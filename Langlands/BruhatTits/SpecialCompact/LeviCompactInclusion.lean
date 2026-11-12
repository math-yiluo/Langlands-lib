import Langlands.BruhatTits.SpecialCompact.LeviProjectionFromPair
import Langlands.Geometry.Building.SpecialPointFixedLocus
import Langlands.Geometry.Building.NormalizerNormOneFixerBoundedness
import Langlands.GroupScheme.Rational.RelativeSplitCentralDirectionsProof

/-! # The prescribed Levi compact stabilizer maps into the ambient stabilizer -/

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Geometry.Building Langlands.Plancherel
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.SpecialCompact

/-- A real affine map whose displacement is fixed by its linear part cannot
move a point if some positive power fixes it. -/
theorem affineEquiv_apply_eq_of_linear_fixed_of_pow_fixed
    {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    (f : A ≃ᵃ[ℝ] A) (x : A) (hlin : f.linear (f x -ᵥ x) = f x -ᵥ x)
    (k : ℕ) (hk : 0 < k) (hpow : (f ^ k) x = x) : f x = x := by
  let v := f x -ᵥ x
  have hstep : f x = v +ᵥ x := (vsub_vadd _ _).symm
  have hpows : ∀ m : ℕ, (f ^ m) x = (m : ℝ) • v +ᵥ x := by
    intro m
    induction m with
    | zero => simp
    | succ m hm =>
      rw [pow_succ', AffineEquiv.coe_mul, Function.comp_apply, hm, AffineEquiv.map_vadd,
        map_smul, hlin, hstep, vadd_vadd]
      simp only [Nat.cast_succ, add_smul, one_smul, vadd_vsub]
  have hvzero : (k : ℝ) • v = 0 := by
    rw [← vadd_right_cancel_iff x, zero_vadd, ← hpows, hpow]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  exact vsub_eq_zero_iff_eq.mp ((smul_eq_zero.mp hvzero).resolve_left hk0)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (iM : S.toGrp ⟶ M)
    [Mono i.hom.hom.left] [Mono iM.hom.hom.left]
    (j : M ⟶ G) (hcomp : iM ≫ j = i) (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j)
    (D : KPApartmentData i (localFieldOrder F))

local notation "Nmap" => normalizerPointsMap iM j i hcomp

include hcomp in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The same full real cocharacter action is used by a Levi normalizer point. -/
theorem normalizerAction_leviMap (n : normalizerPoints iM) :
    normalizerAction i (Nmap n) = normalizerAction iM n := by
  change cocharacterRealAut _ = cocharacterRealAut _
  rw [normalizingAut_leviMap i iM j hcomp]

include hcomp hj in
/-- A Levi Weyl element fixes every additional central direction of the
ambient apartment quotient, using the published full-lattice fixedness theorem. -/
theorem translationAction_fixes_leviProjectionKernel
    (hM : IsConnectedReductive M) (hiM : IsMaximalSplitTorus iM)
    (n : normalizerPoints iM) (v : TranslationSpace i)
    (hv : leviTranslationProjection i iM j hcomp ζ hj v = 0) :
    translationAction i (Nmap n) v = v := by
  have hfixed := (relativeSplitCentralDirections F M hM S iM hiM).2.2.2.2.2.1
  induction v using Submodule.Quotient.induction_on with
  | _ w =>
    change (Submodule.Quotient.mk w : TranslationSpace iM) = 0 at hv
    have hw := (Submodule.Quotient.mk_eq_zero (rootAnnihilator iM)).mp hv
    rw [translationAction_mk]
    change (Submodule.Quotient.mk (normalizerAction i (Nmap n) w) : TranslationSpace i) =
      Submodule.Quotient.mk w
    rw [normalizerAction_leviMap i iM j hcomp]
    exact congrArg (fun z : V S => (Submodule.Quotient.mk z : TranslationSpace i))
      (hfixed (QuotientGroup.mk n) w hw)

/-- Apartment-level form of the published centralizer fixed-point norm-kernel
criterion, with all carriers explicit rather than bundled valuation data. -/
theorem centralizer_normOne_of_apartment_fixed
    (hM : IsConnectedReductive M) (hiM : IsMaximalSplitTorus iM)
    (CM : CentralizerDatum iM) (P : KPApartmentData iM (localFieldOrder F))
    (hOM : P.IsOmegaCompatible CM) (z : rationalPoints CM.Z)
    (hz : rationalPoints.map CM.j z ∈ rationalCommonNormKernel M)
    (y : P.Apartment) (hy : CM.toNormalizer z • y = y) :
    z ∈ rationalCommonNormKernel CM.Z := by
  rw [← centralizerTranslation_ker CM.s CM.bijective, MonoidHom.mem_ker]
  let v : V S := (CM.translation z).toAdd
  rw [hOM.smul_eq_vadd z y] at hy
  have hmk : (Submodule.Quotient.mk v : TranslationSpace iM) = 0 := by
    rw [← vadd_right_cancel_iff y, zero_vadd]
    exact hy
  rw [Submodule.Quotient.mk_eq_zero, Langlands.Geometry.Building.mem_rootAnnihilator] at hmk
  have hspan := relativeRootsRestrictedCharactersSpan F M hM S iM hiM
  have hv0 : v = 0 := by
    refine eq_zero_of_eval_eq_zero_of_span hiM.isSplitSubtorus.1 hspan ?_
    rintro χ (hχ | ⟨χM, rfl⟩)
    · exact hmk χ hχ
    · have hres : torusCharacterRestrict iM χM =
          Cartan.characterRestriction CM.s (characterRestrict CM.j χM) := by
        have heq : characterRestrict iM χM =
            characterRestrict CM.s (characterRestrict CM.j χM) := by
          rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, CM.comp_eq]
        simp only [torusCharacterRestrict, Cartan.characterRestriction,
          AddMonoidHom.comp_apply, heq]
      have heval : eval S (torusCharacterRestrict iM χM) v =
          -((rationalCharacterValuation M (rationalPoints.map CM.j z)).toAdd χM : ℝ) := by
        rw [hres, eval_centralizerTranslation, rationalCharacterValuation_apply,
          rationalCharacterValuation_apply, rationalCharacterEval_characterRestrict]
      rw [heval, (mem_rationalCommonNormKernel_iff_valuation M _).mp hz χM,
        Int.cast_zero, neg_zero]
  change CM.translation z = 1
  rw [← toAdd_eq_zero]
  exact hv0

variable (hM : IsConnectedReductive M) (hiM : IsMaximalSplitTorus iM)
    (CM : CentralizerDatum iM)
    (C : CentralizerDatum i) (hO : D.IsOmegaCompatible C)
    (c : CM.Z ⟶ C.Z) (hc : CM.j ≫ j = c ≫ C.j)

include hM hiM CM C hO c hc in
/-- A norm-one normalizer point fixing an equivariant affine projection fixes
its source point when the linear kernel is fixed pointwise. -/
theorem normalizer_smul_eq_of_projected_fixed
    (PM : KPApartmentData iM (localFieldOrder F))
    (f : D.Apartment →ᵃ[ℝ] PM.Apartment)
    (hequiv : ∀ (n : normalizerPoints iM) (x : D.Apartment), f (Nmap n • x) = n • f x)
    (hfixed : ∀ (n : normalizerPoints iM) (v : TranslationSpace i),
      f.linear v = 0 → translationAction i (Nmap n) v = v)
    (hOP : PM.IsOmegaCompatible CM)
    (n : normalizerPoints iM) (hn : (n : rationalPoints M) ∈ rationalCommonNormKernel M)
    (x : D.Apartment) (hnx : n • f x = f x) : Nmap n • x = x := by
  let nG := Nmap n
  have : Finite (relativeWeylGroup iM) := hiM.isSplitSubtorus.1.finite_relativeWeylGroup_of_span iM
    (relativeRootsRestrictedCharactersSpan F M hM S iM hiM)
  obtain ⟨k, hk, hnk⟩ :=
    (isOfFinOrder_of_finite (QuotientGroup.mk n : relativeWeylGroup iM)).exists_pow_eq_one
  have hcentral : ((n ^ k : normalizerPoints iM) : rationalPoints M) ∈ centralizerPoints iM := by
    change n ^ k ∈ (centralizerPoints iM).subgroupOf (normalizerPoints iM)
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' ((centralizerPoints iM).subgroupOf (normalizerPoints iM))) (n ^ k) = 1
    rw [map_pow]
    exact hnk
  rw [← torusCentralizer_carrier_base, ← CM.isRepresentedBy.2] at hcentral
  obtain ⟨z, hz⟩ : ∃ z : rationalPoints CM.Z,
      rationalPoints.map CM.j z = ((n ^ k : normalizerPoints iM) : rationalPoints M) := hcentral
  have hzn : CM.toNormalizer z = n ^ k := Subtype.ext hz
  have hfixpow : ∀ k : ℕ, n ^ k • f x = f x := by
    intro k
    induction k with
    | zero => simp
    | succ k hk => rw [pow_succ', mul_smul, hk, hnx]
  have hzNorm : rationalPoints.map CM.j z ∈ rationalCommonNormKernel M := by
    rw [hz]
    exact (rationalCommonNormKernel M).pow_mem hn k
  have hzFix : CM.toNormalizer z • f x = f x := by
    rw [hzn]
    exact hfixpow k
  have hz1 : z ∈ rationalCommonNormKernel CM.Z :=
    centralizer_normOne_of_apartment_fixed (iM := iM) (hM := hM) (hiM := hiM)
      (CM := CM) (P := PM) (hOM := hOP) (z := z) hzNorm (f x) hzFix
  have hnGk : nG ^ k = C.toNormalizer (rationalPoints.map c z) := by
    change (Nmap n) ^ k = _
    rw [← map_pow]
    apply Subtype.ext
    change rationalPoints.map j ((n ^ k : normalizerPoints iM) : rationalPoints M) =
      rationalPoints.map C.j (rationalPoints.map c z)
    rw [← hz]
    exact congrArg (fun f : CM.Z ⟶ G => rationalPoints.map f z) hc
  have hkfix : nG ^ k • x = x := by
    rw [hnGk]
    exact hO.smul_eq_self (map_mem_rationalCommonNormKernel c hz1) x
  refine affineEquiv_apply_eq_of_linear_fixed_of_pow_fixed (D.normalizerAffineEquiv nG) x ?_ k hk ?_
  · apply hfixed n
    change f.linear (Nmap n • x -ᵥ x) = 0
    rw [f.linearMap_vsub, hequiv n x, hnx, vsub_self]
  · rw [← map_pow]
    exact hkfix


include hS hcomp hj hjc hM hiM CM C hO c hc in
/-- A norm-one Levi normalizer fixing the target of any literal restriction
pair fixes its original ambient point. -/
theorem normalizer_smul_eq_of_isLeviRestriction
    (PM : KPApartmentData iM (localFieldOrder F)) (hOM : PM.IsOmegaCompatible CM)
    (x : D.Apartment) (xM : PM.Apartment) (hres : IsLeviRestriction j x xM)
    (n : normalizerPoints iM) (hn : (n : rationalPoints M) ∈ rationalCommonNormKernel M)
    (hnx : n • xM = xM) : Nmap n • x = x := by
  let f := leviProjectionFromPair i iM j hcomp ζ hj D PM x xM
  have hequiv : ∀ (n : normalizerPoints iM) (y : D.Apartment),
      f (Nmap n • y) = n • f y :=
    leviProjectionFromPair_normalizer hS i iM j hcomp ζ hj hjc D PM x xM hres
  have hfixed : ∀ (n : normalizerPoints iM) (v : TranslationSpace i),
      f.linear v = 0 → translationAction i (Nmap n) v = v := by
    intro n v hv
    change leviTranslationProjection i iM j hcomp ζ hj v = 0 at hv
    exact translationAction_fixes_leviProjectionKernel i iM j hcomp ζ hj hM hiM n v hv
  have hnx' : n • f x = f x := by
    simpa only [f, leviProjectionFromPair_apply_self] using hnx
  exact normalizer_smul_eq_of_projected_fixed (i := i) (iM := iM) (j := j) (hcomp := hcomp)
    (D := D) (hM := hM) (hiM := hiM) (CM := CM) (C := C) (hO := hO) (c := c) (hc := hc)
    (PM := PM) (f := f) hequiv hfixed hOM n hn x hnx'

include hM in
/-- V7 puts every singleton sharp fixer in the norm kernel of the actual group. -/
theorem sharpFixer_le_normKernel_of_topologyCompatible
    (PM : KPApartmentData iM (localFieldOrder F))
    (hTopo : PM.IsTopologyCompatible) (xM : PM.Apartment) :
    PM.sharpFixer {xM} ≤ rationalCommonNormKernel M := by
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  let : TopologicalSpace (rationalPoints M) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPointTopology F M.X
  let : Smooth M.X.hom := hM.smooth
  let : IsTopologicalGroup (rationalPoints M) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_isTopologicalGroup F M
  change (⨆ a : relativeRoots iM, PM.rootFixer a {xM}) ≤ _
  refine iSup_le fun (a : relativeRoots iM) => ?_
  rw [PM.rootFixer_singleton]
  have hbound := ((hTopo xM.val xM.mem a a.property).2 (0 : ℝ)).2
  have hcompact : IsCompact ((PM.filtration xM a 0).topologicalClosure : Set (rationalPoints M)) :=
    hbound.isCompact_closure M.X
  exact (Subgroup.le_topologicalClosure _).trans
    (compactSubgroup_le_rationalCommonNormKernel M _ hcompact)

include hS hcomp hj hjc hM hiM CM C hO c hc in
/-- The norm-one stabilizer of any supplied Levi restriction point maps into
the ambient norm-one stabilizer, under actual V6 on both sides and Levi V7. -/
theorem leviSpecialCompactSubgroup_le_comap
    (PM : KPApartmentData iM (localFieldOrder F)) (hOM : PM.IsOmegaCompatible CM)
    (hTopo : PM.IsTopologyCompatible)
    (x : D.Apartment) (xM : PM.Apartment) (hres : IsLeviRestriction j x xM) :
    PM.specialCompactSubgroup xM ≤
      (D.specialCompactSubgroup x).comap (rationalPoints.map j) := by
  intro m hm
  obtain ⟨hmnorm, hmfix⟩ := (KPApartmentData.mem_specialCompactSubgroup PM).mp hm
  obtain ⟨n, hnfix, p, hp, hmp⟩ :=
    (ApartmentQuotient.mem_stabilizer_apartment_iff PM.sharpFixerFamily xM m).mp hmfix
  have hpNorm := sharpFixer_le_normKernel_of_topologyCompatible (iM := iM)
    (hM := hM) PM hTopo xM hp
  have hnNorm : (n : rationalPoints M) ∈ rationalCommonNormKernel M := by
    have h := (rationalCommonNormKernel M).mul_mem
      ((rationalCommonNormKernel M).inv_mem hpNorm) hmnorm
    rwa [hmp, inv_mul_cancel_left] at h
  have hpn := sharpFixer_le_of_isLeviRestriction hS i iM j hcomp ζ hj hjc D PM x xM hres hp
  have hnGfix := normalizer_smul_eq_of_isLeviRestriction (i := i) (iM := iM)
    (hS := hS) (j := j) (hcomp := hcomp) (ζ := ζ) (hj := hj) (hjc := hjc)
    (D := D) (hM := hM) (hiM := hiM) (CM := CM) (C := C) (hO := hO) (c := c) (hc := hc)
    PM hOM x xM hres n hnNorm hnfix
  apply (KPApartmentData.mem_specialCompactSubgroup D).mpr
  refine ⟨map_mem_rationalCommonNormKernel j hmnorm, ?_⟩
  rw [hmp, map_mul, mul_smul]
  change rationalPoints.map j p • (Nmap n : rationalPoints G) • D.apartmentMap x = D.apartmentMap x
  rw [← D.apartmentMap_smul, hnGfix]
  exact D.sharpFixer_le_reducedFixer x hpn

/-- The actual homomorphism from the Levi compact stabilizer to the
ambient compact stabilizer, induced by the fixed group inclusion `j`. -/
def leviSpecialCompactInclusion
    (PM : KPApartmentData iM (localFieldOrder F)) (hOM : PM.IsOmegaCompatible CM)
    (hTopo : PM.IsTopologyCompatible)
    (x : D.Apartment) (xM : PM.Apartment) (hres : IsLeviRestriction j x xM) :
    PM.specialCompactSubgroup xM →* D.specialCompactSubgroup x where
  toFun m := ⟨rationalPoints.map j m,
    leviSpecialCompactSubgroup_le_comap (hS := hS) (i := i) (iM := iM)
      (j := j) (hcomp := hcomp) (ζ := ζ) (hj := hj) (hjc := hjc)
      (D := D) (hM := hM) (hiM := hiM) (CM := CM) (C := C) (hO := hO)
      (c := c) (hc := hc) PM hOM hTopo x xM hres m.property⟩
  map_one' := by
    apply Subtype.ext
    exact (rationalPoints.map j).map_one
  map_mul' m n := by
    apply Subtype.ext
    exact (rationalPoints.map j).map_mul (m : rationalPoints M) (n : rationalPoints M)

end Langlands.BruhatTits.SpecialCompact
