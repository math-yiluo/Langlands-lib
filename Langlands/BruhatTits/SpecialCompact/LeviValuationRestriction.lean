import Langlands.BruhatTits.SpecialCompact.LeviRootTransport
import Langlands.Geometry.Building.KPApartment
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeRootStandardCocharacter

/-! # Restricting actual root valuations to a prescribed cocharacter Levi -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.SpecialCompact

variable {F : Type u} [Field F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G M : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffineHom M.X.hom]
    (iM : S.toGrp ⟶ M) (j : M ⟶ G)

/-- Restrict by the original point map on Levi roots, with the normalization
at infinity outside the Levi root support. -/
def leviRestrictedRootFunctionFamily (φ : RootFunctionFamily S G) : RootFunctionFamily S M := by
  classical
  exact ⟨fun a m => if a ∈ relativeRoots iM then φ a (rationalPoints.map j m) else ⊤⟩

omit [IsAffineHom G.X.hom] in
@[simp] theorem leviRestrictedRootFunctionFamily_apply
    (φ : RootFunctionFamily S G) (a : characterLattice S) (ha : a ∈ relativeRoots iM)
    (m : rationalPoints M) :
    leviRestrictedRootFunctionFamily iM j φ a m = φ a (rationalPoints.map j m) := by
  classical
  exact ite_eq_left ha

omit [IsAffineHom G.X.hom] in
@[simp] theorem leviRestrictedRootFunctionFamily_apply_not_mem
    (φ : RootFunctionFamily S G) (a : characterLattice S) (ha : a ∉ relativeRoots iM)
    (m : rationalPoints M) :
    leviRestrictedRootFunctionFamily iM j φ a m = ⊤ := by
  classical
  exact ite_eq_right ha

variable [Smooth G.X.hom] [ConnectedSpace G.X.left] [LocallyOfFiniteType M.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (hcomp : iM ≫ j = i)
    (ζ : cocharacterLattice S)
    (hj : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j)

include hS hcomp hj hjc

/-- Every finite root-filtration level is the literal closed-embedding preimage. -/
theorem leviRestrictedRootFiltration_eq_comap
    (φ : RootFunctionFamily S G) (a : characterLattice S) (ha : a ∈ relativeRoots iM)
    (r : ℝ) :
    rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ) a r =
      rationalPoints.map j ⁻¹' rootFiltration i φ a r := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  have hcomap := leviRootGroupPoints_eq_comap hS i iM j hcomp ζ hj hjc a
    ((hroots ▸ ha).1.1)
  ext m
  simp only [mem_rootFiltration, leviRestrictedRootFunctionFamily_apply iM j φ a ha,
    Set.mem_preimage, ← Subgroup.mem_comap, ← hcomap]

/-- Finite root-filtration levels have exactly the same image under inclusion. -/
theorem image_leviRestrictedRootFiltration
    (φ : RootFunctionFamily S G) (a : characterLattice S) (ha : a ∈ relativeRoots iM)
    (r : ℝ) :
    rationalPoints.map j '' rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ) a r =
      rootFiltration i φ a r := by
  rw [leviRestrictedRootFiltration_eq_comap iM j hS i hcomp ζ hj hjc φ a ha r]
  apply Set.image_preimage_eq_iff.mpr
  intro g hg
  have hmap := map_leviRootGroupPoints hS i iM j hcomp ζ hj hjc a ha
  have hgin : g ∈ (rootGroupPoints iM a).map (rationalPoints.map j) := hmap.symm ▸ hg.1
  obtain ⟨m, hm, rfl⟩ := hgin
  exact ⟨m, rfl⟩

/-- The finite-value images used by V0 are unchanged on corresponding roots. -/
theorem image_leviRestrictedRootFunctionFamily
    (φ : RootFunctionFamily S G) (a : characterLattice S) (ha : a ∈ relativeRoots iM) :
    leviRestrictedRootFunctionFamily iM j φ a '' (rootGroupPoints iM a : Set (rationalPoints M)) =
      φ a '' (rootGroupPoints i a : Set (rationalPoints G)) := by
  have hmap := map_leviRootGroupPoints hS i iM j hcomp ζ hj hjc a ha
  ext v
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨rationalPoints.map j m, hmap ▸ Subgroup.mem_map.mpr ⟨m, hm, rfl⟩,
      (leviRestrictedRootFunctionFamily_apply iM j φ a ha m).symm⟩
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp (hmap.symm ▸ hg)
    exact ⟨m, hm, leviRestrictedRootFunctionFamily_apply iM j φ a ha m⟩

/-- The entire V3 generating union transports through the original inclusion;
zero pairing keeps every occurring combination inside the Levi root system. -/
theorem image_leviRestricted_commutatorGenerators
    (φ : RootFunctionFamily S G) (a b : characterLattice S)
    (ha : a ∈ relativeRoots iM) (hb : b ∈ relativeRoots iM) (r s : ℝ) :
    rationalPoints.map j ''
      (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots iM),
        rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ)
          (p • a + q • b) (p * r + q * s)) =
      ⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots i),
        rootFiltration i φ (p • a + q • b) (p * r + q * s) := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  have haz : latticePairing S a ζ = 0 := (hroots ▸ ha).2
  have hbz : latticePairing S b ζ = 0 := (hroots ▸ hb).2
  have hzero (p q : ℕ) : latticePairing S (p • a + q • b) ζ = 0 := by
    simp only [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply,
      haz, hbz, smul_zero, zero_add]
  ext g
  simp only [Set.mem_image, Set.mem_iUnion]
  constructor
  · rintro ⟨m, ⟨p, q, hp, hq, hc, hm⟩, rfl⟩
    refine ⟨p, q, hp, hq, (hroots ▸ hc).1, ?_⟩
    exact (Set.mem_image_of_mem (rationalPoints.map j) hm :
      rationalPoints.map j m ∈ rationalPoints.map j '' _) |>
      (image_leviRestrictedRootFiltration iM j hS i hcomp ζ hj hjc φ _ hc _ ▸ ·)
  · rintro ⟨p, q, hp, hq, hc, hg⟩
    have hcM : p • a + q • b ∈ relativeRoots iM := hroots.symm ▸ ⟨hc, hzero p q⟩
    have him : g ∈ rationalPoints.map j '' rootFiltration iM
        (leviRestrictedRootFunctionFamily iM j φ) (p • a + q • b) (p * r + q * s) :=
      (image_leviRestrictedRootFiltration iM j hS i hcomp ζ hj hjc φ _ hcM _).symm ▸ hg
    obtain ⟨m, hm, rfl⟩ := him
    exact ⟨m, ⟨p, q, hp, hq, hcM, hm⟩, rfl⟩

section Valuation
variable [Mono i.hom.hom.left] [Mono iM.hom.hom.left]

/-- All axioms V0--V5 restrict to the actual prescribed Levi. -/
theorem leviRestricted_isRootDatumValuation
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    {φ : RootFunctionFamily S G} (hφ : IsRootDatumValuation i φ) :
    IsRootDatumValuation iM (leviRestrictedRootFunctionFamily iM j φ) := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  have hsub : relativeRoots iM ⊆ relativeRoots i := fun a ha => (hroots ▸ ha).1
  have hneg : ∀ a ∈ relativeRoots iM, -a ∈ relativeRoots iM := by
    intro a ha
    have har := HasRelativeRootSystem.neg_mem_relativeRoots i
      (relativeRootSystem F G hG S i hi) hS (hsub ha)
    exact hroots.symm ▸ ⟨har, by
      simpa only [map_neg, LinearMap.neg_apply, neg_eq_zero] using (hroots ▸ ha).2⟩
  have hinj : Function.Injective (rationalPoints.map j) := by
    have : Mono j.hom.hom := hj.1
    intro a b hab
    exact (cancel_mono j.hom.hom).mp hab
  have hmap (a : characterLattice S) (ha : a ∈ relativeRoots iM) (m : rationalPoints M)
      (hm : m ∈ rootGroupPoints iM a) : rationalPoints.map j m ∈ rootGroupPoints i a := by
    rw [← map_leviRootGroupPoints hS i iM j hcomp ζ hj hjc a ha]
    exact Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
  have hlevel (a : characterLattice S) (ha : a ∈ relativeRoots iM) (r : ℝ)
      (m : rationalPoints M) :
      m ∈ rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ) a r ↔
        rationalPoints.map j m ∈ rootFiltration i φ a r := by
    rw [leviRestrictedRootFiltration_eq_comap iM j hS i hcomp ζ hj hjc φ a ha r]
    rfl
  refine
    { eq_top_of_not_mem_roots := fun a ha m =>
        leviRestrictedRootFunctionFamily_apply_not_mem iM j φ a ha m
      eq_top_of_not_mem := ?_
      three_le_encard := ?_
      one_mem := ?_
      mul_mem := ?_
      inv_mem := ?_
      eq_top_iff := ?_
      reflection := ?_
      commutator := ?_
      double := ?_
      opposite := ?_ }
  · intro a ha m hm
    rw [leviRestrictedRootFunctionFamily_apply iM j φ a ha]
    apply hφ.eq_top_of_not_mem a (hsub ha)
    have hc := leviRootGroupPoints_eq_comap hS i iM j hcomp ζ hj hjc a (hsub ha).1
    exact fun hh => hm (hc.symm ▸ hh)
  · intro a ha
    rw [image_leviRestrictedRootFunctionFamily iM j hS i hcomp ζ hj hjc φ a ha]
    exact hφ.three_le_encard a (hsub ha)
  · intro a ha r
    apply (hlevel a ha r 1).mpr
    simpa only [map_one] using hφ.one_mem a (hsub ha) r
  · intro a ha r m n hm hn
    apply (hlevel a ha r (m * n)).mpr
    rw [map_mul]
    exact hφ.mul_mem a (hsub ha) r _ _ ((hlevel a ha r m).mp hm) ((hlevel a ha r n).mp hn)
  · intro a ha r m hm
    apply (hlevel a ha r m⁻¹).mpr
    rw [map_inv]
    exact hφ.inv_mem a (hsub ha) r _ ((hlevel a ha r m).mp hm)
  · intro a ha m hm
    rw [leviRestrictedRootFunctionFamily_apply iM j φ a ha,
      hφ.eq_top_iff a (hsub ha) _ (hmap a ha m hm)]
    exact ⟨fun he => hinj (he.trans (map_one (rationalPoints.map j)).symm),
      fun he => he ▸ map_one (rationalPoints.map j)⟩
  · intro a ha n hn
    let n' := normalizerPointsMap iM j i hcomp n
    obtain ⟨c, hc⟩ := hφ.reflection a (hsub ha) n'
      (realizesReflection_leviMap i iM j hcomp a n hn)
    refine ⟨c, fun m hm hm1 => ?_⟩
    rw [leviRestrictedRootFunctionFamily_apply iM j φ a ha,
      leviRestrictedRootFunctionFamily_apply iM j φ (-a) (hneg a ha)]
    simpa only [n', normalizerPointsMap_val, rationalPoints.map_apply, map_mul, map_inv]
      using hc (rationalPoints.map j m) (hmap a ha m hm)
        (fun h => hm1 (hinj (h.trans (map_one (rationalPoints.map j)).symm)))
  · intro a ha b hb hab r s
    let U := Subgroup.closure (rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ) a r)
    let V := Subgroup.closure (rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ) b s)
    let W := Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
      (_ : p • a + q • b ∈ relativeRoots iM),
      rootFiltration iM (leviRestrictedRootFunctionFamily iM j φ)
        (p • a + q • b) (p * r + q * s))
    have hm : (⁅U, V⁆).map (rationalPoints.map j) ≤ W.map (rationalPoints.map j) := by
      dsimp only [U, V, W]
      rw [Subgroup.map_commutator, MonoidHom.map_closure, MonoidHom.map_closure,
        MonoidHom.map_closure,
        image_leviRestrictedRootFiltration iM j hS i hcomp ζ hj hjc φ a ha r,
        image_leviRestrictedRootFiltration iM j hS i hcomp ζ hj hjc φ b hb s,
        image_leviRestricted_commutatorGenerators iM j hS i hcomp ζ hj hjc φ a b ha hb r s]
      exact hφ.commutator a (hsub ha) b (hsub hb) hab r s
    intro m hm'
    have him := hm (Subgroup.mem_map.mpr ⟨m, hm', rfl⟩)
    obtain ⟨n, hn, hnm⟩ := him
    exact hinj hnm ▸ hn
  · intro a ha h2a m hm
    rw [leviRestrictedRootFunctionFamily_apply iM j φ (2 • a) h2a,
      leviRestrictedRootFunctionFamily_apply iM j φ a ha]
    exact hφ.double a (hsub ha) (hsub h2a) _ (hmap _ h2a m hm)
  · intro a ha m hm hm1 m' hm' m'' hm'' hn
    rw [leviRestrictedRootFunctionFamily_apply iM j φ (-a) (hneg a ha),
      leviRestrictedRootFunctionFamily_apply iM j φ a ha]
    apply hφ.opposite a (hsub ha) _ (hmap a ha m hm)
      (fun h => hm1 (hinj (h.trans (map_one (rationalPoints.map j)).symm)))
      _ (hmap (-a) (hneg a ha) m' hm') _ (hmap (-a) (hneg a ha) m'' hm'')
    exact (normalizerPointsMap iM j i hcomp ⟨m' * m * m'', hn⟩).property
      |> (by simpa only [normalizerPointsMap_val, MonObj.mul_comp, rationalPoints.map_apply] using ·)


/-- The intrinsic restriction as a map of actual valuation subtypes. -/
def leviValuationRestriction
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (φ : {φ : RootFunctionFamily S G // IsRootDatumValuation i φ}) :
    {ψ : RootFunctionFamily S M // IsRootDatumValuation iM ψ} :=
  ⟨leviRestrictedRootFunctionFamily iM j φ.val,
    leviRestricted_isRootDatumValuation iM j hS i hcomp ζ hj hjc hG hi φ.property⟩

/-- Compatibility with the same field valuation and same split torus is retained. -/
theorem leviRestricted_isSplitTorusCompatible
    {φ : RootFunctionFamily S G} {ω : Fˣ → ℝ}
    (hφ : IsSplitTorusCompatible i ω φ) :
    IsSplitTorusCompatible iM ω (leviRestrictedRootFunctionFamily iM j φ) := by
  have hroots := relativeRoots_centralizer_factor dynamicLie i iM j hcomp ζ hj
  intro a ha s m hm
  rw [leviRestrictedRootFunctionFamily_apply iM j φ a ha,
    leviRestrictedRootFunctionFamily_apply iM j φ a ha]
  have hms : rationalPoints.map j (rationalPoints.map iM s) = rationalPoints.map i s := by
    change (s ≫ iM.hom.hom) ≫ j.hom.hom = s ≫ i.hom.hom
    rw [Category.assoc]
    exact congrArg (fun f : S.toGrp ⟶ G => s ≫ f.hom.hom) hcomp
  have hmap : rationalPoints.map j m ∈ rootGroupPoints i a := by
    rw [← map_leviRootGroupPoints hS i iM j hcomp ζ hj hjc a ha]
    exact Subgroup.mem_map.mpr ⟨m, hm, rfl⟩
  simpa only [map_mul, map_inv, hms] using hφ a (hroots ▸ ha).1 s _ hmap

/-- Restriction intertwines translation by the full real cocharacter space. -/
theorem leviRestrictedRootFunctionFamily_vadd
    (φ : RootFunctionFamily S G) (v : V S) :
    leviRestrictedRootFunctionFamily iM j (v +ᵥ φ) =
      v +ᵥ leviRestrictedRootFunctionFamily iM j φ := by
  ext a m
  by_cases ha : a ∈ relativeRoots iM
  · simp only [RootFunctionFamily.vadd_apply,
      leviRestrictedRootFunctionFamily_apply iM j _ a ha]
  · simp only [RootFunctionFamily.vadd_apply,
      leviRestrictedRootFunctionFamily_apply_not_mem iM j _ a ha, WithTop.top_add]

/-- Restriction intertwines the actual normalizer action at the same torus. -/
theorem leviRestrictedRootFunctionFamily_smul
    (φ : RootFunctionFamily S G) (n : normalizerPoints iM) :
    leviRestrictedRootFunctionFamily iM j
        (normalizerPointsMap iM j i hcomp n • φ) =
      n • leviRestrictedRootFunctionFamily iM j φ := by
  ext a m
  by_cases ha : a ∈ relativeRoots iM
  · have hb : weylAction iM n⁻¹ a ∈ relativeRoots iM :=
      weylAction_mapsTo_relativeRoots iM n⁻¹ ha
    rw [leviRestrictedRootFunctionFamily_apply iM j _ a ha,
      RootFunctionFamily.smul_apply, RootFunctionFamily.smul_apply,
      leviRestrictedRootFunctionFamily_apply iM j _ _ hb]
    have hinv : (normalizerPointsMap iM j i hcomp n)⁻¹ =
        normalizerPointsMap iM j i hcomp n⁻¹ := (map_inv _ _).symm
    rw [hinv, weylAction_normalizerPointsMap]
    simp only [normalizerPointsMap_val, rationalPoints.map_apply, MonObj.mul_comp,
      GrpObj.inv_comp]
  · have hb : weylAction iM n⁻¹ a ∉ relativeRoots iM := by
      intro hb
      have h := weylAction_mapsTo_relativeRoots iM n hb
      simp only [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        LinearEquiv.coe_one, id_eq] at h
      exact ha h
    rw [leviRestrictedRootFunctionFamily_apply_not_mem iM j _ a ha,
      RootFunctionFamily.smul_apply,
      leviRestrictedRootFunctionFamily_apply_not_mem iM j _ _ hb]

end Valuation

end Langlands.BruhatTits.SpecialCompact
