import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitConstantTermExistenceProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalComponentValuation
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ParabolicLimitOfAnnihilators
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitJacquetContraction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundReduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalInducedJacquetProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviOriginalOrbitXiBound
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakPartProjection
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakConstantTermExistence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalSquareIntegrableDecayProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalModulusFactorization
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFaceLattice
import Langlands.Representation.Aubert.General.RationalCartanCentralSupport
import Langlands.BruhatTits.SpecialCompact.StandardLeviWeakChamberTransport
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.Geometry.Building.CocharacterUniformizerProof
import Langlands.Representation.Plancherel.SplitTorusCompactKernel
import Langlands.Representation.Jacquet.StandardCasselmanUniformAsymptotics

/-! # The weak constant term as a limit (Waldspurger, Lemma III.5.1)

Proof of `RationalOrbitWeakConstantTermLimitStatement`: coordinates of `H_0` on `A(F)`,
generators of the coordinate directions in `C_A`, bounds of `δ^{-1/2} Ξ` on deep shells, and the
main theorem `rationalOrbitWeakConstantTermLimit`, which applies the abstract criterion
`tendstoZeroAlongParabolic_of_strictAnnihilators` to `a ↦ (f_ω)^+_{P'}(m' a)`.
-/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

section Coordinates

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {q : A.toGrp ⟶ S.toGrp}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem one_lt_residueCardinality_real [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : (1 : ℝ) < (LocalField.residueCardinality F : ℝ) := by
  exact_mod_cast LocalField.residueCardinality_gt_one F

/-- `H_0` on `A(F)` is additive. -/
theorem rationalComponentH0_mul (x y : rationalPoints A.toGrp) :
    rationalComponentH0 hG hi hν (qA := q) (x * y) =
      rationalComponentH0 hG hi hν (qA := q) x + rationalComponentH0 hG hi hν (qA := q) y := by
  rw [← rationalComponentValuation_toAdd, ← rationalComponentValuation_toAdd,
    ← rationalComponentValuation_toAdd, map_mul, toAdd_mul]

/-- `H_0` on `A(F)` turns powers into multiples. -/
theorem rationalComponentH0_pow (x : rationalPoints A.toGrp) (n : ℕ) :
    rationalComponentH0 hG hi hν (qA := q) (x ^ n) =
      n • rationalComponentH0 hG hi hν (qA := q) x := by
  rw [← rationalComponentValuation_toAdd, ← rationalComponentValuation_toAdd, map_pow, toAdd_pow]

/-- **Character norms in `H_0`-coordinates**: `|α|_A(x)| = q^{-⟨α, H_0(x)⟩}` for the restriction to
`A` of a character `α` of `S`. -/
theorem characterNorm_componentCharacterRestriction_eq_rpow (α : characterLattice S)
    (x : rationalPoints A.toGrp) :
    CocharacterUniformizer.characterNorm F A (componentCharacterRestriction q α) x =
      (LocalField.residueCardinality F : ℝ) ^
        (-RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q) x)) := by
  have heq : CocharacterUniformizer.characterNorm F A (componentCharacterRestriction q α) x =
      CocharacterUniformizer.characterNorm F S α (rationalPoints.map q x) := by
    simp [CocharacterUniformizer.characterNorm, componentCharacterRestriction,
      Plancherel.rationalNormCharacters_apply, rationalCharacterEval_characterRestrict]
  rw [heq, BruhatTits.Cartan.RenardLeviCones.characterNorm_eq_rpow, eval_rationalComponentH0]

/-- On the common norm kernel of `A(F)`, every coordinate of `H_0` vanishes. -/
theorem eval_rationalComponentH0_eq_zero_of_mem_kernel (α : characterLattice S)
    {n : rationalPoints A.toGrp} (hn : n ∈ Plancherel.rationalCommonNormKernel A.toGrp) :
    RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q) n) = 0 := by
  have h1 : CocharacterUniformizer.characterNorm F A (componentCharacterRestriction q α) n = 1 := by
    have h := (Plancherel.mem_rationalCommonNormKernel (G := A.toGrp) n).mp hn
      ((rationalCharacters.equivCharacterLattice A).symm (componentCharacterRestriction q α))
    simp only [CocharacterUniformizer.characterNorm, Plancherel.rationalNormCharacters_apply, h,
      Units.val_one, NNReal.coe_one]
  rw [characterNorm_componentCharacterRestriction_eq_rpow hG hi hν] at h1
  have hq := one_lt_residueCardinality_real (F := F)
  have h2 := Real.logb_rpow (b := (LocalField.residueCardinality F : ℝ))
    (x := -RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q) n))
    (by linarith) hq.ne'
  rw [h1, Real.logb_one] at h2
  linarith

/-- **Coordinates through the lattice section**: if `x · (ϖ^c)⁻¹` lies in the common norm
kernel, `⟨α, H_0(x)⟩ = ⟨α, q_* c⟩`. -/
theorem eval_rationalComponentH0_of_mem_kernel (α : characterLattice S)
    {x : rationalPoints A.toGrp} {c : cocharacterLattice A}
    (h : x * (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c))⁻¹ ∈
      Plancherel.rationalCommonNormKernel A.toGrp) :
    RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q) x) =
      (latticePairing S α (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c) : ℝ) := by
  have hx : x = x * (CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c))⁻¹ *
      CocharacterUniformizer.latticeSection F A (Multiplicative.ofAdd c) := by group
  rw [hx, rationalComponentH0_mul, map_add, eval_rationalComponentH0_eq_zero_of_mem_kernel hG hi hν
    α h, zero_add, eval_rationalComponentH0_latticeSection]

/-- Large coordinates put a point in the source's cone: if `⟨α, H_0(x)⟩ > -log_q ε` for every
simple root `α ∉ J`, then `x ∈ standardCone ε`. -/
theorem mem_standardCone_of_eval_gt [LocallyOfFiniteType G.X.hom] {J : Set (characterLattice S)}
    {ε : ℝ} (hε : 0 < ε) {x : rationalPoints A.toGrp}
    (hx : ∀ α ∈ simpleRelativeRoots i ν \ J,
      -Real.logb (LocalField.residueCardinality F) ε <
        RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q) x)) :
    x ∈ standardCone i ν J q ε := by
  rintro _ ⟨α, hα, rfl⟩
  rw [characterNorm_componentCharacterRestriction_eq_rpow hG hi hν,
    ← Real.lt_logb_iff_rpow_lt one_lt_residueCardinality_real hε]
  linarith [hx α hα]

/-- Positive coordinates outside `J` make a point of `C_A` strict. -/
theorem mem_CAstrict_of_eval_pos {J : Set (characterLattice S)} {x : rationalPoints A.toGrp}
    (hxC : x ∈ CocharacterUniformizer.CA F A)
    (hx : ∀ α ∈ simpleRelativeRoots i ν \ J,
      0 < RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q) x)) :
    x ∈ CocharacterUniformizer.CAstrict F A (standardParabolicComponentCharacters i ν J q) := by
  refine ⟨hxC, ?_⟩
  rintro _ ⟨α, hα, rfl⟩
  rw [characterNorm_componentCharacterRestriction_eq_rpow hG hi hν]
  exact Real.rpow_lt_one_of_one_lt_of_neg one_lt_residueCardinality_real (by linarith [hx α hα])

end Coordinates

section Generators

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {q : A.toGrp ⟶ S.toGrp} {J : Set (characterLattice S)}
  [LocallyOfFiniteType G.X.hom]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The forms `Δ_0 − Δ_0^{M'}` are the evaluations of the simple roots outside `J`. -/
theorem mem_rationalOutsideSimpleForms {β : Module.Dual ℝ (RealTorusSpace.V S)} :
    β ∈ rationalOutsideSimpleForms hi (ν := ν) J ↔
      ∃ r ∈ simpleRelativeRoots i ν \ J, RealTorusSpace.eval S r = β := by
  classical
  unfold rationalOutsideSimpleForms
  rw [Finset.mem_image]
  simp only [Set.Finite.mem_toFinset]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem eval_mem_rationalOutsideSimpleForms {r : characterLattice S}
    (hr : r ∈ simpleRelativeRoots i ν \ J) :
    RealTorusSpace.eval S r ∈ rationalOutsideSimpleForms hi (ν := ν) J :=
  (mem_rationalOutsideSimpleForms hi).2 ⟨r, hr, rfl⟩

/-- **Generators of the coordinate directions.** For every form `β ∈ Δ_0 − Δ_0^{M'}` there is a
lattice point `h β ∈ C_A` with `β(H_0(h β)) = d` and `α(H_0(h β)) = 0` for the other forms `α`,
for one common `d > 0`: lift a standard cocharacter of `Δ_0 − {r}` to `A` and rescale by the
product of the other positive pairings. -/
theorem exists_rationalComponentH0_generators (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hJ : J ⊆ simpleRelativeRoots i ν) (hex : ∃ ζ, IsStandardCocharacter i ν J ζ) :
    ∃ d : ℝ, 0 < d ∧ ∃ h : Module.Dual ℝ (RealTorusSpace.V S) → rationalPoints A.toGrp,
      (∀ β ∈ rationalOutsideSimpleForms hi (ν := ν) J, h β ∈ CocharacterUniformizer.CA F A) ∧
      (∀ β ∈ rationalOutsideSimpleForms hi (ν := ν) J,
        β (rationalComponentH0 hG hi hν (qA := q) (h β)) = d) ∧
      ∀ β ∈ rationalOutsideSimpleForms hi (ν := ν) J,
        ∀ α ∈ rationalOutsideSimpleForms hi (ν := ν) J, α ≠ β →
          α (rationalComponentH0 hG hi hν (qA := q) (h β)) = 0 := by
  classical
  have hstep : ∀ r ∈ simpleRelativeRoots i ν \ J, ∃ e : cocharacterLattice A,
      0 < latticePairing S r (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) e) ∧
      ∀ α ∈ simpleRelativeRoots i ν, α ≠ r →
        latticePairing S α (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) e) = 0 := by
    rintro r ⟨hr, hrJ⟩
    obtain ⟨ζr, hζr⟩ := (standardCocharacter F G hG S i hi ν hν (simpleRelativeRoots i ν \ {r})
      Set.sdiff_subset).1
    obtain ⟨e, he⟩ := hA.exists_cocharacter_lift_of_annihilates i ν hi hex ζr
      (fun α hα => hζr.2.1 α ⟨hJ hα, fun hαr => hrJ (by
        rw [Set.mem_singleton_iff.mp hαr] at hα
        exact hα)⟩)
    refine ⟨e, ?_, fun α hα hαr => ?_⟩
    · rw [he]
      exact hζr.2.2 r hr fun h => h.2 rfl
    · rw [he]
      exact hζr.2.1 α ⟨hα, hαr⟩
  choose! e hepos hezero using hstep
  have hroots : ∀ β ∈ rationalOutsideSimpleForms hi (ν := ν) J,
      ∃ r ∈ simpleRelativeRoots i ν \ J, RealTorusSpace.eval S r = β :=
    fun β hβ => (mem_rationalOutsideSimpleForms hi).1 hβ
  choose! root hroot hrootβ using hroots
  set Sf : Finset (characterLattice S) := ((hi.1.1.finite_simpleRelativeRoots i ν).subset
    (Set.sdiff_subset : simpleRelativeRoots i ν \ J ⊆ simpleRelativeRoots i ν)).toFinset with hSf
  have hmemSf : ∀ r, r ∈ Sf ↔ r ∈ simpleRelativeRoots i ν \ J :=
    fun r => Set.Finite.mem_toFinset _
  obtain ⟨n, hn⟩ : ∃ n : characterLattice S → ℤ, ∀ r, n r =
      latticePairing S r (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) (e r)) :=
    ⟨_, fun _ => rfl⟩
  have hDpos : (0 : ℤ) < ∏ r ∈ Sf, n r :=
    Finset.prod_pos fun r hr => (hn r).symm ▸ hepos r ((hmemSf r).1 hr)
  have heval : ∀ (r α : characterLattice S) (k : ℤ),
      RealTorusSpace.eval S α (rationalComponentH0 hG hi hν (qA := q)
        (CocharacterUniformizer.latticeSection F A (.ofAdd (k • e r)))) =
        ((k * latticePairing S α
          (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) (e r)) : ℤ) : ℝ) := by
    intro r α k
    rw [eval_rationalComponentH0_latticeSection, map_zsmul, map_zsmul, smul_eq_mul]
  refine ⟨((∏ r ∈ Sf, n r : ℤ) : ℝ), by exact_mod_cast hDpos,
    fun β => CocharacterUniformizer.latticeSection F A
      (.ofAdd ((∏ t ∈ Sf.erase (root β), n t) • e (root β))), fun β _ => ⟨_, rfl⟩, ?_, ?_⟩
  · intro β hβ
    have hr := hroot β hβ
    have h1 := heval (root β) (root β) (∏ t ∈ Sf.erase (root β), n t)
    rw [hrootβ β hβ] at h1
    rw [h1, ← hn, Finset.prod_erase_mul _ _ ((hmemSf _).2 hr)]
  · intro β hβ α hα hαβ
    have hr := hroot β hβ
    obtain ⟨r', hr', rfl⟩ := (mem_rationalOutsideSimpleForms hi).1 hα
    rw [heval, hezero (root β) hr r' hr'.1 (fun h => hαβ (by rw [h, hrootβ β hβ])), mul_zero,
      Int.cast_zero]

end Generators

section ShellBound

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) {q : A.toGrp ⟶ S.toGrp} {J : Set (characterLattice S)}
  (hJ : J ⊆ simpleRelativeRoots i ν) (hA : IsCompatibleStandardSplitComponent i ν J A q)

include hG hi hν hJ hA in
/-- A lattice point of `A(F)` whose pairings with the simple roots outside `J` vanish maps to a
central element of `G(F)` lying in `P_0(F)` (its pairings with `J` vanish automatically). -/
theorem map_latticeSection_mem_center (c : cocharacterLattice A)
    (hc : ∀ r ∈ simpleRelativeRoots i ν \ J,
      latticePairing S r (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c) = 0) :
    rationalPoints.map (q ≫ i) (CocharacterUniformizer.latticeSection F A (.ofAdd c)) ∈
        Subgroup.center (rationalPoints G) ∧
      rationalPoints.map (q ≫ i) (CocharacterUniformizer.latticeSection F A (.ofAdd c)) ∈
        standardParabolicPoints i ν ∅ := by
  have heq : rationalPoints.map (q ≫ i) (CocharacterUniformizer.latticeSection F A (.ofAdd c)) =
      Aubert.General.uniformizerPowers i
        (.ofAdd (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S) c)) := by
    change rationalPoints.map i (rationalPoints.map
      (CommGroupScheme.groupHom (Additive.ofMul q : A ⟶ S))
        (Plancherel.RenardCartan.uniformizerSection A (.ofAdd c))) = _
    rw [Plancherel.RenardCartan.uniformizerSection_naturality]
    rfl
  rw [heq]
  let := hG.smooth
  let := hG.connectedSpace
  refine ⟨Aubert.General.uniformizerPowers_mem_center_of_simpleRootPairing_eq_zero i ν hi.1.1 hν
    (relativeRootNegation F G hG S i hi) _ fun β => ?_, ?_⟩
  · rw [Aubert.General.simpleRootPairing_apply]
    by_cases hβJ : β.1 ∈ J
    · exact hA.latticePairing_eq_zero hJ c hβJ
    · exact hc β.1 ⟨β.2, hβJ⟩
  · exact standardLevi_le_standardParabolic i ν ∅ _ (uniformizerPowers_mem_standardLevi i ν ∅ _)

/-- `δ_{U_J}` is trivial on elements central in `G(F)`. -/
theorem standardRadicalModulus_eq_one_of_mem_center (z : standardLeviPoints i ν J)
    (hz : (z : rationalPoints G) ∈ Subgroup.center (rationalPoints G)) :
    standardRadicalModulus i ν J z = 1 := by
  rw [standardRadicalModulus, HaarModulus.closedRestrictCharacter, MonoidHom.comp_apply]
  exact closedNormalizerCharacter_eq_one_of_commute _ _ _
    fun u _ => (Subgroup.mem_center_iff.mp hz u).symm

variable {K : Subgroup (rationalPoints G)} (hKo : IsOpen (K : Set (rationalPoints G)))
  (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)

include hG hi hν hJ hA hKo in
/-- **Bounds on deep shells.** For `m ∈ M_J(F)`, the function
`y ↦ |δ_{U_J}(m y)^{-1/2}| Ξ(m y)` on `A(F)` is bounded on every shell
`{R₀ < ⟨r, H_0(y)⟩ ≤ B, r ∈ Δ_0 − J}`: it is continuous and invariant under the lattice points
central in `G(F)`, and the shell is compact modulo those. -/
theorem exists_bound_halfModulus_rationalXi (m : standardLeviPoints i ν J) (R₀ B : ℝ) :
    ∃ C : ℝ, ∀ y : rationalPoints A.toGrp,
      (∀ r ∈ simpleRelativeRoots i ν \ J,
        R₀ < RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := q) y) ∧
          RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := q) y) ≤ B) →
      ‖(standardHalfModulus i ν J (m * standardComponentHom hA y))⁻¹‖ *
          rationalXi hKc hPK ((m * standardComponentHom hA y : standardLeviPoints i ν J) :
            rationalPoints G) ≤ C := by
  classical
  have hsplit : IsSplitTorus A.toGrp := hA.1.1
  have : IsAffineHom A.toGrp.X.hom := hsplit.isAffineHom
  have : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  let : TopologicalSpace (rationalPoints A.toGrp) := rationalPointTopology F A.X
  let : Smooth A.X.hom := hsplit.smooth
  let : IsTopologicalGroup (rationalPoints A.toGrp) := rationalPoint_isTopologicalGroup F A.toGrp
  have hι : Continuous (fun y : rationalPoints A.toGrp => rationalPoints.map (q ≫ i) y) :=
    continuous_rationalPointMap F (q ≫ i).hom.hom
  have hj : Continuous (fun y => (m * standardComponentHom hA y : standardLeviPoints i ν J)) :=
    continuous_const.mul (hι.subtype_mk _)
  have hδ : Continuous (fun m : standardLeviPoints i ν J => standardHalfModulus i ν J m) := by
    refine continuous_of_mul_right_invariant isOpen_ker_standardRadicalModulus
      (standardRadicalModulus i ν J).ker.one_mem fun m h hh => ?_
    have h1 : standardRadicalModulus i ν J h = 1 := MonoidHom.mem_ker.mp hh
    rw [standardHalfModulus_mul]
    simp [standardHalfModulus, h1]
  set Sf : Finset (characterLattice S) := ((hi.1.1.finite_simpleRelativeRoots i ν).subset
    (Set.sdiff_subset : simpleRelativeRoots i ν \ J ⊆ simpleRelativeRoots i ν)).toFinset with hSf
  have hmemSf : ∀ r, r ∈ Sf ↔ r ∈ simpleRelativeRoots i ν \ J :=
    fun r => Set.Finite.mem_toFinset _
  obtain ⟨C, hC⟩ := exists_bound_of_latticeSection (CocharacterUniformizer.latticeSection F A)
    (Plancherel.SplitTorus.isCompact_commonNormKernel hsplit)
    (fun x => by
      obtain ⟨c, hc, -⟩ := (CocharacterUniformizer.isUniformizerLatticeSection F A hsplit).2.2 x
      exact ⟨Multiplicative.toAdd c, hc⟩)
    Sf (fun r y => RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := q) y))
    (fun r => (latticePairing S r).toAddMonoidHom.comp
      (RealTorusSpace.cocharacterMapInt (Additive.ofMul q : A ⟶ S)).toAddMonoidHom)
    (fun r _ x c hxc => eval_rationalComponentH0_of_mem_kernel hG hi hν r hxc)
    (Φ := fun y => ‖(standardHalfModulus i ν J (m * standardComponentHom hA y))⁻¹‖ *
      rationalXi hKc hPK ((m * standardComponentHom hA y : standardLeviPoints i ν J) :
        rationalPoints G))
    ((continuous_norm.comp ((hδ.comp hj).inv₀ fun y => standardHalfModulus_ne_zero _)).mul
      ((continuous_rationalXi hKo hKc hPK).comp (continuous_subtype_val.comp hj)))
    (fun x c hc => by
      obtain ⟨hcen, hpar⟩ := map_latticeSection_mem_center hG hi hν hJ hA c
        (fun r hr => hc r ((hmemSf r).2 hr))
      have hz1 : standardRadicalModulus i ν J
          (standardComponentHom hA (CocharacterUniformizer.latticeSection F A (.ofAdd c))) = 1 :=
        standardRadicalModulus_eq_one_of_mem_center _ hcen
      have hzh : standardHalfModulus i ν J
          (standardComponentHom hA (CocharacterUniformizer.latticeSection F A (.ofAdd c))) = 1 := by
        simp [standardHalfModulus, hz1]
      rw [map_mul, ← mul_assoc, standardHalfModulus_mul, hzh, mul_one, Subgroup.coe_mul,
        coe_standardComponentHom, (Subgroup.mem_center_iff.mp hcen _),
        rationalXi_mul_of_mem_center hKo hKc hPK hpar hcen])
    R₀ B
  exact ⟨C, fun y hy => hC y fun r hr => hy r ((hmemSf r).1 hr)⟩

end ShellBound

section Main

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) (K : Subgroup (rationalPoints G)))

-- `M_I(F)` as a subtype of `G(F) = rationalPoints G`, with the membership of `Subgroup G(F)`.
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)) x}

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  (C : Subgroup 𝐌) [C.Normal] (hC : C ≤ Subgroup.center 𝐌)
  [MeasurableSpace (𝐌 ⧸ C)] (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation mu)
  (I' : Finset (RationalPointFamily.SimpleRoot i ν))
  {A : CommGroupScheme (Spec (CommRingCat.of F))} {qA : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν I') A qA)

set_option maxHeartbeats 1600000 in
/-- **The weak constant term as a limit** (Waldspurger, Lemma III.5.1, for the actual orbit
coefficients): `δ_{U'}(m' a)^{-1/2} f_ω(m' a) − (f_ω)^w_{P'}(m' a) → 0` as `a →_{P'} ∞`. -/
theorem rationalOrbitWeakConstantTermLimit :
    RationalOrbitWeakConstantTermLimitStatement hG hi hν I hKc hPK π C hC mu hsq I' hA := by
  intro _ ζ hζ K0 B hK0o hK0c hB hmem hbasis hfin hcover ψ ω m'
  have hJ : RationalPointFamily.rootSet i ν I' ⊆ simpleRelativeRoots i ν :=
    RationalPointFamily.rootSet_subset i ν I'
  have hcoverI := hcover _ (RationalPointFamily.rootSet_subset i ν I)
  have hupper := rationalXiUpperBound_of_jacquetUnipotent rationalMinimalInducedJacquetUnipotent
  -- uniform annihilators of the constant terms at every strict point of `C_A`
  have hann : ∀ y ∈ CocharacterUniformizer.CAstrict F A
      (standardParabolicComponentCharacters i ν (RationalPointFamily.rootSet i ν I') qA),
      HasUniformSplitAnnihilators (standardComponentHom hA) y
        (rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ) :=
    fun y hy => hasUniformSplitAnnihilators_rationalOrbitConstantTerm_of_xiUpperBound hG hi hν I
      hKc hPK hK0c hbasis hcoverI π C hC mu hsq I' hA hB hmem hupper hζ y hy ψ
  -- the constant-term identity on a cone
  have hex := rationalOrbitConstantTermExistence hG hi hν I hKc hPK π C hC mu hsq I' hA hζ hB
    hmem ψ ω
  obtain ⟨ε, hε, heq⟩ := hex.isStandardConstantTerm hA m'
  -- a strict point and the coordinate generators
  obtain ⟨g₀, hg₀CA, -, hg₀pos⟩ := exists_rationalComponentH0_strict hG hi hν hA hζ
  have hg₀s := mem_CAstrict_of_eval_pos hG hi hν hg₀CA hg₀pos
  obtain ⟨d, hd, h, hhT, hhβ, hhα⟩ := exists_rationalComponentH0_generators hG hi hν hA hJ ⟨ζ, hζ⟩
  set R₁ := -Real.logb (LocalField.residueCardinality F) ε with hR₁
  set j := standardComponentHom hA with hjdef
  set c := rationalOrbitConstantTerm hG hi hν I hKc hPK π C hC mu hsq I' hA ψ ω with hcdef
  have hcone : ∀ y : rationalPoints A.toGrp,
      (∀ r ∈ simpleRelativeRoots i ν \ RationalPointFamily.rootSet i ν I',
        R₁ < RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := qA) y)) →
      (standardHalfModulus i ν (RationalPointFamily.rootSet i ν I') (m' * j y))⁻¹ *
          rationalInducedOrbitCoefficientMap hG hi hν I hKc hPK π C hC mu hsq ψ ω
            ((m' * j y : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')) :
              rationalPoints G) = c (m' * j y) :=
    fun y hy => heq y (mem_standardCone_of_eval_gt hG hi hν hε hy)
  refine TendstoZeroAlongParabolic.congr_of_forall
    (g := fun x => positivePart j c (m' * j x)) ?_ (R₀ := R₁)
    (fun x hx => congrArg (fun t => t - weakPart j c (m' * j x))
      (hcone x fun r hr => hx _ (eval_mem_rationalOutsideSimpleForms hi hr)))
  refine tendstoZeroAlongParabolic_of_strictAnnihilators (rationalComponentH0_mul hG hi hν)
    (CocharacterUniformizer.CA F A) ?_ hg₀CA ?_ hd h hhT hhβ hhα ?_
  · -- annihilators of the positive part, transported to `a ↦ (f_ω)^+_{P'}(m' a)`
    intro y hyCA hypos
    obtain ⟨Nw, Np, θ, pw, pp, -, hθ1, -, hppm, -, -, -, hpproots, -, hpp⟩ :=
      hann y (mem_CAstrict_of_eval_pos hG hi hν hyCA
        fun r hr => hypos _ (eval_mem_rationalOutsideSimpleForms hi hr))
    exact ⟨pp ω, hppm ω, θ, hθ1, hpproots ω,
      aeval_rightFunctions_comp_eq_zero (fun x => m' * j x) j
        (fun y x => by simp only [map_mul, mul_assoc]) (hpp ω)⟩
  · intro α hα
    obtain ⟨r, hr, rfl⟩ := (mem_rationalOutsideSimpleForms hi).1 hα
    exact hg₀pos r hr
  · -- boundedness on deep shells
    refine ⟨R₁, fun Bd => ?_⟩
    obtain ⟨Nw, Np, θ, pw, pp, -, hθ1, hpwm, hppm, hpwd, hppd, hpwroots, hpproots, hpw, hpp⟩ :=
      hann g₀ hg₀s
    obtain ⟨Cw, hCw⟩ := exists_norm_le_sum_translates (j g₀) Nw Np hθ1
    set Kt := Np * (Nw - 1) + Np + 1 with hKt
    set Sf : Finset (characterLattice S) := ((hi.1.1.finite_simpleRelativeRoots i ν).subset
      (Set.sdiff_subset : simpleRelativeRoots i ν \ RationalPointFamily.rootSet i ν I' ⊆
        simpleRelativeRoots i ν)).toFinset with hSf
    have hmemSf : ∀ r, r ∈ Sf ↔ r ∈ simpleRelativeRoots i ν \ RationalPointFamily.rootSet i ν I' :=
      fun r => Set.Finite.mem_toFinset _
    set M₀ := ∑ r ∈ Sf, RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := qA) g₀)
      with hM₀def
    have hM₀ : ∀ r ∈ simpleRelativeRoots i ν \ RationalPointFamily.rootSet i ν I',
        RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := qA) g₀) ≤ M₀ :=
      fun r hr => Finset.single_le_sum (f := fun r =>
        RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := qA) g₀))
        (fun r' hr' => (hg₀pos r' ((hmemSf r').1 hr')).le) ((hmemSf r).2 hr)
    obtain ⟨CΦ, hCΦ⟩ := exists_bound_halfModulus_rationalXi hG hi hν hJ hA K.isOpen hKc hPK m' R₁
      (Bd + Kt * M₀)
    obtain ⟨cξ, hcξ, hfξ⟩ :=
      exists_norm_rationalInducedOrbitCoefficientMap_le_rationalXi_of_squareIntegrable hG hi hν I
        hKc hPK hK0c hbasis hcoverI π C hC mu hsq ψ
    have hcb : ∀ y : rationalPoints A.toGrp,
        (∀ r ∈ simpleRelativeRoots i ν \ RationalPointFamily.rootSet i ν I',
          R₁ < RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := qA) y) ∧
            RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := qA) y) ≤ Bd + Kt * M₀) →
        ‖c (m' * j y)‖ ≤ cξ * CΦ := by
      intro y hy
      rw [← hcone y fun r hr => (hy r hr).1, norm_mul]
      calc _ ≤ ‖(standardHalfModulus i ν (RationalPointFamily.rootSet i ν I') (m' * j y))⁻¹‖ *
              (cξ * rationalXi hKc hPK
                ((m' * j y : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')) :
                  rationalPoints G)) :=
            mul_le_mul_of_nonneg_left (hfξ ω _) (norm_nonneg _)
        _ = cξ * (‖(standardHalfModulus i ν (RationalPointFamily.rootSet i ν I') (m' * j y))⁻¹‖ *
              rationalXi hKc hPK
                ((m' * j y : standardLeviPoints i ν (RationalPointFamily.rootSet i ν I')) :
                  rationalPoints G)) := by ring
        _ ≤ cξ * CΦ := mul_le_mul_of_nonneg_left (hCΦ y hy) hcξ.le
    refine ⟨cξ * CΦ + |Cw| * (Kt * (cξ * CΦ)), fun a ha => ?_⟩
    have ha' : ∀ r ∈ simpleRelativeRoots i ν \ RationalPointFamily.rootSet i ν I',
        R₁ < RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := qA) a) ∧
          RealTorusSpace.eval S r (rationalComponentH0 hG hi hν (qA := qA) a) ≤ Bd :=
      fun r hr => ha _ (eval_mem_rationalOutsideSimpleForms hi hr)
    have hshift : ∀ k ∈ Finset.range Kt, ‖c (m' * j a * j g₀ ^ k)‖ ≤ cξ * CΦ := by
      intro k hk
      have e : m' * j a * j g₀ ^ k = m' * j (a * g₀ ^ k) := by rw [map_mul, map_pow, mul_assoc]
      rw [e]
      refine hcb _ fun r hr => ?_
      rw [rationalComponentH0_mul, rationalComponentH0_pow, map_add, map_nsmul, nsmul_eq_mul]
      have h0 := (hg₀pos r hr).le
      have hk' : (k : ℝ) ≤ Kt := by exact_mod_cast (Finset.mem_range.mp hk).le
      have h1 := ha' r hr
      have h2 := hM₀ r hr
      constructor
      · nlinarith
      · nlinarith
    have hw := hCw (pw ω) (pp ω) (hpwm ω) (hppm ω) (hpwd ω) (hppd ω) (hpwroots ω) (hpproots ω)
      c (weakPart j c) (positivePart j c) (weakPart_add_positivePart j c).symm (hpw ω) (hpp ω)
      (m' * j a)
    have hsum : ∑ k ∈ Finset.range Kt, ‖c (m' * j a * j g₀ ^ k)‖ ≤ Kt * (cξ * CΦ) := by
      calc _ ≤ ∑ _k ∈ Finset.range Kt, cξ * CΦ := Finset.sum_le_sum hshift
        _ = Kt * (cξ * CΦ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hc0 : ‖c (m' * j a)‖ ≤ cξ * CΦ := by
      simpa using hshift 0 (Finset.mem_range.mpr (Nat.succ_pos _))
    calc ‖positivePart j c (m' * j a)‖ = ‖c (m' * j a) - weakPart j c (m' * j a)‖ := rfl
      _ ≤ ‖c (m' * j a)‖ + ‖weakPart j c (m' * j a)‖ := norm_sub_le _ _
      _ ≤ cξ * CΦ + |Cw| * (Kt * (cξ * CΦ)) := by
        refine add_le_add hc0 ?_
        calc ‖weakPart j c (m' * j a)‖
            ≤ Cw * ∑ k ∈ Finset.range Kt, ‖c (m' * j a * j g₀ ^ k)‖ := hw
          _ ≤ |Cw| * ∑ k ∈ Finset.range Kt, ‖c (m' * j a * j g₀ ^ k)‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self _)
              (Finset.sum_nonneg fun _ _ => norm_nonneg _)
          _ ≤ |Cw| * (Kt * (cξ * CΦ)) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)

end Main

end Langlands.HarishChandraSchwartz
