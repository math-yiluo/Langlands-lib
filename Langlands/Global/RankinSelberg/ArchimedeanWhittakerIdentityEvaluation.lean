import Langlands.Global.RankinSelberg.ArchimedeanWhittakerRegularity
import Langlands.Global.RankinSelberg.RealPlaceWhittakerCovariance
import Langlands.Global.RankinSelberg.SelfPairPositiveData
import Langlands.Automorphic.CuspidalHilbertOrbitCoefficientProof
import Langlands.Automorphic.CuspidalHilbertCoefficientComparison

/-! # Nonzero evaluation at the identity for actual global Whittaker functions -/

noncomputable section

open NumberField
open scoped Classical ContDiff Manifold Matrix.Norms.Operator CategoryTheory.MonObj Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerEvaluation

open Langlands.Automorphic ContinuousRationalFunctions ArchimedeanGL
  ArchimedeanWhittakerRegularity

private local instance (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
private local instance (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
private local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
private local instance {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
  {r : ℕ} (T : CuspidalOperatorRealization F r)
  (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)

local notation "n" => r + 1

omit [CompactSpace (AdeleQuotient F)] in
private theorem equiv_adelicPoint (g : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    GeneralLinearGroupPoints.adelicEquiv F n (adelicPoint F n (archimedeanGLCoordinates F n g) b) =
      AdelicGL.pair F n g b := by
  rw [adelicEquiv_adelicPoint, ContinuousMulEquiv.symm_apply_apply]

include hχ in
/-- The global coefficient restricted to the infinite group at a fixed finite offset. -/
def coefficient (b : FiniteAdelicGL F n) :
    T.Space →ₗ[ℂ] SmoothFunctions F n where
  toFun x := ⟨fun g => cuspWhittaker F T χ x (adelicPoint F n (archimedeanGLCoordinates F n g) b),
    by
      change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞
        (fun g : ArchimedeanGL F n => cuspWhittaker F T χ x
          (adelicPoint F n (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm g)) b))
      simp only [ContinuousMulEquiv.apply_symm_apply]
      have hVal : ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ArchimedeanMatrix F n) ∞
          (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n) :=
        Units.contMDiff_val
      have h := contMDiffOn_iff_contDiffOn.mpr (contDiffOn_archWhittakerExt T χ hχ x b)
      exact (h.comp_contMDiff hVal (fun g => g.isUnit)).congr
        (fun g => (archWhittakerExt_units T χ hχ x b g).symm)⟩
  map_add' x y := Subtype.ext (funext fun g =>
    UnramifiedWhittaker.cuspWhittaker_add F χ hχ T x y _)
  map_smul' c x := Subtype.ext (funext fun g =>
    UnramifiedWhittaker.cuspWhittaker_smul F χ T c x _)

theorem coefficient_apply (b : FiniteAdelicGL F n) (x : T.Space) (g : InfiniteAdelicGL F n) :
    (coefficient T χ hχ b x).val g =
      cuspWhittaker F T χ x (adelicPoint F n (archimedeanGLCoordinates F n g) b) := rfl

private theorem coefficient_extension (b : FiniteAdelicGL F n) (x : T.Space)
    (g : ArchimedeanGL F n) :
    archWhittakerExt T χ x b (g : ArchimedeanMatrix F n) =
      (coefficient T χ hχ b x).val ((archimedeanGLCoordinates F n).symm g) := by
  rw [coefficient_apply, ContinuousMulEquiv.apply_symm_apply]
  exact archWhittakerExt_units T χ hχ x b g

/-- The analytic coefficient respects the compact right translations of the actual carrier. -/
theorem coefficient_compact (b : FiniteAdelicGL F n) (k : standardInfiniteCompact F n)
    (x : T.Space) :
    coefficient T χ hχ b (T.realization.compactRepresentation k x) =
      ArchimedeanGL.smoothRightAction F n k.val (coefficient T χ hχ b x) := by
  apply Subtype.ext
  funext g
  change cuspWhittaker F T χ (T.realization.compactRepresentation k x)
      (adelicPoint F n (archimedeanGLCoordinates F n g) b) =
    cuspWhittaker F T χ x (adelicPoint F n (archimedeanGLCoordinates F n (g * k.val)) b)
  rw [RealPlaceWhittaker.cuspWhittaker_compact]
  apply congrArg (cuspWhittaker F T χ x)
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [map_mul, MulEquiv.apply_symm_apply, equiv_adelicPoint, equiv_adelicPoint,
    AdelicGL.ofInfinite_eq_pair, AdelicGL.pair_mul, mul_one]

/-- The analytic coefficient respects real Lie differentiation of the actual carrier. -/
theorem coefficient_lie (b : FiniteAdelicGL F n) (X : RealLieAlgebra F n)
    (x : T.Space) :
    coefficient T χ hχ b (T.realization.lieOperator X x) =
      smoothDifferential F n X (coefficient T χ hχ b x) := by
  apply Subtype.ext
  funext g
  rw [smoothDifferential_eq_of_extension F n X _ (archWhittakerExt T χ x b)
    (coefficient_extension T χ hχ b x)]
  rw [fderiv_archWhittakerExt_mul T χ hχ]
  have hlie : lieDeriv T (realLieAlgebraToMatrix F n X) x = T.realization.lieOperator X x := by
    unfold lieDeriv Unfolding.matrixGenerator
    rw [LinearEquiv.symm_apply_apply]
  rw [hlie, archWhittakerExt_units T χ hχ]
  rfl

/-- The actual Whittaker coefficient respects the whole enveloping algebra action. -/
theorem coefficient_enveloping (b : FiniteAdelicGL F n) (a : EnvelopingAlgebra F n) :
    ∀ x : T.Space,
      coefficient T χ hχ b (T.realization.envelopingAction a x) =
        envelopingAction F n a (coefficient T χ hχ b x) := by
  open CuspidalHilbertOrbitCoefficientProof in
  induction a using enveloping_real_left_induction with
  | h1 =>
    intro x
    simp only [map_one, Module.End.one_apply]
  | hadd a a' ha ha' =>
    intro x
    simp only [map_add, LinearMap.add_apply, ha, ha']
  | hsmul c a ha =>
    intro x
    simp only [map_smul, LinearMap.smul_apply, ha]
  | hgen X a ha =>
    intro x
    rw [envelopingAction_generator_mul, coefficient_lie, ha, envelopingAction_mul,
      smoothEnvelopingAction_generator_apply]

/-- Center finiteness and compact finiteness of the actual vector pass to the coefficient. -/
theorem coefficient_jointFinite (b : FiniteAdelicGL F n) (x : T.Space) :
    IsJointFinite F n (coefficient T χ hχ b x) := by
  let C := coefficient T χ hχ b
  have hcenter : IsCenterFinite F n (C x) := by
    obtain ⟨I, hI, hz⟩ := CuspidalHilbertOrbitCoefficient.exists_center_ideal T.realization x
    change Module.Finite ℂ (centerOrbitSpan F n (C x))
    rw [centerOrbitSpan_eq_range]
    let := hI
    have hle : I.restrictScalars ℂ ≤ LinearMap.ker (centerOrbitMap F n (C x)) := by
      intro z hzI
      rw [LinearMap.mem_ker, centerOrbitMap_apply, centerAction_apply,
        ← coefficient_enveloping T χ hχ b, hz z hzI, map_zero]
    have : Module.Finite ℂ (EnvelopingCenter F n ⧸ LinearMap.ker (centerOrbitMap F n (C x))) :=
      Module.Finite.of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle)
    exact Module.Finite.equiv (centerOrbitMap F n (C x)).quotKerEquivRange
  let Φ : T.realization.compactRepresentation.IntertwiningMap
      ((ArchimedeanGL.smoothRightAction F n).comp (standardInfiniteCompact F n).subtype) :=
    { toLinearMap := C
      isIntertwining' := fun k => LinearMap.ext fun y => coefficient_compact T χ hχ b k y }
  have hgroup := (CuspidalHilbertOrbitCoefficient.isFiniteVector_compactRepresentation
    T.realization x).map Φ
  exact separateJointFinite F n (C x) hcenter (compactGroupFiniteDifferential F n (C x) hgroup)

/-- If all coefficient evaluations of a fixed finite slice at the identity vanish,
the whole slice vanishes. -/
theorem coefficient_eq_zero_of_eval_one (b : FiniteAdelicGL F n)
    (h : ∀ x : T.Space, (coefficient T χ hχ b x).val 1 = 0) (x : T.Space) :
    coefficient T χ hχ b x = 0 := by
  apply jointFinite_eq_of_compact_enveloping_values F n _ _ (coefficient_jointFinite T χ hχ b x)
    ((jointFiniteFunctions F n).zero_mem)
  intro a k
  rw [map_zero, ← coefficient_enveloping T χ hχ b]
  have hk := congrArg (fun f : SmoothFunctions F n => f.val 1)
    (coefficient_compact T χ hχ b k (T.realization.envelopingAction a x))
  change (coefficient T χ hχ b
      (T.realization.compactRepresentation k (T.realization.envelopingAction a x))).val 1 =
    (coefficient T χ hχ b (T.realization.envelopingAction a x)).val (1 * k.val) at hk
  rw [one_mul] at hk
  exact hk.symm.trans (h _)

include hχ in
/-- Some actual cuspidal vector has a nonzero global Whittaker value at the identity
for the specified nontrivial character. -/
theorem exists_cuspWhittaker_one_ne_zero :
    ∃ x : T.Space, cuspWhittaker F T χ x 1 ≠ 0 := by
  by_contra! h
  obtain ⟨x, hx⟩ := exists_ne (0 : T.Space)
  obtain ⟨z, hz⟩ := SelfPair.exists_cuspWhittaker_ne_zero T χ hχ hx
  let g := AdelicGL.infinite F n (GeneralLinearGroupPoints.adelicEquiv F n z)
  let b := AdelicGL.finite F n (GeneralLinearGroupPoints.adelicEquiv F n z)
  have hpoint : adelicPoint F n (archimedeanGLCoordinates F n g) b = z := by
    apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
    rw [equiv_adelicPoint]
    exact AdelicGL.pair_projections F n _
  have hb (y : T.Space) : (coefficient T χ hχ b y).val 1 = 0 := by
    rw [coefficient_apply]
    have hp : adelicPoint F n (archimedeanGLCoordinates F n 1) b =
        1 * (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.ofFinite F n b) := by
      apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
      rw [one_mul, equiv_adelicPoint, MulEquiv.apply_symm_apply, AdelicGL.ofFinite_eq_pair]
    rw [hp, ← UnramifiedWhittaker.cuspWhittaker_finiteRepresentation]
    exact h (T.realization.finiteRepresentation b y)
  have hzero := congrArg (fun f : SmoothFunctions F n => f.val g)
    (coefficient_eq_zero_of_eval_one T χ hχ b hb x)
  exact hz ((congrArg (cuspWhittaker F T χ x) hpoint).symm.trans hzero)

omit [CompactSpace (AdeleQuotient F)] in
theorem adelicPoint_one :
    adelicPoint F n 1 1 = 1 := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [adelicEquiv_adelicPoint, map_one, map_one, ← AdelicGL.ofFinite_eq_pair, map_one]

include hχ in
/-- A nonzero actual real-place restriction can be chosen with finite offset one. -/
theorem exists_realPlaceWhittaker_one_ne_zero
    (v : {v : InfinitePlace F // v.IsReal}) :
    ∃ W, IsRealPlaceWhittaker F T χ v W ∧ W 1 ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_cuspWhittaker_one_ne_zero T χ hχ
  refine ⟨fun g => cuspWhittaker F T χ x (realPlacePoint F n v g * finitePoint F n 1),
    ⟨x, 1, rfl⟩, ?_⟩
  simpa only [realPlacePoint, finitePoint, map_one, adelicPoint_one, one_mul] using hx

include hχ in
/-- A nonzero actual complex-place restriction can be chosen with finite offset one. -/
theorem exists_complexPlaceWhittaker_one_ne_zero
    (w : {v : InfinitePlace F // v.IsComplex}) :
    ∃ W, IsComplexPlaceWhittaker F T χ w W ∧ W 1 ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_cuspWhittaker_one_ne_zero T χ hχ
  refine ⟨fun g => cuspWhittaker F T χ x (complexPlacePoint F n w g * finitePoint F n 1),
    ⟨x, 1, rfl⟩, ?_⟩
  simpa only [complexPlacePoint, finitePoint, map_one, adelicPoint_one, one_mul] using hx

end Langlands.Global.RankinSelbergGlobal.ArchimedeanWhittakerEvaluation
