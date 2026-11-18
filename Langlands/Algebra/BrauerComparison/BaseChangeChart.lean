import Langlands.Algebra.BrauerComparison.Relative
import Langlands.Algebra.BrauerScalarExtension
import Langlands.Algebra.MatrixSplitDefect
import Langlands.Algebra.TensorProductSplittingCharts

/-! # Scalar extension of an actual relative Brauer chart -/

noncomputable section

open Matrix
open scoped TensorProduct

universe u v

namespace Langlands.BrauerComparison

open CentralSimple CentralSimple.SemilinearGaloisAction
open ClassFieldTheory.Local (relativeInflation relativeRestriction)
open GroupScheme.SpecialLinearInnerForm (conjugationAlgHom)

attribute [local instance] coefficientGLAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (E M : Type u) [Field E] [Field M] [Algebra K E] [Algebra K M]
  [Algebra E M] [Algebra L M] [IsScalarTower K E M] [IsScalarTower K L M]
  {A : CSA.{u, u} K} {I : Type v} [Fintype I] [DecidableEq I]

/-- Extend the splitting field of a matrix chart along `L → M`. -/
def enlargedSplittingChart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    M ⊗[K] A ≃ₐ[M] Matrix I I M :=
  (Brauer.baseChangeTowerEquiv L M A).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[M] M) e).trans matrixBaseChangeChart

@[simp] theorem enlargedSplittingChart_tmul (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (m : M) (a : A) :
    enlargedSplittingChart M e (m ⊗ₜ[K] a) =
      m • (e (1 ⊗ₜ[K] a)).map (algebraMap L M) := by
  have h : (Brauer.baseChangeTowerEquiv L M A).symm (m ⊗ₜ[K] a) =
      m ⊗ₜ[L] ((1 : L) ⊗ₜ[K] a) := by
    apply (Brauer.baseChangeTowerEquiv L M A).injective
    rw [AlgEquiv.apply_symm_apply, Brauer.baseChangeTowerEquiv_tmul, one_smul]
  simp [enlargedSplittingChart, h, Algebra.TensorProduct.congr_apply]

/-- Extend an `L`-splitting chart to an `M`-splitting chart of the scalar-extended algebra. -/
def baseChangeSplittingChart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    M ⊗[E] (E ⊗[K] A) ≃ₐ[M] Matrix I I M :=
  (Brauer.baseChangeTowerEquiv E M A).trans (enlargedSplittingChart M e)

@[simp] theorem baseChangeSplittingChart_tmul (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (m : M) (r : E) (a : A) :
    baseChangeSplittingChart E M e (m ⊗ₜ[E] (r ⊗ₜ[K] a)) =
      (r • m) • (e (1 ⊗ₜ[K] a)).map (algebraMap L M) := by
  simp [baseChangeSplittingChart]

omit [Fintype I] [DecidableEq I] in
private theorem tower_coefficientMap (s : Gal(M/E)) (Z : M ⊗[E] (E ⊗[K] A)) :
    Brauer.baseChangeTowerEquiv E M A (tensorCoefficientMap s Z) =
      tensorCoefficientMap (s.restrictScalars K) (Brauer.baseChangeTowerEquiv E M A Z) := by
  induction Z with
  | tmul m b =>
    induction b with
    | tmul x a =>
      simp only [tensorCoefficientMap_tmul, Brauer.baseChangeTowerEquiv_tmul]
      have hx : s (x • m) = x • s m := by
        simp only [Algebra.smul_def, map_mul, s.commutes]
      exact congrArg (fun y : M => y ⊗ₜ[K] a) hx.symm
    | add b b' hb hb' => simp only [TensorProduct.tmul_add, map_add, hb, hb']
  | add Z Z' hZ hZ' => simp only [map_add, hZ, hZ']

variable [Normal K L]

/-- Include the restricted two-cochain in the units of the upper field. -/
def baseChangeFactor (c : Gal(L/K) → Gal(L/K) → Lˣ) (s t : Gal(M/E)) : Mˣ :=
  Units.map (algebraMap L M).toMonoidHom
    (c ((s.restrictScalars K).restrictNormal L) ((t.restrictScalars K).restrictNormal L))

omit [Fintype I] [DecidableEq I] in
private theorem baseChangeMatrix_map (s : Gal(M/E)) (X : Matrix I I L) :
    (X.map (algebraMap L M)).map s =
      (X.map ((s.restrictScalars K).restrictNormal L)).map (algebraMap L M) := by
  ext i j
  exact ((s.restrictScalars K).restrictNormal_commutes L (X i j)).symm

/-- The coefficient extension of the original inner lift at the restricted automorphism. -/
def baseChangeLift (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (s : Gal(M/E)) : GL I M :=
  GeneralLinearGroup.map (algebraMap L M)
    ((splittingChartIndexAction e).innerMatrix ((s.restrictScalars K).restrictNormal L))

/-- The extended lifts act on the enlarged chart by semilinear conjugation. -/
theorem enlargedSplittingChart_action (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (s : Gal(M/K)) (X : Matrix I I M) :
    (splittingChartIndexAction (enlargedSplittingChart M e)).act s X =
      (baseChangeLift K M e s : Matrix I I M) * X.map s *
        ((baseChangeLift K M e s)⁻¹ : GL I M) := by
  let f := algebraMap L M
  let ρ := splittingChartIndexAction e
  let r := (s.restrictScalars K).restrictNormal L
  let P := ρ.innerMatrix r
  let Q := baseChangeLift K M e s
  let conj := conjugationAlgHom (R := M) Q
  let Φ := conj.toRingHom.comp s.mapMatrix.toRingHom
  change (splittingChartIndexAction (enlargedSplittingChart M e)).act s X = Φ X
  have hsmul (m : M) (Z : Matrix I I M) : Φ (m • Z) = s m • Φ Z := by
    have hmap : (m • Z).map s = s m • Z.map s := by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    change conj ((m • Z).map s) = s m • conj (Z.map s)
    rw [hmap, map_smul]
  have hfixed (a : A) : Φ ((e (1 ⊗ₜ[K] a)).map f) = (e (1 ⊗ₜ[K] a)).map f := by
    let Y := e (1 ⊗ₜ[K] a)
    have hY : ρ.act r Y = Y := by
      simp only [ρ, Y, splittingChartIndexAction_apply, tensorCoefficientMap_tmul, map_one]
    change (Q : Matrix I I M) * (Y.map f).map s * (Q⁻¹ : GL I M) = Y.map f
    rw [baseChangeMatrix_map (K := K) K M]
    change ((P : Matrix I I L).map f) * (Y.map r).map f *
      (((P⁻¹ : GL I L) : Matrix I I L).map f) = Y.map f
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun Z : Matrix I I L => Z.map f) ((ρ.act_eq_innerMatrix r Y).symm.trans hY)
  obtain ⟨Z, rfl⟩ := (enlargedSplittingChart M e).surjective X
  rw [splittingChartIndexAction_apply]
  induction Z with
  | tmul m a =>
    rw [tensorCoefficientMap_tmul, enlargedSplittingChart_tmul, enlargedSplittingChart_tmul,
      hsmul, hfixed]
  | add Z Z' hZ hZ' => simp only [map_add, hZ, hZ']

/-- The chart of the scalar-extended algebra uses the same lifts at restricted automorphisms. -/
theorem baseChangeSplittingChart_action (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (s : Gal(M/E)) (X : Matrix I I M) :
    (splittingChartIndexAction (baseChangeSplittingChart E M e)).act s X =
      (baseChangeLift E M e s : Matrix I I M) * X.map s *
        ((baseChangeLift E M e s)⁻¹ : GL I M) := by
  obtain ⟨Z, rfl⟩ := (baseChangeSplittingChart E M e).surjective X
  rw [splittingChartIndexAction_apply]
  simp only [baseChangeSplittingChart, AlgEquiv.trans_apply, tower_coefficientMap E M]
  rw [← splittingChartIndexAction_apply, enlargedSplittingChart_action]
  rfl

/-- The scalar factor for the extended lifts is the included restricted factor. -/
theorem baseChangeLift_mul (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) (s t : Gal(M/E)) :
    baseChangeLift E M e s * (s • baseChangeLift E M e t) =
      GeneralLinearGroup.scalar I
        (baseChangeFactor E M (splittingChartIndexAction e).scalarDefect s t) *
          baseChangeLift E M e (s * t) := by
  let F := GeneralLinearGroup.map (n := I) (algebraMap L M)
  let r : Gal(M/E) →* Gal(L/K) :=
    (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom K)
  let ρ := splittingChartIndexAction e
  have h (g : GL I L) : s • F g = F ((r s) • g) := by
    apply Units.ext
    exact baseChangeMatrix_map E M s (g : Matrix I I L)
  change F (ρ.innerMatrix (r s)) * (s • F (ρ.innerMatrix (r t))) =
    GeneralLinearGroup.scalar I (Units.map (algebraMap L M).toMonoidHom
      (ρ.scalarDefect (r s) (r t))) * F (ρ.innerMatrix (r (s * t)))
  rw [h, ← map_mul F, ρ.innerMatrix_mul, map_mul F, GeneralLinearGroup.map_scalar, map_mul r]
  rfl

variable [Nonempty I]

/-- Enlarging the splitting field inflates the relative class. -/
theorem relativeClass_enlargedSplittingChart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    relativeClass (enlargedSplittingChart M e) =
      relativeInflation K L M 2 (relativeClass e) := by
  rw [relativeClass, descentClass_eq_of_lifts _ (baseChangeLift K M e)
    (baseChangeFactor K M (splittingChartIndexAction e).scalarDefect)
    (enlargedSplittingChart_action M e) (baseChangeLift_mul K M e)]
  simp only [relativeClass, descentClass, unitClass, groupCohomology.H2π_comp_map_apply]
  congr 1

/-- The mixed chart computes inflation followed by ordinary restriction. -/
theorem relativeClass_baseChangeSplittingChart (e : L ⊗[K] A ≃ₐ[L] Matrix I I L) :
    relativeClass (baseChangeSplittingChart E M e) =
      relativeRestriction K E M 2 (relativeInflation K L M 2 (relativeClass e)) := by
  rw [relativeClass, descentClass_eq_of_lifts _ (baseChangeLift E M e)
    (baseChangeFactor E M (splittingChartIndexAction e).scalarDefect)
    (baseChangeSplittingChart_action E M e) (baseChangeLift_mul E M e)]
  simp only [relativeClass, descentClass, unitClass, groupCohomology.H2π_comp_map_apply]
  congr 1

end Langlands.BrauerComparison
