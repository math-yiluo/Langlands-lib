import Langlands.Global.AdelicRootHyperplaneStatement
import Langlands.Global.AdelicSquareIntegrableInducedForms
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Real and complex coordinates adapted to the imaginary axis

For an abelian group `X` (the rational characters of a parabolic), complexification
`ℝ ⊗ X → ℂ ⊗ X`, coordinates `ℝⁿ ≃ ℝ ⊗ X` and their complex-linear extension `ℂⁿ ≃ ℂ ⊗ X`, and
the behaviour of the imaginary parameters, the real part and the root forms in these
coordinates. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.ImaginaryAxis

section Generic

variable {X : Type*} [AddCommGroup X]

/-- Complexification `ℝ ⊗ X → ℂ ⊗ X`, `r ⊗ χ ↦ r ⊗ χ`. -/
def complexify : ℝ ⊗[ℤ] X →ₗ[ℝ] ℂ ⊗[ℤ] X :=
  AlgebraTensorModule.map (Algebra.linearMap ℝ ℂ) LinearMap.id

@[simp]
theorem complexify_tmul (r : ℝ) (χ : X) :
    complexify (r ⊗ₜ[ℤ] χ) = (r : ℂ) ⊗ₜ[ℤ] χ := rfl

/-- The map `μ ↦ iμ` is `i` times complexification. -/
theorem map_I_eq_smul_complexify (y : ℝ ⊗[ℤ] X) :
    AlgebraTensorModule.map (LinearMap.toSpanSingleton ℝ ℂ Complex.I) LinearMap.id y =
      Complex.I • complexify y := by
  induction y using TensorProduct.inductionOn with
  | tmul r χ =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.toSpanSingleton_apply, LinearMap.id_coe,
      id_eq, complexify_tmul, TensorProduct.smul_tmul', smul_eq_mul, Complex.real_smul]
    ring_nf
  | add a b ha hb => simp [ha, hb, smul_add]

/-- The real part of `iμ` vanishes. -/
theorem map_re_map_I (y : ℝ ⊗[ℤ] X) :
    AlgebraTensorModule.map Complex.reLm (LinearMap.id : X →ₗ[ℤ] X)
      (AlgebraTensorModule.map (LinearMap.toSpanSingleton ℝ ℂ Complex.I) LinearMap.id y) = 0 := by
  induction y using TensorProduct.inductionOn with
  | tmul r χ => simp
  | add a b ha hb => simp [ha, hb]

/-- Finite dimensionality over `ℂ` of `ℂ ⊗ X` gives finite dimensionality over `ℝ` of
`ℝ ⊗ X`. -/
theorem finiteDimensional_real [FiniteDimensional ℂ (ℂ ⊗[ℤ] X)] :
    FiniteDimensional ℝ (ℝ ⊗[ℤ] X) := by
  have e := AlgebraTensorModule.cancelBaseChange ℤ ℝ ℂ ℂ X
  have h1 : Module.rank ℂ (ℂ ⊗[ℝ] (ℝ ⊗[ℤ] X)) < Cardinal.aleph0 := by
    rw [e.rank_eq]
    exact Module.rank_lt_aleph0 ℂ _
  rw [Module.rank_baseChange, Cardinal.lift_lt_aleph0] at h1
  exact Module.rank_lt_aleph0_iff.mp h1

theorem cancelBaseChange_one_tmul (v : ℝ ⊗[ℤ] X) :
    AlgebraTensorModule.cancelBaseChange ℤ ℝ ℂ ℂ X ((1 : ℂ) ⊗ₜ[ℝ] v) = complexify v := by
  induction v using TensorProduct.inductionOn with
  | tmul r χ =>
    rw [AlgebraTensorModule.cancelBaseChange_tmul, complexify_tmul, Complex.real_smul, mul_one]
  | add a b ha hb => rw [TensorProduct.tmul_add, map_add, ha, hb, map_add]

variable [FiniteDimensional ℝ (ℝ ⊗[ℤ] X)]

/-- Real coordinates `ℝⁿ ≃ ℝ ⊗ X` from Mathlib's chosen basis. -/
def realCoordinates :
    (Fin (Module.finrank ℝ (ℝ ⊗[ℤ] X)) → ℝ) ≃ₗ[ℝ] ℝ ⊗[ℤ] X :=
  (Module.finBasis ℝ (ℝ ⊗[ℤ] X)).equivFun.symm

/-- The complexified basis of `ℂ ⊗ X`. -/
def complexBasis : Module.Basis (Fin (Module.finrank ℝ (ℝ ⊗[ℤ] X))) ℂ (ℂ ⊗[ℤ] X) :=
  ((Module.finBasis ℝ (ℝ ⊗[ℤ] X)).baseChange ℂ).map
    (AlgebraTensorModule.cancelBaseChange ℤ ℝ ℂ ℂ X)

theorem complexBasis_apply (j : Fin (Module.finrank ℝ (ℝ ⊗[ℤ] X))) :
    complexBasis j = complexify (Module.finBasis ℝ (ℝ ⊗[ℤ] X) j) := by
  rw [complexBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    cancelBaseChange_one_tmul]

/-- Complex coordinates `ℂⁿ ≃ ℂ ⊗ X`, the complex-linear extension of `realCoordinates`. -/
def complexCoordinates :
    (Fin (Module.finrank ℝ (ℝ ⊗[ℤ] X)) → ℂ) ≃ₗ[ℂ] ℂ ⊗[ℤ] X :=
  (complexBasis (X := X)).equivFun.symm

theorem complexCoordinates_ofReal (x : Fin (Module.finrank ℝ (ℝ ⊗[ℤ] X)) → ℝ) :
    complexCoordinates (fun j => (x j : ℂ)) = complexify (realCoordinates x) := by
  rw [complexCoordinates, realCoordinates, Module.Basis.equivFun_symm_apply,
    Module.Basis.equivFun_symm_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [complexBasis_apply, map_smul]
  exact algebraMap_smul ℂ (x j) _

/-- The slice `x ↦ i x` of `ℂⁿ`. -/
def imaginarySlice {n : ℕ} (x : Fin n → ℝ) : Fin n → ℂ := fun j => Complex.I * x j

theorem complexCoordinates_imaginarySlice (x : Fin (Module.finrank ℝ (ℝ ⊗[ℤ] X)) → ℝ) :
    complexCoordinates (imaginarySlice x) =
      AlgebraTensorModule.map (LinearMap.toSpanSingleton ℝ ℂ Complex.I) LinearMap.id
        (realCoordinates x) := by
  have : imaginarySlice x = Complex.I • fun j => (x j : ℂ) := by
    ext j; simp [imaginarySlice]
  rw [this, map_smul, complexCoordinates_ofReal, map_I_eq_smul_complexify]

end Generic

section Parabolic

open Langlands.GroupScheme Langlands.Global.AdelicGroupPoints

variable {F : Type*} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

omit [NumberField F] in
/-- The complex root form restricts to the real one on complexified real parameters. -/
theorem rootFunctional_complexify (β : characterLattice A) (y : RealCharacterParameter F P) :
    r.rootFunctional hA hT β (complexify y) = (r.realRootFunctional hA hT β y : ℂ) := by
  induction y using TensorProduct.inductionOn with
  | tmul s χ =>
    rw [complexify_tmul, ParabolicRootPresentation.rootFunctional_tmul]
    have : (s ⊗ₜ[ℤ] χ : RealCharacterParameter F P) = s • ((1 : ℝ) ⊗ₜ[ℤ] χ) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul, Complex.ofReal_mul]
  | add a b ha hb => simp [map_add, ha, hb]

omit [NumberField F] in
/-- Imaginary parameters have real part zero, so every root form vanishes on their real part. -/
theorem realRootFunctional_parameterRealPart_imaginaryParameter (β : characterLattice A)
    (y : RealCharacterParameter F P) :
    r.realRootFunctional hA hT β (parameterRealPart F P (imaginaryParameter F P y)) = 0 := by
  have h : parameterRealPart F P (imaginaryParameter F P y) = 0 :=
    map_re_map_I (X := GroupScheme.rationalCharacters P) y
  rw [h, map_zero]

omit [NumberField F] in
/-- A parameter whose real part has root form at most `R` along a unipotent root is not
`R`-regular. -/
theorem not_isRegularParameter_of_le {R : ℝ} {β : characterLattice A}
    (hβ : β ∈ r.unipotentRoots) {lam : ComplexCharacterParameter F P}
    (h : r.realRootFunctional hA hT β (parameterRealPart F P lam) ≤ R) :
    ¬ r.IsRegularParameter hA hT R lam := fun hreg =>
  absurd (lt_of_lt_of_le (hreg β hβ : R < r.realRootFunctional hA hT β
    (parameterRealPart F P lam)) h) (lt_irrefl R)

end Parabolic

end Langlands.Global.ImaginaryAxis
