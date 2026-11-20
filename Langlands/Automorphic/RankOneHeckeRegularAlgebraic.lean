import Langlands.Automorphic.RankOneHeckeRealization
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Global.InfinityType
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Regular algebraicity of the automorphic `GL(1)` realization of a Hecke character

The center of the enveloping algebra acts on `RankOneHecke.cuspidal χ` through the augmentation
composed with the shift by the derivative of `χ ∘ det`. When that derivative is an integral
combination of the embedding coordinates, this infinitesimal character is Clozel's regular
algebraic one, with the integral weights as highest weight. Over a totally complex field this
is the case when `χ` has, at every complex place, the parameter of `z ↦ z^a z̄^b` with integers
`a, b`.
-/

noncomputable section

universe u uP

open scoped Manifold ContDiff Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.RankOneHecke

open Langlands.Global Langlands.LocalFactor.Archimedean Langlands.Archimedean
open Langlands.Archimedean.ComplexDeterminantTwist

/-- The values of the algebraic character `z ↦ z^a z̄^b` in `ℂ`. -/
theorem complexCharacter_val (a b : ℤ) (z : ℂˣ) :
    ((InfinityType.complexCharacter a b z : ℂˣ) : ℂ) = (z : ℂ) ^ a * star (z : ℂ) ^ b := by
  rw [InfinityType.complexCharacter_apply, Units.val_mul, Units.val_zpow_eq_zpow_val,
    Units.val_zpow_eq_zpow_val, Units.coe_star]

/-- Character data of `z ↦ z^a z̄^b` for integers `a, b`: weight `a - b` and exponent
`(a + b) / 2`. -/
def exponentData (a b : ℤ) : ComplexCharacterData where
  character := InfinityType.complexCharacter a b
  weight := a - b
  exponent := ((a + b : ℤ) : ℂ) / 2
  character_eq z := by
    have hz : (z : ℂ) ≠ 0 := z.ne_zero
    have hn : (‖(z : ℂ)‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    have hpow : ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ (2 * (((a + b : ℤ) : ℂ) / 2)) =
        ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ (a + b) := by
      rw [show (2 : ℂ) * (((a + b : ℤ) : ℂ) / 2) = ((a + b : ℤ) : ℂ) by ring,
        Complex.cpow_intCast]
    have hstar : star (z : ℂ) = ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ 2 / (z : ℂ) := by
      rw [eq_div_iff hz]
      have hm : star (z : ℂ) * (z : ℂ) = ((Complex.normSq (z : ℂ) : ℝ) : ℂ) := by
        rw [mul_comm]
        exact Complex.mul_conj (z : ℂ)
      rw [hm, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [complexCharacter_val]
    rw [hpow, hstar, div_zpow, ← zpow_natCast (((‖(z : ℂ)‖ : ℝ) : ℂ)) 2, ← zpow_mul, div_zpow,
      zpow_sub₀ hz, zpow_sub₀ hn, zpow_add₀ hn,
      show ((2 : ℕ) : ℤ) * b = b + b by push_cast; ring, zpow_add₀ hn]
    field_simp

@[simp]
theorem exponentData_character_apply (a b : ℤ) (z : ℂˣ) :
    ((exponentData a b).character z : ℂ) = (z : ℂ) ^ a * star (z : ℂ) ^ b :=
  complexCharacter_val a b z

/-- The derivative at `1` of `g ↦ η(det g)` on `GL_1(ℂ)`, for `η(z) = z^a z̄^b`, along `X`
is `a X₀₀ + b X̄₀₀`. -/
theorem rightDerivative_detCharacter_exponentData (a b : ℤ) (X : Matrix (Fin 1) (Fin 1) ℂ) :
    rightDerivative (matrixModel ℂ 1) X
        (detCharacter (n := 1) (exponentData a b).character) 1 =
      (a : ℂ) * X 0 0 + (b : ℂ) * starRingEnd ℂ (X 0 0) := by
  rw [rightDerivative_eq_fderiv (contMDiff_detCharacter _) X 1, Units.val_one, one_mul]
  let P : Matrix (Fin 1) (Fin 1) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    { toFun := fun Y => Y 0 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let Q : Matrix (Fin 1) (Fin 1) ℂ →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.comp P
  have hP1 : P 1 = 1 := by simp [P]
  have hQ1 : Q 1 = 1 := by simp [Q, hP1]
  let G : Matrix (Fin 1) (Fin 1) ℂ → ℂ := fun Y => P Y ^ a * Q Y ^ b
  have heq : unitsExtension (detCharacter (n := 1) (exponentData a b).character) =ᶠ[nhds 1] G := by
    filter_upwards [isOpen_setOf_isUnit_matrix.mem_nhds (isUnit_one (M := Matrix (Fin 1) (Fin 1) ℂ))]
      with Y hY
    obtain ⟨g, rfl⟩ := hY
    rw [unitsExtension_val, detCharacter, exponentData_character_apply,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
    rfl
  have h1 : HasFDerivAt (fun Y => P Y ^ a) (((a : ℂ) * 1 ^ (a - 1)) • P) 1 := by
    have h := (hasDerivAt_zpow a (P 1) (Or.inl (by rw [hP1]; exact one_ne_zero))).comp_hasFDerivAt
      (1 : Matrix (Fin 1) (Fin 1) ℂ) P.hasFDerivAt
    rw [hP1] at h
    exact h
  have h2 : HasFDerivAt (fun Y => Q Y ^ b) (((b : ℂ) * 1 ^ (b - 1)) • Q) 1 := by
    have h := (hasDerivAt_zpow b (Q 1) (Or.inl (by rw [hQ1]; exact one_ne_zero))).comp_hasFDerivAt
      (1 : Matrix (Fin 1) (Fin 1) ℂ) Q.hasFDerivAt
    rw [hQ1] at h
    exact h
  have hG : HasFDerivAt G ((P 1 ^ a) • (((b : ℂ) * 1 ^ (b - 1)) • Q) +
      (Q 1 ^ b) • (((a : ℂ) * 1 ^ (a - 1)) • P)) 1 := h1.mul h2
  rw [heq.fderiv_eq, hG.fderiv]
  simp only [add_apply, smul_apply, hP1, hQ1, one_zpow,
    mul_one, one_mul, smul_eq_mul]
  simp [P, Q]
  ring

end Langlands.Automorphic.RankOneHecke

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.LocalFactor.Archimedean
open Langlands.Archimedean NumberField

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]

local instance rankOneRegularRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance rankOneRegularContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance rankOneRegularSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance rankOneRegularFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance rankOneRegularStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

local instance rankOneRegularSpaceGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace RankOneHecke

/-- The algebra character of the enveloping algebra of `GL_1` by which it acts on the line
`χ ∘ det`: the augmentation composed with the shift attached to `χ`. -/
def envelopingCharacter (χ : HeckeCharacter F) : EnvelopingAlgebra F 1 →ₐ[ℂ] ℂ :=
  (augmentation F 1).comp (heckeEnvelopingShift 1 χ)

/-- The infinitesimal character of the `GL(1)` realization of `χ`. -/
def infinitesimalCharacter (χ : HeckeCharacter F) : EnvelopingCenter F 1 →ₐ[ℂ] ℂ :=
  (envelopingCharacter χ).comp (centerInclusion F 1)

/-- The enveloping character on a Lie generator is the derivative of `χ ∘ det`. -/
theorem envelopingCharacter_envelopingGenerator (χ : HeckeCharacter F)
    (U : ComplexLieAlgebra F 1) :
    envelopingCharacter χ (envelopingGenerator F 1 U) =
      complexCharacterDifferential (χ.infiniteDeterminantCharacter 1)
        (χ.infiniteDeterminantCharacter_mem_smoothFunctions 1) U := by
  change augmentation F 1 (characterShift _ _ (envelopingGenerator F 1 U)) = _
  rw [characterShift, envelopingShift_generator, map_add, AlgHom.commutes,
    augmentation_envelopingGenerator, zero_add]
  rfl

/-- On the complexification of a real direction the enveloping character is the real
derivative of `χ ∘ det`. -/
theorem envelopingCharacter_realGenerator (χ : HeckeCharacter F) (X : ArchimedeanMatrix F 1) :
    envelopingCharacter χ (realGenerator F 1 X) =
      characterDifferential (χ.infiniteDeterminantCharacter 1)
        (χ.infiniteDeterminantCharacter_mem_smoothFunctions 1)
        ((realLieAlgebraToMatrix F 1).symm X) := by
  rw [realGenerator, envelopingCharacter_envelopingGenerator, complexify_apply,
    complexCharacterDifferential_tmul, one_mul]

/-- The one-dimensional module of the enveloping algebra of `GL_1` acting through the
enveloping character of `χ`. -/
def characterModule (χ : HeckeCharacter F) : ModuleCat.{u} (EnvelopingAlgebra F 1) :=
  letI : Module (EnvelopingAlgebra F 1) (ULift.{u} ℂ) :=
    Module.compHom (ULift.{u} ℂ) (envelopingCharacter χ).toRingHom
  ModuleCat.of (EnvelopingAlgebra F 1) (ULift.{u} ℂ)

/-- The vector `1` of the character module. -/
def characterVector (χ : HeckeCharacter F) : characterModule χ := (ULift.up 1 : ULift.{u} ℂ)

theorem characterModule_smul (χ : HeckeCharacter F) (a : EnvelopingAlgebra F 1)
    (w : characterModule χ) :
    a • w = (ULift.up (envelopingCharacter χ a * ULift.down w) : ULift.{u} ℂ) := rfl

/-- **Regular algebraicity criterion in rank one.** If the derivative of `χ ∘ det` along every
diagonal direction is the weight `μ`, with integral entries, then the infinitesimal character of
the `GL(1)` realization of `χ` is regular algebraic. -/
theorem isRegularAlgebraicCharacter_infinitesimalCharacter (χ : HeckeCharacter F)
    (μ : EmbeddingIndex F → Fin 1 → ℤ)
    (hμ : ∀ d : Fin 1 → mixedEmbedding.mixedSpace F,
      characterDifferential (χ.infiniteDeterminantCharacter 1)
          (χ.infiniteDeterminantCharacter_mem_smoothFunctions 1)
          ((realLieAlgebraToMatrix F 1).symm (Matrix.diagonal d)) =
        diagonalWeight F 1 (fun j i => (μ j i : ℂ)) d) :
    IsRegularAlgebraicCharacter F 1 (infinitesimalCharacter χ) := by
  refine ⟨μ, fun j a b _ => ?_, characterModule χ, characterVector χ, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h : a = b := Subsingleton.elim a b
    rw [h]
  · intro h
    exact one_ne_zero (congrArg ULift.down h)
  · intro d
    rw [characterModule_smul, characterModule_smul, envelopingCharacter_realGenerator, hμ d,
      AlgHom.commutes]
    rfl
  · intro i j hij
    exact absurd hij (by
      have hi : i = j := Subsingleton.elim i j
      rw [hi]
      exact lt_irrefl j)
  · intro z
    rw [characterModule_smul, characterModule_smul, AlgHom.commutes]
    rfl

variable [CompactSpace (AdeleQuotient F)]

set_option maxHeartbeats 1600000 in
/-- The center of the enveloping algebra acts on the `GL(1)` realization of `χ` through
`infinitesimalCharacter χ`. -/
theorem cuspidal_hasInfinitesimalCharacter (χ : HeckeCharacter F) :
    (cuspidal χ).realization.HasInfinitesimalCharacter (infinitesimalCharacter χ) := by
  intro z f
  obtain ⟨c, hc⟩ := (ConstantFunctions.scalarEquiv F 1).surjective
    (((ConstantFunctions.realization F 1).heckeDeterminantTwistEquiv χ).symm f)
  have hf : f = (ConstantFunctions.realization F 1).heckeDeterminantTwistEquiv χ
      (ConstantFunctions.scalarEquiv F 1 c) := by
    rw [hc]
    exact (((ConstantFunctions.realization F 1).heckeDeterminantTwistEquiv χ).apply_symm_apply
      f).symm
  subst hf
  have h1 := (ConstantFunctions.realization F 1).heckeDeterminantTwistEquiv_differential χ
    (z : EnvelopingAlgebra F 1) (ConstantFunctions.scalarEquiv F 1 c)
  have h2 := ConstantFunctions.envelopingAction_scalarEquiv F 1
    (heckeEnvelopingShift 1 χ (z : EnvelopingAlgebra F 1)) c
  have h3 : ConstantFunctions.scalarEquiv F 1
      (augmentation F 1 (heckeEnvelopingShift 1 χ (z : EnvelopingAlgebra F 1)) * c) =
        augmentation F 1 (heckeEnvelopingShift 1 χ (z : EnvelopingAlgebra F 1)) •
          ConstantFunctions.scalarEquiv F 1 c :=
    (ConstantFunctions.scalarEquiv F 1).map_smul _ c
  exact h1.trans ((congrArg ((ConstantFunctions.realization F 1).heckeDeterminantTwistEquiv χ)
    (h2.trans h3)).trans
      (((ConstantFunctions.realization F 1).heckeDeterminantTwistEquiv χ).map_smul _ _))

/-- The `GL(1)` realization of `χ` is regular algebraic when the derivative of `χ ∘ det` along
diagonal directions is an integral weight. -/
theorem cuspidal_isRegularAlgebraic (χ : HeckeCharacter F)
    (μ : EmbeddingIndex F → Fin 1 → ℤ)
    (hμ : ∀ d : Fin 1 → mixedEmbedding.mixedSpace F,
      characterDifferential (χ.infiniteDeterminantCharacter 1)
          (χ.infiniteDeterminantCharacter_mem_smoothFunctions 1)
          ((realLieAlgebraToMatrix F 1).symm (Matrix.diagonal d)) =
        diagonalWeight F 1 (fun j i => (μ j i : ℂ)) d) :
    (cuspidal χ).isoClass.IsRegularAlgebraic :=
  (CuspidalOperatorRealization.isoClass_isRegularAlgebraic_iff _).mpr
    ⟨infinitesimalCharacter χ, isRegularAlgebraicCharacter_infinitesimalCharacter χ μ hμ,
      cuspidal_hasInfinitesimalCharacter χ⟩

/-- The integral weight attached to exponents `a v, b v` at the complex places: `a v` at the
coordinate of `v` and `b v` at its conjugate. -/
def exponentWeight (a b : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v} → ℤ) :
    EmbeddingIndex F → Fin 1 → ℤ
  | .inl _, _ => 0
  | .inr (v, false), _ => a v
  | .inr (v, true), _ => b v

omit [CompactSpace (AdeleQuotient F)] in
/-- Over a totally complex field, if `χ` has at every complex place `v` the parameter of
`z ↦ z^(a v) z̄^(b v)`, then the derivative of `χ ∘ det` on `GL_1` along a diagonal direction is
the weight `exponentWeight a b`. -/
theorem characterDifferential_diagonal [NumberField.IsTotallyComplex F] {χ : HeckeCharacter F}
    (a b : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v} → ℤ)
    (hχ : ∀ v, χ.HasComplexPlaceParameter v (exponentData (a v) (b v)))
    (d : Fin 1 → mixedEmbedding.mixedSpace F) :
    characterDifferential (χ.infiniteDeterminantCharacter 1)
        (χ.infiniteDeterminantCharacter_mem_smoothFunctions 1)
        ((realLieAlgebraToMatrix F 1).symm (Matrix.diagonal d)) =
      diagonalWeight F 1 (fun j i => (exponentWeight a b j i : ℂ)) d := by
  classical
  have hRP : IsEmpty {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v} :=
    ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr
      (NumberField.IsTotallyComplex.isComplex v.1)) v.2⟩
  rw [← sum_placeLieInclusions F 1 ((realLieAlgebraToMatrix F 1).symm (Matrix.diagonal d)),
    map_add, map_sum, map_sum, Finset.univ_eq_empty, Finset.sum_empty, zero_add]
  simp only [ComplexPlaceHeckeTwist.characterDifferential_complexPlaceLieInclusion 1 (hχ _),
    rightDerivative_detCharacter_exponentData]
  simp only [diagonalWeight, Fin.sum_univ_one, Fintype.sum_sum_type, Finset.univ_eq_empty,
    Finset.sum_empty, zero_add, Fintype.sum_prod_type, Fintype.sum_bool, exponentWeight,
    embeddingComponent_inr_false, embeddingComponent_inr_true]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h0 : complexPlaceLieProjection F 1 v ((realLieAlgebraToMatrix F 1).symm (Matrix.diagonal d))
      0 0 = (d 0).2 v := by
    change ((Matrix.diagonal d) 0 0).2 v = _
    rw [Matrix.diagonal_apply_eq]
  rw [h0]
  ring

/-- Over a totally complex field, the `GL(1)` realization of a Hecke character with integral
exponents at every complex place is regular algebraic. -/
theorem cuspidal_isRegularAlgebraic_of_exponentData [NumberField.IsTotallyComplex F]
    {χ : HeckeCharacter F}
    (a b : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v} → ℤ)
    (hχ : ∀ v, χ.HasComplexPlaceParameter v (exponentData (a v) (b v))) :
    (cuspidal χ).isoClass.IsRegularAlgebraic :=
  cuspidal_isRegularAlgebraic χ (exponentWeight a b) (characterDifferential_diagonal a b hχ)

end RankOneHecke

end Langlands.Automorphic
