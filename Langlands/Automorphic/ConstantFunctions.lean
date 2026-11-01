import Langlands.Automorphic.RegularAlgebraic
import Langlands.Automorphic.FullOperatorRealization

/-!
# Actual constant automorphic functions

Constant functions satisfy all defining automorphic conditions. Their genuine
archimedean differentials act through the existing enveloping augmentation.
-/

noncomputable section

universe uF

open scoped Classical TensorProduct Manifold Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.ConstantFunctions

open Langlands.Global NumberField ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- Actual real-smooth constant functions on the completion-based infinite group. -/
def archimedean : ℂ →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n where
  toFun c := ⟨fun _ => c, contMDiff_const⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem archimedean_apply (c : ℂ) (g : InfiniteAdelicGL F n) :
    (archimedean F n c).val g = c := rfl

/-- The actual directional derivative kills a constant, in the actual matrix coordinates. -/
theorem smoothDifferential_archimedean (X : ArchimedeanGL.RealLieAlgebra F n) (c : ℂ) :
    ArchimedeanGL.smoothDifferential F n X (archimedean F n c) = 0 := by
  apply Subtype.ext
  funext g
  change fderiv ℝ (fun _ : ArchimedeanMatrix F n => c) _ _ = 0
  simp

theorem complexSmoothLieAction_archimedean
    (X : ArchimedeanGL.ComplexLieAlgebra F n) (c : ℂ) :
    ArchimedeanGL.complexSmoothLieAction F n X (archimedean F n c) = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [ArchimedeanGL.complexSmoothLieAction_tmul, LinearMap.smul_apply,
      smoothDifferential_archimedean, smul_zero]
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply, hX, hY, add_zero]

/-- Every genuine enveloping differential acts on constants through the augmentation. -/
theorem envelopingAction_archimedean (a : ArchimedeanGL.EnvelopingAlgebra F n) (c : ℂ) :
    ArchimedeanGL.envelopingAction F n a (archimedean F n c) =
      archimedean F n (ArchimedeanGL.augmentation F n a * c) := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ArchimedeanGL.ComplexLieAlgebra F n)) a
  change ArchimedeanGL.envelopingAction F n
      (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) (archimedean F n c) =
    archimedean F n
      (ArchimedeanGL.augmentation F n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) * c)
  induction t using TensorAlgebra.induction generalizing c with
  | algebraMap z =>
    simp only [AlgHom.commutes]
    rfl
  | ι X =>
    change ArchimedeanGL.envelopingAction F n (ArchimedeanGL.envelopingGenerator F n X)
      (archimedean F n c) = _
    rw [ArchimedeanGL.envelopingAction_generator, complexSmoothLieAction_archimedean]
    change 0 = archimedean F n
      (ArchimedeanGL.augmentation F n (ArchimedeanGL.envelopingGenerator F n X) * c)
    simp
  | mul x y hx hy =>
    simp only [map_mul, Module.End.mul_apply, hy, hx, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, add_mul]

/-- Actual continuous rational-left-invariant constant adelic functions. -/
def continuous : ℂ →ₗ[ℂ] ContinuousRationalFunctions F n where
  toFun c := ⟨⟨fun _ => c, fun _ _ => rfl⟩, continuous_const⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evaluate_continuous (c : ℂ) (x : AdelicGL F n) :
    evaluate F n (continuous F n c) x = c := rfl

theorem continuous_injective : Function.Injective (continuous F n) := by
  intro c d h
  exact congrArg (fun f => evaluate F n f 1) h

@[simp]
theorem rightAction_continuous (g : AdelicGL F n) (c : ℂ) :
    continuousRightAction F n g (continuous F n c) = continuous F n c := rfl

/-- Constants have real-smooth infinite slices and the whole finite group as a stabilizer. -/
def finiteSmooth : ℂ →ₗ[ℂ] FiniteSmoothRationalFunctions F n where
  toFun c := ⟨continuous F n c, by
    constructor
    · change continuous F n c ∈ (⨅ b : FiniteAdelicGL F n,
        (ArchimedeanGL.smoothFunctions F n).comap (infiniteSlice F n b) :
          Submodule ℂ (ContinuousRationalFunctions F n))
      apply (Submodule.mem_iInf _).mpr
      intro b
      exact (archimedean F n c).property
    · exact ⟨⊤, fun _ => rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem finiteSmoothSlice_finiteSmooth (b : FiniteAdelicGL F n) (c : ℂ) :
    finiteSmoothSlice F n b (finiteSmooth F n c) = archimedean F n c := rfl

@[simp]
theorem finiteSmoothRightAction_finiteSmooth (g : AdelicGL F n) (c : ℂ) :
    finiteSmoothRightAction F n g (finiteSmooth F n c) = finiteSmooth F n c := rfl

/-- The genuine adelic enveloping action has the same constant-scalar formula. -/
theorem finiteSmoothEnvelopingAction_finiteSmooth
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (c : ℂ) :
    finiteSmoothEnvelopingAction F n a (finiteSmooth F n c) =
      finiteSmooth F n (ArchimedeanGL.augmentation F n a * c) := by
  apply finiteSmoothSlice_injective F n
  funext b
  change finiteSmoothSlice F n b
      (finiteSmoothEnvelopingAction F n a (finiteSmooth F n c)) =
    finiteSmoothSlice F n b
      (finiteSmooth F n (ArchimedeanGL.augmentation F n a * c))
  rw [finiteSmoothSlice_envelopingAction, finiteSmoothSlice_finiteSmooth,
    envelopingAction_archimedean, finiteSmoothSlice_finiteSmooth]

/-- The common center orbit of the entire slice family is finite dimensional. -/
theorem isCenterFinite_finiteSmooth (c : ℂ) :
    IsCenterFinite F n (finiteSmoothInclusion F n (finiteSmooth F n c)) := by
  apply (isCenterFinite_iff_finiteSmoothCenterVector F n _).mpr
  change Module.Finite ℂ (FiniteVectors.orbitSpan (finiteSmoothCenterRepresentation F n)
    (finiteSmooth F n c))
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (finiteSmooth F n))
  apply Submodule.span_le.mpr
  rintro _ ⟨z, rfl⟩
  exact ⟨_, finiteSmoothEnvelopingAction_finiteSmooth F n
    (ArchimedeanGL.centerInclusion F n z) c |>.symm⟩

/-- Constants are finite under every infinite subgroup, in particular the standard compact. -/
theorem isInfiniteFinite_continuous (U : Subgroup (InfiniteAdelicGL F n)) (c : ℂ) :
    IsInfiniteFinite F n U (continuous F n c) := by
  change Module.Finite ℂ (infiniteOrbitSpan F n U (continuous F n c))
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (continuous F n))
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact ⟨c, rfl⟩

/-- Every constant satisfies all the defining automorphic conditions. -/
theorem isAutomorphicForm_finiteSmooth (c : ℂ) :
    IsAutomorphicForm F n (finiteSmoothInclusion F n (finiteSmooth F n c)) := by
  refine ⟨(hasFiniteLevel_iff_mem_finiteSmooth F n _).mpr
    (finiteSmooth F n c).property.2,
    isInfiniteFinite_continuous F n (standardInfiniteCompact F n) c,
    isCenterFinite_finiteSmooth F n c, ?_⟩
  intro b
  exact ArchimedeanGL.HasPolynomialGrowth.const c

/-- A concrete constant automorphic form, with every defining condition proved. -/
def form : ℂ →ₗ[ℂ] AutomorphicForms F n where
  toFun c := ⟨finiteSmooth F n c,
    (mem_automorphicSubrepresentation F n _).mpr (isAutomorphicForm_finiteSmooth F n c)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem evaluate_form (c : ℂ) (x : AdelicGL F n) :
    evaluate F n (automorphicToContinuous F n (form F n c)) x = c := rfl

theorem form_injective : Function.Injective (form F n) := by
  intro c d h
  exact congrArg (fun f => evaluate F n (automorphicToContinuous F n f) 1) h

/-- This constructs a nonzero form in every rank and number-field universe. -/
theorem form_one_ne_zero : form F n 1 ≠ 0 := by
  intro h
  have he := congrArg (fun f => evaluate F n (automorphicToContinuous F n f) 1) h
  exact one_ne_zero he

@[simp]
theorem automorphicFiniteRightAction_form (d : FiniteAdelicGL F n) (c : ℂ) :
    automorphicFiniteRightAction F n d (form F n c) = form F n c := rfl

@[simp]
theorem automorphicCompactRightAction_form (k : standardInfiniteCompact F n) (c : ℂ) :
    automorphicCompactRightAction F n k (form F n c) = form F n c := rfl

theorem automorphicEnvelopingAction_form
    (a : ArchimedeanGL.EnvelopingAlgebra F n) (c : ℂ) :
    automorphicEnvelopingAction F n a (form F n c) =
      form F n (ArchimedeanGL.augmentation F n a * c) := by
  apply Subtype.ext
  exact finiteSmoothEnvelopingAction_finiteSmooth F n a c

/-- The constant line is invariant under the entire concrete operator algebra. -/
theorem invariant_range_finiteSmooth :
    ∀ (a : automorphicOperatorAlgebra F n) (f), f ∈ LinearMap.range (finiteSmooth F n) →
      a.val f ∈ LinearMap.range (finiteSmooth F n) := by
  apply (operator_invariant_iff F n (LinearMap.range (finiteSmooth F n))).mpr
  refine ⟨?_, ?_, ?_⟩
  · rintro d f ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro k f ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro a f ⟨c, rfl⟩
    exact ⟨_, (finiteSmoothEnvelopingAction_finiteSmooth F n a c).symm⟩

/-- The very same constant forms, viewed in the published stable realization carrier. -/
def stableForm : ℂ →ₗ[ℂ] StableAutomorphicFunctions F n :=
  (stableAutomorphicEquiv F n).symm.toLinearMap.comp (form F n)

@[simp]
theorem stableForm_val (c : ℂ) : (stableForm F n c).val = finiteSmooth F n c := rfl

theorem stableForm_injective : Function.Injective (stableForm F n) :=
  (stableAutomorphicEquiv F n).symm.injective.comp (form_injective F n)

/-- The actual constant subspace of forms, preserved by all three operator families. -/
def realization : OperatorRealization F n where
  toSubmodule := LinearMap.range (stableForm F n)
  apply_mem_toSubmodule a _f hf := by
    obtain ⟨c, rfl⟩ := hf
    obtain ⟨d, hd⟩ := invariant_range_finiteSmooth F n a (finiteSmooth F n c) ⟨c, rfl⟩
    refine ⟨d, ?_⟩
    apply Subtype.ext
    exact hd

local instance : AddCommGroup (realization F n).Space := Submodule.addCommGroup _

/-- Scalars identify with the actual embedded constant line, with no existence input. -/
def scalarEquiv : ℂ ≃ₗ[ℂ] (realization F n).Space :=
  LinearEquiv.ofInjective (stableForm F n) (stableForm_injective F n)

@[simp]
theorem formInclusion_scalarEquiv (c : ℂ) :
    (realization F n).formInclusion (scalarEquiv F n c) = form F n c := rfl

@[simp]
theorem evaluate_scalarEquiv (c : ℂ) (x : AdelicGL F n) :
    evaluate F n ((realization F n).toContinuous (scalarEquiv F n c)) x = c := rfl

/-- Evaluation at the identity is the inverse of the concrete constant-line map. -/
theorem scalarEquiv_symm_apply (f : (realization F n).Space) :
    (scalarEquiv F n).symm f = evaluate F n ((realization F n).toContinuous f) 1 := by
  obtain ⟨c, rfl⟩ := (scalarEquiv F n).surjective f
  rw [LinearEquiv.symm_apply_apply, evaluate_scalarEquiv]

theorem realization_finrank : Module.finrank ℂ (realization F n).Space = 1 := by
  rw [← (scalarEquiv F n).finrank_eq, Module.finrank_self]

@[simp]
theorem finiteRepresentation_scalarEquiv (d : FiniteAdelicGL F n) (c : ℂ) :
    (realization F n).finiteRepresentation d (scalarEquiv F n c) =
      scalarEquiv F n c := rfl

@[simp]
theorem compactRepresentation_scalarEquiv (k : standardInfiniteCompact F n) (c : ℂ) :
    (realization F n).compactRepresentation k (scalarEquiv F n c) =
      scalarEquiv F n c := rfl

/-- Genuine enveloping differentials restrict to their augmentation on the constant line. -/
theorem envelopingAction_scalarEquiv (a : ArchimedeanGL.EnvelopingAlgebra F n) (c : ℂ) :
    (realization F n).envelopingAction a (scalarEquiv F n c) =
      scalarEquiv F n (ArchimedeanGL.augmentation F n a * c) := by
  apply Subtype.ext
  apply Subtype.ext
  exact finiteSmoothEnvelopingAction_finiteSmooth F n a c

theorem realization_hasInfinitesimalCharacter :
    (realization F n).HasInfinitesimalCharacter
      ((ArchimedeanGL.augmentation F n).comp (ArchimedeanGL.centerInclusion F n)) := by
  intro z f
  obtain ⟨c, rfl⟩ := (scalarEquiv F n).surjective f
  rw [envelopingAction_scalarEquiv]
  exact (scalarEquiv F n).map_smul (ArchimedeanGL.augmentation F n z.val) c

/-- The actual constant realization has regular algebraic infinitesimal character of weight zero. -/
theorem realization_isRegularAlgebraic : (realization F n).IsRegularAlgebraic :=
  ⟨_, ArchimedeanGL.isRegularAlgebraicCharacter_augmentation F n,
    realization_hasInfinitesimalCharacter F n⟩

end Langlands.Automorphic.ConstantFunctions
