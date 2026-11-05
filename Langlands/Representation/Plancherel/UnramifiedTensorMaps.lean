import Langlands.Representation.Plancherel.UnramifiedUniversalTwist

/-!
# Specialization of regular-linear tensor maps

Polynomial families of operators on any parameter subset are exactly the
specializations of maps linear over the concrete regular algebra. Existence
uses a basis of the source; uniqueness is asserted only when specialization
is known at every actual unramified character. The rational version retains
one denominator, nonzero on the whole subset, for all source vectors.
-/

noncomputable section

open scoped TensorProduct NNReal

namespace Langlands.Plancherel

universe uG uI uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

local instance unramifiedTensorMapAddCommGroup
    (X : Type*) [AddCommGroup X] [Module ℂ X] :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] X) :=
  TensorProduct.addCommGroup

/-- Extend a complex-linear map into the target tensor by regular scalars. -/
def unramifiedTensorMapLift
    (f : V →ₗ[ℂ] unramifiedRegularFunctions ν ⊗[ℂ] W) :
    unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[unramifiedRegularFunctions ν]
      unramifiedRegularFunctions ν ⊗[ℂ] W :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.id : unramifiedRegularFunctions ν →ₗ[unramifiedRegularFunctions ν]
      unramifiedRegularFunctions ν).smulRight f)

@[simp]
theorem unramifiedTensorMapLift_tmul
    (f : V →ₗ[ℂ] unramifiedRegularFunctions ν ⊗[ℂ] W)
    (b : unramifiedRegularFunctions ν) (v : V) :
    unramifiedTensorMapLift ν f (b ⊗ₜ[ℂ] v) = b • f v := rfl

/-- The operator on the original carriers obtained by specializing a
regular-linear tensor map at an actual character. -/
def unramifiedTensorMapSpecialization
    (T : unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[unramifiedRegularFunctions ν]
      unramifiedRegularFunctions ν ⊗[ℂ] W)
    (χ : unramifiedCharacters ν) : V →ₗ[ℂ] W :=
  (LinearMap.proj χ).comp ((unramifiedTensorEvaluation ν W).comp
    ((T.restrictScalars ℂ).comp
      (TensorProduct.mk ℂ (unramifiedRegularFunctions ν) V 1)))

@[simp]
theorem unramifiedTensorMapSpecialization_apply
    (T : unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[unramifiedRegularFunctions ν]
      unramifiedRegularFunctions ν ⊗[ℂ] W)
    (χ : unramifiedCharacters ν) (v : V) :
    unramifiedTensorMapSpecialization ν T χ v =
      unramifiedTensorEvaluation ν W (T (1 ⊗ₜ[ℂ] v)) χ := rfl

/-- Specialization commutes with a regular-linear map on every tensor,
including tensors whose coefficients vary with the parameter. -/
theorem unramifiedTensorEvaluation_map
    (T : unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[unramifiedRegularFunctions ν]
      unramifiedRegularFunctions ν ⊗[ℂ] W)
    (t : unramifiedRegularFunctions ν ⊗[ℂ] V) (χ : unramifiedCharacters ν) :
    unramifiedTensorEvaluation ν W (T t) χ =
      unramifiedTensorMapSpecialization ν T χ (unramifiedTensorEvaluation ν V t χ) := by
  induction t using TensorProduct.inductionOn with
  | tmul b v =>
    have hb : b ⊗ₜ[ℂ] v = b • ((1 : unramifiedRegularFunctions ν) ⊗ₜ[ℂ] v) := by
      simp [TensorProduct.smul_tmul']
    rw [unramifiedTensorEvaluation_tmul, hb, T.map_smul,
      unramifiedTensorEvaluation_regular_smul, map_smul]
    rfl
  | add t u ht hu =>
    simp only [map_add, Pi.add_apply, ht, hu]

/-- Every regular-linear tensor map gives a polynomial operator family
on every parameter subset. -/
theorem unramifiedTensorMapSpecialization_isPolynomialOperatorOn
    (T : unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[unramifiedRegularFunctions ν]
      unramifiedRegularFunctions ν ⊗[ℂ] W)
    (Ω : Set (unramifiedCharacters ν)) :
    UnramifiedOperatorFamily.IsPolynomialOperatorOn Ω
      (fun χ => unramifiedTensorMapSpecialization ν T χ.val) :=
  fun v => unramifiedTensorEvaluation_isPolynomialOn ν W Ω (T (1 ⊗ₜ[ℂ] v))

/-- Simultaneous specialization at all characters determines the map.
No analogous uniqueness assertion is made on an arbitrary subset. -/
theorem unramifiedTensorMapSpecialization_injective :
    Function.Injective
      (unramifiedTensorMapSpecialization ν :
        (unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[unramifiedRegularFunctions ν]
          unramifiedRegularFunctions ν ⊗[ℂ] W) →
        unramifiedCharacters ν → V →ₗ[ℂ] W) := by
  intro T S h
  apply LinearMap.ext
  intro t
  apply unramifiedTensorEvaluation_injective ν W
  funext χ
  rw [unramifiedTensorEvaluation_map, unramifiedTensorEvaluation_map, h]

/-- Polynomiality on a subset gives one regular-linear map whose
specialization agrees with every operator of the family. The choices on a
basis need no density or finite-dimensionality assumption. -/
theorem isPolynomialOperatorOn_iff_exists_unramifiedTensorMap
    (Ω : Set (unramifiedCharacters ν)) (A : Ω → V →ₗ[ℂ] W) :
    UnramifiedOperatorFamily.IsPolynomialOperatorOn Ω A ↔
      ∃ T : unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[unramifiedRegularFunctions ν]
          unramifiedRegularFunctions ν ⊗[ℂ] W,
        ∀ (χ : Ω) (t : unramifiedRegularFunctions ν ⊗[ℂ] V),
          unramifiedTensorEvaluation ν W (T t) χ.val =
            A χ (unramifiedTensorEvaluation ν V t χ.val) := by
  classical
  constructor
  · intro hA
    let e := Module.Free.chooseBasis ℂ V
    have hex := fun i =>
      (isPolynomialOn_iff_exists_unramifiedTensor ν W Ω (fun χ => A χ (e i))).mp
        (hA (e i))
    choose t ht using hex
    let f := e.constr ℂ t
    have hf (χ : Ω) :
        (LinearMap.proj χ.val).comp ((unramifiedTensorEvaluation ν W).comp f) = A χ := by
      apply e.ext
      intro i
      simpa only [f, LinearMap.comp_apply, LinearMap.proj_apply,
        Module.Basis.constr_basis] using ht i χ
    refine ⟨unramifiedTensorMapLift ν f, ?_⟩
    intro χ s
    rw [unramifiedTensorEvaluation_map]
    have hs : unramifiedTensorMapSpecialization ν (unramifiedTensorMapLift ν f) χ.val =
        A χ := by
      ext v
      simpa using LinearMap.congr_fun (hf χ) v
    rw [hs]
  · rintro ⟨T, hT⟩ v
    apply (isPolynomialOn_iff_exists_unramifiedTensor ν W Ω _).mpr
    refine ⟨T (1 ⊗ₜ[ℂ] v), ?_⟩
    intro χ
    simpa using hT χ (1 ⊗ₜ[ℂ] v)

/-- Rationality has exactly the same single-denominator quantifier order
when expressed by one regular-linear numerator on the tensor modules. -/
theorem isRationalOperatorOn_iff_exists_unramifiedTensorNumerator
    (Ω : Set (unramifiedCharacters ν)) (A : Ω → V →ₗ[ℂ] W) :
    UnramifiedOperatorFamily.IsRationalOperatorOn Ω A ↔
      ∃ (b : unramifiedRegularFunctions ν)
        (T : unramifiedRegularFunctions ν ⊗[ℂ] V →ₗ[unramifiedRegularFunctions ν]
          unramifiedRegularFunctions ν ⊗[ℂ] W),
        (∀ χ : Ω, b.val χ.val ≠ 0) ∧
        ∀ (χ : Ω) (t : unramifiedRegularFunctions ν ⊗[ℂ] V),
          unramifiedTensorEvaluation ν W (T t) χ.val =
            b.val χ.val • A χ (unramifiedTensorEvaluation ν V t χ.val) := by
  constructor
  · rintro ⟨b, hb, hA⟩
    obtain ⟨T, hT⟩ := (isPolynomialOperatorOn_iff_exists_unramifiedTensorMap ν Ω
      (fun χ => b.val χ.val • A χ)).mp hA
    exact ⟨b, T, hb, hT⟩
  · rintro ⟨b, T, hb, hT⟩
    refine ⟨b, hb, ?_⟩
    exact (isPolynomialOperatorOn_iff_exists_unramifiedTensorMap ν Ω
      (fun χ => b.val χ.val • A χ)).mpr ⟨T, hT⟩

end Langlands.Plancherel
