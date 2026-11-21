import Langlands.Representation.FiniteVectors
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.RepresentationTheory.Intertwining

/-! # Operator actions on spans of translated functions -/

noncomputable section

universe uA uV uX uR

set_option autoImplicit false

namespace Langlands.Automorphic

variable {A : Type uA} {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Apply a complex linear operator to each coefficient of a finite family. -/
def finsuppCoefficientEnd (A : Type uA) (V : Type uV) [AddCommGroup V] [Module ℂ V] :
    Module.End ℂ V →ₐ[ℂ] Module.End ℂ (A →₀ V) where
  toFun L := Finsupp.mapRange.linearMap L
  map_one' := LinearMap.ext fun v => Finsupp.ext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun v => Finsupp.ext fun _ => rfl
  map_zero' := LinearMap.ext fun v => Finsupp.ext fun a => by
    change (0 : V) = (0 : A →₀ V) a
    rw [Finsupp.zero_apply]
  map_add' _ _ := LinearMap.ext fun v => Finsupp.ext fun _ => rfl
  commutes' c := LinearMap.ext fun v => Finsupp.ext fun a => by
    simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    rfl

@[simp]
theorem finsuppCoefficientEnd_single (L : Module.End ℂ V) (a : A) (v : V) :
    finsuppCoefficientEnd A V L (Finsupp.single a v) = Finsupp.single a (L v) :=
  Finsupp.mapRange_single (hf := L.map_zero)

section Translates

variable [Monoid A] {X : Type uX}
  (β : Representation ℂ A (X → ℂ)) (φ : V →ₗ[ℂ] (X → ℂ))

/-- The evaluation of a finite family is the sum of the translated functions. -/
def translatedFunctionSum : (A →₀ V) →ₗ[ℂ] (X → ℂ) :=
  Finsupp.lsum ℂ fun a => (β a).comp φ

@[simp]
theorem translatedFunctionSum_single (a : A) (v : V) :
    translatedFunctionSum β φ (Finsupp.single a v) = β a (φ v) :=
  Finsupp.lsum_single ℂ _ a v

/-- Multiplying the index on the left shifts the labels of the translated functions. -/
def translationIndexAction : Representation ℂ A (A →₀ V) where
  toFun a := Finsupp.lmapDomain V ℂ (a * ·)
  map_one' := Finsupp.lhom_ext fun b v => by simp only [Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, one_mul, Module.End.one_apply]
  map_mul' a b := Finsupp.lhom_ext fun c v => by
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      Module.End.mul_apply, mul_assoc]

@[simp]
theorem translationIndexAction_single (a b : A) (v : V) :
    translationIndexAction (V := V) a (Finsupp.single b v) = Finsupp.single (a * b) v :=
  Finsupp.mapDomain_single

theorem translationIndexAction_commute (a : A) (L : Module.End ℂ V) :
    Commute (translationIndexAction (V := V) a) (finsuppCoefficientEnd A V L) :=
  Finsupp.lhom_ext fun b v => by simp only [Module.End.mul_apply, finsuppCoefficientEnd_single,
    translationIndexAction_single]

theorem translatedFunctionSum_shift (a : A) (v : A →₀ V) :
    translatedFunctionSum β φ (translationIndexAction a v) = β a (translatedFunctionSum β φ v) := by
  have h : (translatedFunctionSum β φ).comp (translationIndexAction a) =
      (β a).comp (translatedFunctionSum β φ) := by
    apply Finsupp.lhom_ext
    intro b w
    simp only [LinearMap.comp_apply, translationIndexAction_single, translatedFunctionSum_single,
      map_mul, Module.End.mul_apply]
  exact LinearMap.congr_fun h v

/-- The actual translated function space modeled as a quotient by zero evaluation. -/
abbrev TranslatedFunctionSpan := (A →₀ V) ⧸ LinearMap.ker (translatedFunctionSum β φ)

/-- Evaluate a quotient element as a function. -/
def translatedFunctionEmbedding : TranslatedFunctionSpan β φ →ₗ[ℂ] (X → ℂ) :=
  (LinearMap.ker (translatedFunctionSum β φ)).liftQ (translatedFunctionSum β φ) le_rfl

theorem translatedFunctionEmbedding_injective : Function.Injective (translatedFunctionEmbedding β φ) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)

/-- The translation action descends and acts on the represented functions by translation. -/
def translatedFunctionAction : Representation ℂ A (TranslatedFunctionSpan β φ) :=
  (translationIndexAction (V := V)).quotient (LinearMap.ker (translatedFunctionSum β φ))
    fun a v hv => LinearMap.mem_ker.mpr (by
      rw [translatedFunctionSum_shift, LinearMap.mem_ker.mp hv, map_zero])

theorem translatedFunctionEmbedding_action (a : A) (v : TranslatedFunctionSpan β φ) :
    translatedFunctionEmbedding β φ (translatedFunctionAction β φ a v) =
      β a (translatedFunctionEmbedding β φ v) := by
  refine Submodule.Quotient.induction_on _ v ?_
  exact translatedFunctionSum_shift β φ a

theorem translatedFunctionAction_isFiniteVector (hφ : ∀ v, FiniteVectors.IsFiniteVector β (φ v))
    (v : TranslatedFunctionSpan β φ) : FiniteVectors.IsFiniteVector (translatedFunctionAction β φ) v := by
  let E : (translatedFunctionAction β φ).IntertwiningMap β :=
    { toLinearMap := translatedFunctionEmbedding β φ
      isIntertwining' a := LinearMap.ext fun v => translatedFunctionEmbedding_action β φ a v }
  apply (FiniteVectors.isFiniteVector_map_iff E (translatedFunctionEmbedding_injective β φ) v).mp
  refine Submodule.Quotient.induction_on _ v ?_
  intro w
  change FiniteVectors.IsFiniteVector β (translatedFunctionSum β φ w)
  induction w using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact FiniteVectors.isFiniteVector_zero β
  | add x y hx hy => rw [map_add]; exact hx.add hy
  | single a v =>
    rw [translatedFunctionSum_single]
    exact (FiniteVectors.isFiniteVector_iff β _).mpr ⟨FiniteVectors.orbitSubrepresentation β (φ v),
      hφ v, FiniteVectors.action_mem_orbitSpan β a (φ v)⟩

end Translates

section Quotient

variable {R : Type uR} [Ring R] [Algebra ℂ R]

/-- Descend an algebra action to a stable complex quotient. -/
def stableQuotientAlgebraAction (ρ : R →ₐ[ℂ] Module.End ℂ V) (P : Submodule ℂ V)
    (hP : ∀ a v, v ∈ P → ρ a v ∈ P) : R →ₐ[ℂ] Module.End ℂ (V ⧸ P) where
  toFun a := P.mapQ P (ρ a) (fun v hv => hP a v hv)
  map_one' := Submodule.linearMap_qext _ <| LinearMap.ext fun v => by
    change P.mkQ (ρ 1 v) = P.mkQ v
    rw [map_one, Module.End.one_apply]
  map_mul' a b := Submodule.linearMap_qext _ <| LinearMap.ext fun v => by
    change P.mkQ (ρ (a * b) v) = P.mkQ (ρ a (ρ b v))
    rw [map_mul, Module.End.mul_apply]
  map_zero' := Submodule.linearMap_qext _ <| LinearMap.ext fun v => by
    change P.mkQ (ρ 0 v) = 0
    simp only [map_zero, LinearMap.zero_apply]
  map_add' a b := Submodule.linearMap_qext _ <| LinearMap.ext fun v => by
    change P.mkQ (ρ (a + b) v) = P.mkQ (ρ a v) + P.mkQ (ρ b v)
    rw [map_add, LinearMap.add_apply, map_add]
  commutes' c := Submodule.linearMap_qext _ <| LinearMap.ext fun v => by
    change P.mkQ (ρ (algebraMap ℂ R c) v) = (algebraMap ℂ (Module.End ℂ (V ⧸ P)) c) (P.mkQ v)
    rw [ρ.commutes]
    simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, map_smul]

@[simp]
theorem stableQuotientAlgebraAction_mkQ (ρ : R →ₐ[ℂ] Module.End ℂ V) (P : Submodule ℂ V)
    (hP : ∀ a v, v ∈ P → ρ a v ∈ P) (a : R) (v : V) :
    stableQuotientAlgebraAction ρ P hP a (P.mkQ v) = P.mkQ (ρ a v) := rfl

variable [Monoid A] {X : Type uX}
  (β : Representation ℂ A (X → ℂ)) (φ : V →ₗ[ℂ] (X → ℂ))
  (ρ : R →ₐ[ℂ] Module.End ℂ V)

/-- Descend the coefficient action to the span of translated functions. -/
def translatedFunctionOperatorAction
    (h : ∀ a v, v ∈ LinearMap.ker (translatedFunctionSum β φ) →
      finsuppCoefficientEnd A V (ρ a) v ∈ LinearMap.ker (translatedFunctionSum β φ)) :
    R →ₐ[ℂ] Module.End ℂ (TranslatedFunctionSpan β φ) :=
  stableQuotientAlgebraAction ((finsuppCoefficientEnd A V).comp ρ)
    (LinearMap.ker (translatedFunctionSum β φ)) h

theorem translatedFunctionOperatorAction_commute
    (h : ∀ a v, v ∈ LinearMap.ker (translatedFunctionSum β φ) →
      finsuppCoefficientEnd A V (ρ a) v ∈ LinearMap.ker (translatedFunctionSum β φ))
    (a : A) (b : R) :
    Commute (translatedFunctionAction β φ a) (translatedFunctionOperatorAction β φ ρ h b) := by
  apply Submodule.linearMap_qext _
  apply LinearMap.ext
  intro v
  let P := LinearMap.ker (translatedFunctionSum β φ)
  change P.mkQ (translationIndexAction a (finsuppCoefficientEnd A V (ρ b) v)) =
    P.mkQ (finsuppCoefficientEnd A V (ρ b) (translationIndexAction a v))
  exact congrArg P.mkQ (LinearMap.congr_fun (translationIndexAction_commute a (ρ b)).eq v)

end Quotient

end Langlands.Automorphic
