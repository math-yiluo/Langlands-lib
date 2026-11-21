import Langlands.Automorphic.BlockShapeConstantTermIdeleOrbit
import Langlands.Automorphic.CuspidalBlockTermSource
import Langlands.Global.HeckeCharacter

/-! # Continuous Hecke characters from the selected block term -/

noncomputable section

universe u

open NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear

section Cyclic

variable {R A V : Type*} [Monoid R] [Monoid A] [AddCommGroup V] [Module ℂ V]

/-- Existence of a cyclic subspace carrying a character and a given simple quotient. -/
def HasCentralCyclicQuotient (repr : Representation ℂ R V) (σ₀ : Representation ℂ A V) (W₀ : Type*)
    [AddCommGroup W₀] [Module (MonoidAlgebra ℂ R) W₀] : Prop :=
  ∃ (v : repr.asModule) (χ : A →* ℂˣ) (p : (MonoidAlgebra ℂ R ∙ v) →ₗ[MonoidAlgebra ℂ R] W₀),
    Function.Surjective p ∧ ∀ z : A, σ₀ z v = (χ z : ℂ) • v

end Cyclic

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : OperatorRealization F n)

local instance blockTermCharacterRationalAddCommGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance blockTermCharacterContinuousAddCommGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance blockTermCharacterFiniteSmoothAddCommGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance blockTermCharacterFormsAddCommGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance blockTermCharacterStableAddCommGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance blockTermCharacterRealizationAddCommGroup : AddCommGroup S.Space := Submodule.addCommGroup _

local notation "G" => AdelicGL F n
local notation "Cen" => (Fin B.length → Ideles F)
local notation "U" => automorphicOperatorAlgebra F n
local notation "𝓡" => MonoidAlgebra ℂ (automorphicOperatorAlgebra F n)
local notation "V" => FiniteSmoothRationalFunctions F n
local notation "β" => blockConstantTermScalarAction F B
local notation "φ" => realizedBlockConstantTerm F B S
local notation "E" => translatedFunctionSum β φ
local notation "ev" => translatedFunctionEmbedding β φ
local notation "σ" => translatedFunctionAction β φ
local notation "T" => TranslatedBlockConstantTerms F B S
local notation "Γ" => AlgHom.toMonoidHom' (translatedBlockTermOperatorAction F B S)

set_option maxHeartbeats 500000 in
/-- The actual translated block term acquires a character-eigenvector while
preserving the same simple quotient. -/
theorem exists_translatedBlockTerm_centralCyclicQuotient {W : Type u}
    [AddCommGroup W] [Module 𝓡 W] [IsSimpleModule 𝓡 W]
    (q : S.representation.asModule →ₗ[𝓡] W) (hq : Function.Surjective q)
    (hker : ∀ v : S.representation.asModule, φ v = 0 → q v = 0) :
    HasCentralCyclicQuotient Γ σ W := by
  let ρ := S.operatorAction
  have hs : ∀ (a : U) (v : Cen →₀ S.Space), v ∈ LinearMap.ker E →
      finsuppCoefficientEnd Cen S.Space (ρ a) v ∈ LinearMap.ker E := by
    intro a v hv
    change blockTermCoefficientAction F B S a v ∈ LinearMap.ker E
    exact blockTermCoefficient_kernel_stable F B S a v hv
  have hf (f : S.Space) : FiniteVectors.IsFiniteVector β (φ f) :=
    blockShapeConstantTerm_isFiniteVector F B (S.formInclusion f)
  unfold translatedBlockTermOperatorAction
  let q₀ : Representation.asModule (AlgHom.toMonoidHom' ρ) →ₗ[𝓡] W := q
  let : Ring U := Subalgebra.toRing U
  exact exists_translatedFunction_centralCyclicQuotient (R := U) β φ ρ hs hf q₀ hq hker

private theorem continuous_blockTerm (f : V) : Continuous (blockShapeConstantTerm B F f) :=
  (GroupSchemeFunctions.continuous_normalizedBlockConstantTerm F (standardBlockWeight B.cuts)
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm f.val)).comp
      (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.continuous

set_option maxHeartbeats 500000 in
/-- Every element of the translated period space evaluates to a continuous function. -/
theorem continuous_translatedBlockTerm (v : T) : Continuous (ev v) := by
  obtain ⟨w, rfl⟩ := (LinearMap.ker E).mkQ_surjective v
  change Continuous (E w)
  induction w using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact continuous_const
  | add a b ha hb => rw [map_add]; exact ha.add hb
  | single z f =>
    rw [translatedFunctionSum_single]
    exact (continuous_blockTerm F B (S.ambient f)).comp (continuous_const.mul continuous_id)

private theorem blockTerm_principal (f : S.Space) (a : Fin B.length → Fˣ) :
    β (fun i => diagonalUnits F (a i)) (φ f) = φ f := by
  funext g
  let q : B.Levi F := fun i => Matrix.GeneralLinearGroup.scalar (Fin (B.size i)) (a i)
  have hq : (blockLeviScalars F B (fun i => diagonalUnits F (a i))) =
      fun i => AdelicGL.rational F (B.size i) (q i) :=
    funext fun i => AdelicGL.scalar_diagonalUnits F (B.size i) (a i)
  have h := blockShapeLeviSlice_rational_mul B F (S.ambient f) g q 1
  rw [← hq, mul_one] at h
  change blockShapeConstantTerm B F (S.ambient f)
    (B.leviEmbedding (Adeles F) (blockLeviScalars F B (fun i => diagonalUnits F (a i))) * g) =
      blockShapeConstantTerm B F (S.ambient f) g
  simpa only [blockShapeLeviSlice, map_one, one_mul] using h

private theorem translatedFunction_fixed {A X W : Type*} [CommGroup A] [AddCommGroup W] [Module ℂ W]
    (B₀ : Representation ℂ A (X → ℂ)) (C₀ : W →ₗ[ℂ] (X → ℂ))
    (z : A) (hz : ∀ w, B₀ z (C₀ w) = C₀ w) (v : TranslatedFunctionSpan B₀ C₀) :
    B₀ z (translatedFunctionEmbedding B₀ C₀ v) = translatedFunctionEmbedding B₀ C₀ v := by
  let E₀ := translatedFunctionSum B₀ C₀
  obtain ⟨w, rfl⟩ := (LinearMap.ker E₀).mkQ_surjective v
  change B₀ z (E₀ w) = E₀ w
  induction w using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add b c hb hc => simp only [map_add, hb, hc]
  | single b f =>
    rw [show E₀ (Finsupp.single b f) = B₀ b (C₀ f) from translatedFunctionSum_single B₀ C₀ b f,
      ← Module.End.mul_apply, ← map_mul, mul_comm z b, map_mul, Module.End.mul_apply, hz]

private theorem translatedBlockTerm_principal (v : T) (a : Fin B.length → Fˣ) :
    β (fun i => diagonalUnits F (a i)) (ev v) = ev v :=
  translatedFunction_fixed β φ _ (fun f => blockTerm_principal F B S f a) v

private theorem continuous_character_of_function {A X P : Type*} [Monoid A] [TopologicalSpace A]
    (α₀ : Representation ℂ A (X → ℂ)) (f : X → ℂ) (hf : f ≠ 0)
    (χ : A →* ℂˣ) (hχ : ∀ z : A, α₀ z f = (χ z : ℂ) • f)
    (hc : ∀ x, Continuous fun z : A => α₀ z f x)
    (j : P → A) (hj : ∀ a, α₀ (j a) f = f) :
    Continuous χ ∧ ∀ a, χ (j a) = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hf (funext h)
  have hval (z : A) : α₀ z f x = (χ z : ℂ) * f x := congrFun (hχ z) x
  constructor
  · apply Units.isEmbedding_val₀.continuous_iff.mpr
    change Continuous (fun z : A => (χ z : ℂ))
    rw [show (fun z : A => (χ z : ℂ)) = fun z => α₀ z f x / f x from
      funext fun z => (eq_div_iff hx).mpr (hval z).symm]
    exact (hc x).div_const (f x)
  · intro a
    apply Units.ext
    apply mul_right_cancel₀ hx
    change (χ (j a) : ℂ) * f x = 1 * f x
    rw [← hval, one_mul]
    exact congrFun (hj a) x

set_option maxHeartbeats 600000 in
/-- A nonzero block term with an algebraic central character determines a continuous
character, trivial on every tuple of principal ideles. -/
theorem continuous_character_of_translatedBlockTerm_eigenvector (v : T) (hv : v ≠ 0)
    (χ : Cen →* ℂˣ) (hχ : ∀ z : Cen, σ z v = (χ z : ℂ) • v) :
    Continuous χ ∧ ∀ a : Fin B.length → Fˣ, χ (fun i => diagonalUnits F (a i)) = 1 := by
  let f := ev v
  have hv' : f ≠ 0 := fun h => hv ((translatedFunctionEmbedding_injective β φ) (h.trans ((ev).map_zero).symm))
  have he (z : Cen) : β z (ev v) = (χ z : ℂ) • ev v := by
    calc
      _ = ev (σ z v) := (translatedFunctionEmbedding_action β φ z v).symm
      _ = ev ((χ z : ℂ) • v) := congrArg (ev) (hχ z)
      _ = _ := (ev).map_smul _ _
  have hcont (g : G) : Continuous (fun z : Cen => β z f g) := by
    change Continuous (fun z : Cen => f (B.leviEmbedding (Adeles F) (blockLeviScalars F B z) * g))
    exact (continuous_translatedBlockTerm F B S v).comp
      (((B.leviEmbeddingContinuous (Adeles F)).continuous.comp (blockLeviScalars F B).continuous).mul_const g)
  exact continuous_character_of_function β f hv' χ he hcont
    (fun (a : Fin B.length → Fˣ) i => diagonalUnits F (a i))
    (fun a => translatedBlockTerm_principal F B S v a)

variable {S}

/-- Restrict the character of the product centre to one block and descend it to its idele classes. -/
def blockTermHeckeCharacter (χ : Cen →ₜ* ℂˣ)
    (hχ : ∀ a : Fin B.length → Fˣ, χ (fun i => diagonalUnits F (a i)) = 1)
    (i : Fin B.length) : HeckeCharacter F :=
  let j : Ideles F →ₜ* Cen :=
    { toMonoidHom := MonoidHom.mulSingle (fun _ : Fin B.length => Ideles F) i
      continuous_toFun := continuous_mulSingle (A := fun _ : Fin B.length => Ideles F) i }
  HeckeCharacter.ofIdeleCharacter (χ.comp j) (fun a => by
    change χ (Pi.mulSingle i (diagonalUnits F a)) = 1
    have he : (Pi.mulSingle i (diagonalUnits F a) : Cen) =
        fun j => diagonalUnits F ((Pi.mulSingle i a : Fin B.length → Fˣ) j) := by
      funext j
      by_cases hj : j = i
      · subst j; simp only [Pi.mulSingle_eq_same]
      · simp only [Pi.mulSingle_eq_of_ne hj, map_one]
    rw [he]
    exact hχ _)

@[simp]
theorem blockTermHeckeCharacter_onIdeles (χ : Cen →ₜ* ℂˣ)
    (hχ : ∀ a : Fin B.length → Fˣ, χ (fun i => diagonalUnits F (a i)) = 1)
    (i : Fin B.length) (z : Ideles F) :
    (blockTermHeckeCharacter F B χ hχ i).onIdeles z = χ (Pi.mulSingle i z) := rfl

end Langlands.Automorphic
