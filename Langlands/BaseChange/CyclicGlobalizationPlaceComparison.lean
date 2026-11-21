import Langlands.Global.AdelicFunctoriality.CompletedTensorComparisonProof
import Langlands.Global.AdelicFunctoriality.UniquePlaceCompletion
import Langlands.TraceFormula.CyclicFieldGlobalizationStatement
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-! # Completing the split and field tensors of cyclic globalization -/

noncomputable section

set_option autoImplicit false

universe u v uE

namespace Langlands.BaseChange

open Global Global.AdelicFunctoriality IsDedekindDomain
open scoped NumberField FiniteExtension TensorProduct BigOperators

variable {K : Type u} {L : Type v} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (p : FinitePlace K)

private def tensorCompletionProduct :
    p.adicCompletion K ⊗[K] L ≃ₐ[p.adicCompletion K]
      (∀ w : FinitePlacesAbove L p, w.1.adicCompletion L) :=
  AlgEquiv.ofBijective (finiteTensorMap p) (completedTensorComparison K L |>.1 p)

/-- A local tensor that is isomorphic to a field has one place over `p`. -/
theorem subsingleton_finitePlacesAbove_of_tensorField
    {E : Type uE} [Field E] (e : p.adicCompletion K ⊗[K] L ≃+* E) :
    Subsingleton (FinitePlacesAbove L p) := by
  classical
  let f := (tensorCompletionProduct (L := L) p).symm.toRingEquiv.trans e
  refine ⟨fun w w' => ?_⟩
  by_contra h
  let a : ∀ z : FinitePlacesAbove L p, z.1.adicCompletion L := Pi.single w 1
  have ha : a ≠ 0 := by
    intro he
    have he' := congrFun he w
    simp [a] at he'
  have hb : 1 - a ≠ 0 := by
    intro he
    have he' := congrFun he w'
    have h' : w' ≠ w := fun h' => h h'.symm
    simp [a, Pi.single_eq_of_ne h'] at he'
  have hab : a * (1 - a) = 0 := by
    funext z
    by_cases hz : z = w
    · subst z
      simp [a]
    · simp [a, Pi.single_eq_of_ne hz]
  have hmul : f a * f (1 - a) = 0 := by rw [← map_mul, hab, map_zero]
  rcases mul_eq_zero.mp hmul with hf | hf
  · exact ha (f.injective (hf.trans f.map_zero.symm))
  · exact hb (f.injective (hf.trans f.map_zero.symm))

/-- At a single place above `p`, identify the actual tensor with its completion.
The homomorphism is the projection of the canonical completed tensor map. -/
def tensorUniqueCompletion (w : FinitePlacesAbove L p) (hw : ∀ w' : FinitePlacesAbove L p, w' = w) :
    p.adicCompletion K ⊗[K] L ≃ₐ[p.adicCompletion K] w.1.adicCompletion L := by
  let : Unique (FinitePlacesAbove L p) := ⟨⟨w⟩, hw⟩
  let e : (∀ w' : FinitePlacesAbove L p, w'.1.adicCompletion L) ≃ₐ[p.adicCompletion K]
      w.1.adicCompletion L :=
    { __ := RingEquiv.piUnique (fun w' : FinitePlacesAbove L p => w'.1.adicCompletion L)
      commutes' := fun _ => rfl }
  exact (tensorCompletionProduct p).trans e

@[simp] theorem tensorUniqueCompletion_tmul (w : FinitePlacesAbove L p)
    (hw : ∀ w' : FinitePlacesAbove L p, w' = w) (a : p.adicCompletion K) (b : L) :
    tensorUniqueCompletion p w hw (a ⊗ₜ[K] b) =
      algebraMap (p.adicCompletion K) (w.1.adicCompletion L) a *
        algebraMap L (w.1.adicCompletion L) b :=
  finiteTensorMap_tmul p a b w

private theorem completion_isModuleTopology (w : FinitePlacesAbove L p) :
    IsModuleTopology (p.adicCompletion K) (w.1.adicCompletion L) := by
  let : NontriviallyNormedField (p.adicCompletion K) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  exact isModuleTopologyOfFiniteDimensional

/-- The unique-place identification is bicontinuous for the tensor module topology. -/
theorem tensorUniqueCompletion_bicontinuous (w : FinitePlacesAbove L p)
    (hw : ∀ w' : FinitePlacesAbove L p, w' = w) :
    letI := moduleTopology (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
    Continuous (tensorUniqueCompletion p w hw) ∧ Continuous (tensorUniqueCompletion p w hw).symm := by
  let := moduleTopology (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
  let := completion_isModuleTopology p w
  let := ModuleTopology.continuousAdd (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
  let := ModuleTopology.continuousSMul (p.adicCompletion K) (p.adicCompletion K ⊗[K] L)
  exact ⟨IsModuleTopology.continuous_of_linearMap (tensorUniqueCompletion p w hw).toLinearMap,
    IsModuleTopology.continuous_of_linearMap (tensorUniqueCompletion p w hw).symm.toLinearMap⟩

/-- The identification at the unique place intertwines `id ⊗ σ` and the actual
extension of `σ` to that completion. -/
theorem tensorUniqueCompletion_congr [IsGalois K L] (w : FinitePlacesAbove L p)
    (hw : ∀ w' : FinitePlacesAbove L p, w' = w) (σ : L ≃ₐ[K] L)
    (x : p.adicCompletion K ⊗[K] L) :
    tensorUniqueCompletion p w hw
      (Algebra.TensorProduct.congr (AlgEquiv.refl : p.adicCompletion K ≃ₐ[K] _) σ x) =
      uniquePlaceCompletionAutEquiv w hw σ (tensorUniqueCompletion p w hw x) := by
  let : w.1.asIdeal.LiesOver p.asIdeal := w.2
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    change tensorUniqueCompletion p w hw (a ⊗ₜ[K] σ b) =
      uniquePlaceCompletionAutEquiv w hw σ (tensorUniqueCompletion p w hw (a ⊗ₜ[K] b))
    rw [tensorUniqueCompletion_tmul, tensorUniqueCompletion_tmul, map_mul,
      AlgEquiv.commutes, uniquePlaceCompletionAutEquiv_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb]

private theorem surjective_algebraMap_of_split_product {A B : Type*} [Field A] [Field B] [Algebra A B]
    {l : ℕ} (f : (Fin l → A) →ₐ[A] B) (hf : Function.Surjective f) :
    Function.Surjective (algebraMap A B) := by
  classical
  let δ (i : Fin l) : Fin l → A := Pi.single i 1
  have hsum : (∑ i, δ i) = 1 := by
    funext i
    simp [δ, Finset.sum_apply, Pi.single_apply]
  obtain ⟨i, hi⟩ : ∃ i, f (δ i) ≠ 0 := by
    by_contra! h
    have he := congrArg f hsum
    exact zero_ne_one (by simpa only [map_sum, h, Finset.sum_const_zero, map_one] using he)
  have hid : δ i * δ i = δ i := by
    funext j
    by_cases h : j = i
    · subst j
      simp [δ]
    · simp [δ, Pi.single_eq_of_ne h]
  have hfi : f (δ i) = 1 := mul_left_cancel₀ hi (by rw [← map_mul, hid, mul_one])
  intro y
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨x i, ?_⟩
  have hx : δ i * x = δ i * algebraMap A (Fin l → A) (x i) := by
    funext j
    by_cases h : j = i
    · subst j
      simp [δ, Pi.algebraMap_apply]
    · simp [δ, Pi.single_eq_of_ne h]
  have h := congrArg f hx
  simpa only [map_mul, hfi, one_mul, AlgHom.commutes] using h.symm

/-- If the globalization tensor is split, each actual completed inclusion is bijective. -/
theorem completionMap_bijective_of_cyclicShiftSplit (σ : L ≃ₐ[K] L) (l : ℕ)
    (hsplit : TraceFormula.IsCyclicShiftSplit K L (p.adicCompletion K) σ l)
    (w : FinitePlacesAbove L p) :
    Function.Bijective (FiniteExtension.completionMap p w.1) := by
  classical
  obtain ⟨e, -⟩ := hsplit
  let g := e.symm.trans (tensorCompletionProduct p)
  let pr := Pi.evalAlgHom (p.adicCompletion K) (fun w : FinitePlacesAbove L p => w.1.adicCompletion L) w
  let f := pr.comp g.toAlgHom
  have hp : Function.Surjective pr := by
    intro x
    let y : ∀ z : FinitePlacesAbove L p, z.1.adicCompletion L := Pi.single w x
    refine ⟨y, ?_⟩
    change y w = x
    simp [y]
  exact ⟨(FiniteExtension.completionMap p w.1).injective,
    surjective_algebraMap_of_split_product f (hp.comp g.surjective)⟩

/-- The degree-one completed scalar embedding is an isomorphism over the lower completion. -/
def degreeOneCompletionEquiv (w : FinitePlacesAbove L p)
    (h : Module.finrank (p.adicCompletion K) (w.1.adicCompletion L) = 1) :
    p.adicCompletion K ≃ₐ[p.adicCompletion K] w.1.adicCompletion L :=
  AlgEquiv.ofBijective (Algebra.ofId _ _) (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h)

theorem degreeOneCompletionEquiv_bicontinuous (w : FinitePlacesAbove L p)
    (h : Module.finrank (p.adicCompletion K) (w.1.adicCompletion L) = 1) :
    Continuous (degreeOneCompletionEquiv p w h) ∧ Continuous (degreeOneCompletionEquiv p w h).symm := by
  let := completion_isModuleTopology p w
  exact ⟨FiniteExtension.continuous_completionMap p w.1,
    IsModuleTopology.continuous_of_linearMap (degreeOneCompletionEquiv p w h).symm.toLinearMap⟩

/-- The two kinds of tensors used in cyclic globalization give the actual local place data. -/
def CyclicGlobalizationPlaceComparisonStatement : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (p : FinitePlace K) (σ : L ≃ₐ[K] L) (l : ℕ),
    (∀ (E : Type uE) [Field E], (p.adicCompletion K ⊗[K] L ≃+* E) →
      ∃ w : FinitePlacesAbove L p, ∀ w' : FinitePlacesAbove L p, w' = w) ∧
    (TraceFormula.IsCyclicShiftSplit K L (p.adicCompletion K) σ l →
      ∀ w : FinitePlacesAbove L p,
        Module.finrank (p.adicCompletion K) (w.1.adicCompletion L) = 1)

theorem cyclicGlobalizationPlaceComparison : CyclicGlobalizationPlaceComparisonStatement.{u, v, uE} := by
  intro K L _ _ _ _ _ _ p σ l
  refine ⟨fun E _ e => ?_, fun hsplit w => ?_⟩
  · let : Subsingleton (FinitePlacesAbove L p) := subsingleton_finitePlacesAbove_of_tensorField p e
    exact ⟨placeAbove L p, fun _ => Subsingleton.elim _ _⟩
  · exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
      (completionMap_bijective_of_cyclicShiftSplit p σ l hsplit w)

end Langlands.BaseChange
