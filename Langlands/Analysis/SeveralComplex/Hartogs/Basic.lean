import Langlands.Analysis.SeveralComplex.Hartogs.BaireStep
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Hartogs's theorem on separate holomorphy

A function on a product `U₁ ×ˢ U₂` of open subsets of finite-dimensional complex
normed spaces that is complex differentiable in each variable separately is
complex differentiable (`differentiableOn_prod_of_separately`). The diagonal
form `differentiableOn_diag_of_separately` is the one used in the principle of
meromorphic continuation.

The proof is an induction on the dimension of the second factor. The step
`E₁ × ℂ` is `differentiableOn_prod_complex_of_separately`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Set Filter Topology

universe u

section Transfer

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
  {E₂' : Type*} [NormedAddCommGroup E₂'] [NormedSpace ℂ E₂']

/-- Composition with a continuous linear map in the second variable. -/
theorem differentiableOn_comp_prodMap {f : E₁ × E₂ → ℂ} {U₁ : Set E₁} {U₂ : Set E₂}
    (hf : DifferentiableOn ℂ f (U₁ ×ˢ U₂)) (L : E₂' →L[ℂ] E₂) :
    DifferentiableOn ℂ (fun p : E₁ × E₂' => f (p.1, L p.2)) (U₁ ×ˢ (L ⁻¹' U₂)) := by
  have hφ : DifferentiableOn ℂ (fun p : E₁ × E₂' => (p.1, L p.2)) (U₁ ×ˢ (L ⁻¹' U₂)) :=
    (differentiable_fst.prodMk (L.differentiable.comp differentiable_snd)).differentiableOn
  exact hf.comp hφ fun p hp => ⟨hp.1, hp.2⟩

/-- Change of variables in the second factor: if `f ∘ (id × e)` is complex
differentiable on `U₁ ×ˢ e ⁻¹' U₂` for a continuous linear equivalence `e`, then
`f` is complex differentiable on `U₁ ×ˢ U₂`. -/
theorem differentiableOn_of_comp_equiv {f : E₁ × E₂ → ℂ} {U₁ : Set E₁} {U₂ : Set E₂}
    (e : E₂' ≃L[ℂ] E₂)
    (h : DifferentiableOn ℂ (fun p : E₁ × E₂' => f (p.1, e p.2)) (U₁ ×ˢ (e ⁻¹' U₂))) :
    DifferentiableOn ℂ f (U₁ ×ˢ U₂) := by
  have h' := differentiableOn_comp_prodMap h (e.symm : E₂ →L[ℂ] E₂')
  refine (h'.mono fun p hp => ⟨hp.1, ?_⟩).congr fun p _ => ?_
  · simpa using hp.2
  · simp

/-- If the second factor is a subsingleton, holomorphy in the first variable
suffices. -/
theorem differentiableOn_prod_of_subsingleton [Subsingleton E₂] {f : E₁ × E₂ → ℂ}
    {U₁ : Set E₁} {U₂ : Set E₂}
    (hf₁ : ∀ w ∈ U₂, DifferentiableOn ℂ (fun z => f (z, w)) U₁) :
    DifferentiableOn ℂ f (U₁ ×ˢ U₂) := by
  intro p hp
  have h : DifferentiableOn ℂ (fun q : E₁ × E₂ => f (q.1, p.2)) (U₁ ×ˢ U₂) :=
    (hf₁ p.2 hp.2).comp differentiableOn_fst fun q hq => hq.1
  refine (h.congr fun q _ => ?_) p hp
  rw [Subsingleton.elim p.2 q.2]

end Transfer

section Step

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

/-- The induction step. Suppose separate holomorphy implies holomorphy on products
of open sets for `E₁ × E₂` (hypothesis `IH`), and for `(E₁ × E₂) × ℂ` (hypothesis
`hA`). Then it does for `E₁ × (ℂ × E₂)`. -/
theorem differentiableOn_prod_complex_prod
    (hA : ∀ {B : Set (E₁ × E₂)} {D : Set ℂ} {g : (E₁ × E₂) × ℂ → ℂ}, IsOpen B → IsOpen D →
      (∀ t ∈ D, DifferentiableOn ℂ (fun q => g (q, t)) B) →
      (∀ q ∈ B, DifferentiableOn ℂ (fun t => g (q, t)) D) → DifferentiableOn ℂ g (B ×ˢ D))
    (IH : ∀ {U₁ : Set E₁} {U₂ : Set E₂} {f : E₁ × E₂ → ℂ}, IsOpen U₁ → IsOpen U₂ →
      (∀ w ∈ U₂, DifferentiableOn ℂ (fun z => f (z, w)) U₁) →
      (∀ z ∈ U₁, DifferentiableOn ℂ (fun w => f (z, w)) U₂) → DifferentiableOn ℂ f (U₁ ×ˢ U₂))
    {f : E₁ × (ℂ × E₂) → ℂ} {U₁ : Set E₁} {V : Set (ℂ × E₂)} (hU₁ : IsOpen U₁)
    (hV : IsOpen V) (hf₁ : ∀ w ∈ V, DifferentiableOn ℂ (fun z => f (z, w)) U₁)
    (hf₂ : ∀ z ∈ U₁, DifferentiableOn ℂ (fun w => f (z, w)) V) :
    DifferentiableOn ℂ f (U₁ ×ˢ V) := by
  intro p hp
  obtain ⟨D, B', hD, hB', ht₀, ht'₀, hDB'⟩ := isOpen_prod_iff.1 hV p.2.1 p.2.2 hp.2
  let g : (E₁ × E₂) × ℂ → ℂ := fun q => f (q.1.1, (q.2, q.1.2))
  have hg₁ : ∀ t ∈ D, DifferentiableOn ℂ (fun q => g (q, t)) (U₁ ×ˢ B') := by
    intro t ht
    refine IH hU₁ hB' (fun t' ht' => hf₁ (t, t') (hDB' ⟨ht, ht'⟩)) fun z hz => ?_
    exact (hf₂ z hz).comp ((differentiable_const t).prodMk differentiable_id).differentiableOn
      fun t' ht' => hDB' ⟨ht, ht'⟩
  have hg₂ : ∀ q ∈ U₁ ×ˢ B', DifferentiableOn ℂ (fun t => g (q, t)) D := by
    intro q hq
    exact (hf₂ q.1 hq.1).comp (differentiable_id.prodMk (differentiable_const q.2)).differentiableOn
      fun t ht => hDB' ⟨ht, hq.2⟩
  have hgd := hA (hU₁.prod hB') hD hg₁ hg₂
  have hmem : ((p.1, p.2.2), p.2.1) ∈ (U₁ ×ˢ B') ×ˢ D := ⟨⟨hp.1, ht'₀⟩, ht₀⟩
  have hφ : Differentiable ℂ (fun r : E₁ × (ℂ × E₂) => ((r.1, r.2.2), r.2.1)) := by fun_prop
  have hdiff : DifferentiableAt ℂ (g ∘ fun r : E₁ × (ℂ × E₂) => ((r.1, r.2.2), r.2.1)) p :=
    (hgd.differentiableAt (((hU₁.prod hB').prod hD).mem_nhds hmem)).comp p (hφ p)
  exact hdiff.differentiableWithinAt

end Step

/-- Hartogs's theorem for `E₁ × ℂⁿ`, by induction on `n` (with `E₁` varying),
from the case `E × ℂ` (`differentiableOn_prod_complex_of_separately`). -/
theorem differentiableOn_prod_pi_of_separately (n : ℕ) :
    ∀ {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [FiniteDimensional ℂ E₁]
      {U₁ : Set E₁} {U₂ : Set (Fin n → ℂ)} {f : E₁ × (Fin n → ℂ) → ℂ}, IsOpen U₁ → IsOpen U₂ →
      (∀ w ∈ U₂, DifferentiableOn ℂ (fun z => f (z, w)) U₁) →
      (∀ z ∈ U₁, DifferentiableOn ℂ (fun w => f (z, w)) U₂) →
      DifferentiableOn ℂ f (U₁ ×ˢ U₂) := by
  induction n with
  | zero =>
    intro E₁ _ _ _ U₁ U₂ f _ _ hf₁ _
    exact differentiableOn_prod_of_subsingleton hf₁
  | succ n IH =>
    intro E₁ _ _ _ U₁ U₂ f hU₁ hU₂ hf₁ hf₂
    let e : (ℂ × (Fin n → ℂ)) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
      (Fin.consLinearEquiv ℂ (fun _ : Fin (n + 1) => ℂ)).toContinuousLinearEquiv
    refine differentiableOn_of_comp_equiv e ?_
    have hA : ∀ {B : Set (E₁ × (Fin n → ℂ))} {D : Set ℂ} {g : (E₁ × (Fin n → ℂ)) × ℂ → ℂ},
        IsOpen B → IsOpen D → (∀ t ∈ D, DifferentiableOn ℂ (fun q => g (q, t)) B) →
        (∀ q ∈ B, DifferentiableOn ℂ (fun t => g (q, t)) D) → DifferentiableOn ℂ g (B ×ˢ D) :=
      fun hB hD h₁ h₂ => differentiableOn_prod_complex_of_separately (E₁ := E₁ × (Fin n → ℂ))
        hB hD h₁ h₂
    exact differentiableOn_prod_complex_prod hA
      (fun hU hV h₁ h₂ => IH hU hV h₁ h₂) hU₁ (hU₂.preimage e.continuous)
      (fun w hw => hf₁ (e w) hw)
      (fun z hz => (hf₂ z hz).comp e.differentiable.differentiableOn fun _ hw => hw)

/-- Hartogs's theorem on separate holomorphy for a product of open sets in two
finite-dimensional complex normed spaces. -/
theorem differentiableOn_prod_of_separately
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [FiniteDimensional ℂ E₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] [FiniteDimensional ℂ E₂]
    {U₁ : Set E₁} {U₂ : Set E₂} {f : E₁ × E₂ → ℂ} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hf₁ : ∀ w ∈ U₂, DifferentiableOn ℂ (fun z => f (z, w)) U₁)
    (hf₂ : ∀ z ∈ U₁, DifferentiableOn ℂ (fun w => f (z, w)) U₂) :
    DifferentiableOn ℂ f (U₁ ×ˢ U₂) := by
  let e : (Fin (Module.finrank ℂ E₂) → ℂ) ≃L[ℂ] E₂ :=
    (Module.finBasis ℂ E₂).equivFun.symm.toContinuousLinearEquiv
  refine differentiableOn_of_comp_equiv e ?_
  exact differentiableOn_prod_pi_of_separately _ hU₁ (hU₂.preimage e.continuous)
    (fun w hw => hf₁ (e w) hw)
    (fun z hz => (hf₂ z hz).comp e.differentiable.differentiableOn fun _ hw => hw)

/-- Hartogs's theorem in diagonal form: on an open set `U` of a
finite-dimensional complex normed space, a function `G` of two variables that is
complex differentiable on `U` in each variable separately has a complex
differentiable diagonal `s ↦ G s s`. -/
theorem differentiableOn_diag_of_separately
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {U : Set E} (hU : IsOpen U) {G : E → E → ℂ}
    (h₁ : ∀ t ∈ U, DifferentiableOn ℂ (fun s => G s t) U)
    (h₂ : ∀ s ∈ U, DifferentiableOn ℂ (G s) U) :
    DifferentiableOn ℂ (fun s => G s s) U := by
  have h := differentiableOn_prod_of_separately (f := fun p : E × E => G p.1 p.2) hU hU h₁ h₂
  exact h.comp (differentiableOn_id.prodMk differentiableOn_id) fun s hs => ⟨hs, hs⟩

end Langlands.Analysis.SeveralComplex
