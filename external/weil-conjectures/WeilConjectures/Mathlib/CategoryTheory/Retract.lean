/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Retracts as cokernels; matching invariant summands

In a preadditive category, a retract `X` of `Y` is the cokernel of the idempotent endomorphism
`𝟙 Y - r ≫ i` of `Y` (`CategoryTheory.Retract.isoCokernel`).

Two split monomorphisms onto "invariant summands" which are matched by an equivariant
isomorphism have isomorphic sources (`CategoryTheory.isIso_of_comp_eq_comp_of_coinvariant`), and
a retraction of a unit transports along functors together with its invariant-projector property
(`CategoryTheory.retraction_of_eq_comp_map_comp_of_coinvariant`).

A retract of a split monomorphism, for instance a morphism isomorphic to it as an arrow, is a
split monomorphism
(`CategoryTheory.RetractArrow.isSplitMono`, `CategoryTheory.Arrow.isSplitMono_of_iso`).
-/

@[expose] public section

namespace CategoryTheory.Retract

open Limits

variable {C : Type*} [Category* C] [Preadditive C] {X Y : C}

/-- A retract `X` of `Y` (with `i : X ⟶ Y`, `r : Y ⟶ X`, `i ≫ r = 𝟙 X`) is the cokernel of the
idempotent endomorphism `𝟙 Y - r ≫ i` of `Y`: the isomorphism is `i ≫ π`, and its inverse
is induced by `r`, which kills `𝟙 Y - r ≫ i`.
```
         𝟙 Y - r ≫ i         π
    Y ─────────────────▶ Y ─────▶ cokernel (𝟙 Y - r ≫ i)
                         │              │
                       r │              │ cokernel.desc r
                         ▼              ▼
                         X ════════════ X
```
-/
noncomputable def isoCokernel (e : Retract X Y) [HasCokernel (𝟙 Y - e.r ≫ e.i)] :
    X ≅ cokernel (𝟙 Y - e.r ≫ e.i) where
  hom := e.i ≫ cokernel.π _
  inv := cokernel.desc _ e.r (by simp [Preadditive.sub_comp])
  hom_inv_id := by simp
  inv_hom_id := by
    ext
    have h := cokernel.condition (𝟙 Y - e.r ≫ e.i)
    rw [Preadditive.sub_comp, sub_eq_zero] at h
    simpa using h.symm

end CategoryTheory.Retract

namespace CategoryTheory

/-- **Matching two invariant summands.** Let `a₁ : A₁ ⟶ B₁` and `a₂ : A₂ ⟶ B₂` be split
monomorphisms with retractions `r₁`, `r₂`, let `β : B₁ ⟶ B₂` be an isomorphism and `α : A₁ ⟶ A₂`
with `α ≫ a₂ = a₁ ≫ β`. Let `ρ₁`, `ρ₂` be families of endomorphisms of `B₁`, `B₂` such that `β`
carries every `ρ₁ i` to some `ρ₂ i₂`, and such that `ρ₂ i₂ ≫ (r₂ ≫ a₂) = r₂ ≫ a₂`. If, for a
jointly conservative family of functors `H q`, every map out of `H q B₁` invariant under the
`H q (ρ₁ i)` is fixed by `H q (r₁ ≫ a₁)`, then `α` is an isomorphism.

(Think of `a₁`, `a₂` as the inclusions of the invariants of two group actions, and of `β` as an
equivariant isomorphism along a surjective group homomorphism.)
```
A₁ ──α──→ A₂
│a₁       │a₂
↓         ↓
B₁ ──β──→ B₂
```
-/
lemma isIso_of_comp_eq_comp_of_coinvariant {D : Type*} [Category D] {ι : Type*}
    {A : ι → Type*} [∀ q, Category (A q)] (H : ∀ q, D ⥤ A q)
    (hcons : ∀ {X Y : D} (g : X ⟶ Y), (∀ q, IsIso ((H q).map g)) → IsIso g)
    {A₁ A₂ B₁ B₂ : D} (α : A₁ ⟶ A₂) (a₁ : A₁ ⟶ B₁) (r₁ : B₁ ⟶ A₁) (ha₁ : a₁ ≫ r₁ = 𝟙 _)
    (a₂ : A₂ ⟶ B₂) (r₂ : B₂ ⟶ A₂) (ha₂ : a₂ ≫ r₂ = 𝟙 _) (β : B₁ ⟶ B₂) [IsIso β]
    (hsq : α ≫ a₂ = a₁ ≫ β) {κ₁ κ₂ : Type*} (ρ₁ : κ₁ → (B₁ ⟶ B₁)) (ρ₂ : κ₂ → (B₂ ⟶ B₂))
    (hβ : ∀ i, ∃ i₂, ρ₁ i ≫ β = β ≫ ρ₂ i₂) (he₂ : ∀ i₂, ρ₂ i₂ ≫ r₂ ≫ a₂ = r₂ ≫ a₂)
    (he₁ : ∀ q {W : A q} (φ : (H q).obj B₁ ⟶ W), (∀ i, (H q).map (ρ₁ i) ≫ φ = φ) →
      (H q).map (r₁ ≫ a₁) ≫ φ = φ) :
    IsIso α := by
  refine hcons α fun q ↦ ?_
  -- `β ≫ e₂` is invariant under the `ρ₁ i`, hence fixed by `e₁ = r₁ ≫ a₁`
  have hfix : (H q).map (r₁ ≫ a₁) ≫ (H q).map (β ≫ r₂ ≫ a₂) = (H q).map (β ≫ r₂ ≫ a₂) := by
    refine he₁ q _ fun i ↦ ?_
    obtain ⟨i₂, hi⟩ := hβ i
    rw [← Functor.map_comp, reassoc_of% hi, he₂]
  have hfix' : r₁ ≫ α = r₁ ≫ a₁ ≫ β ≫ r₂ := by
    rw [← reassoc_of% hsq, ha₂, Category.comp_id]
  refine ⟨⟨(H q).map (a₂ ≫ inv β ≫ r₁), ?_, ?_⟩⟩
  · rw [← Functor.map_comp, ← Functor.map_id]
    congr 1
    rw [reassoc_of% hsq, IsIso.hom_inv_id_assoc, ha₁]
  · have k : β ≫ r₂ = (β ≫ r₂ ≫ a₂) ≫ r₂ := by
      rw [Category.assoc, Category.assoc, ha₂, Category.comp_id]
    have h₁ : (H q).map (r₁ ≫ α) = (H q).map (β ≫ r₂) := by
      calc (H q).map (r₁ ≫ α) = (H q).map ((r₁ ≫ a₁) ≫ (β ≫ r₂ ≫ a₂) ≫ r₂) := by
            rw [hfix', ← k, Category.assoc]
        _ = (H q).map (r₁ ≫ a₁) ≫ (H q).map (β ≫ r₂ ≫ a₂) ≫ (H q).map r₂ := by
            rw [Functor.map_comp (H q) (r₁ ≫ a₁), Functor.map_comp (H q) (β ≫ r₂ ≫ a₂)]
        _ = (H q).map (β ≫ r₂) := by
            rw [reassoc_of% hfix, ← Functor.map_comp, ← k]
    rw [← Functor.map_comp, Category.assoc, Category.assoc, Functor.map_comp (H q) a₂,
      Functor.map_comp (H q) (inv β), h₁, ← Functor.map_comp, ← Functor.map_comp,
      IsIso.inv_hom_id_assoc, ha₂, Functor.map_id]

/-- **Transporting a retraction of a unit along two functors, with its invariant-projector
property.** Let `α = i ≫ F₂ (F₁ η ≫ c)` for an isomorphism `i`, functors `F₁`, `F₂` and `c` with
`F₂ c = κ` an isomorphism, and let `R` be a retraction of `η`. Then `r = κ⁻¹ ≫ F₂ (F₁ R) ≫ i⁻¹` is
a retraction of `α`, and if `G (F₂ (F₁ (R ≫ η)))` fixes every map invariant under the
`G (F₂ (F₁ (u σ)))`, then `G (r ≫ α)` fixes every map invariant under the
`ρ σ = κ⁻¹ ≫ F₂ (F₁ (u σ)) ≫ κ`. -/
lemma retraction_of_eq_comp_map_comp_of_coinvariant {C D E A : Type*} [Category C]
    [Category D] [Category E] [Category A] (F₁ : C ⥤ D) (F₂ : D ⥤ E) (G : E ⥤ A) {A₀ T : C}
    {W : D} {P : E} (α : P ⟶ F₂.obj W) (i : P ≅ F₂.obj (F₁.obj A₀)) (c : F₁.obj T ⟶ W)
    (κ : F₂.obj (F₁.obj T) ≅ F₂.obj W) (hκ : κ.hom = F₂.map c) (η : A₀ ⟶ T) (R : T ⟶ A₀)
    (hα : α = i.hom ≫ F₂.map (F₁.map η ≫ c)) (hR : η ≫ R = 𝟙 A₀) {ι : Type*}
    (u : ι → (T ⟶ T)) (ρ : ι → (F₂.obj W ⟶ F₂.obj W))
    (hρ : ∀ σ, ρ σ = κ.inv ≫ F₂.map (F₁.map (u σ)) ≫ κ.hom) :
    α ≫ (κ.inv ≫ F₂.map (F₁.map R) ≫ i.inv) = 𝟙 P ∧
      ∀ {B : A} (φ : G.obj (F₂.obj W) ⟶ B),
        (∀ φ' : G.obj (F₂.obj (F₁.obj T)) ⟶ B,
          (∀ σ, G.map (F₂.map (F₁.map (u σ))) ≫ φ' = φ') →
            G.map (F₂.map (F₁.map (R ≫ η))) ≫ φ' = φ') →
        (∀ σ, G.map (ρ σ) ≫ φ = φ) →
        G.map ((κ.inv ≫ F₂.map (F₁.map R) ≫ i.inv) ≫ α) ≫ φ = φ := by
  rw [F₂.map_comp, ← hκ] at hα
  have he : (κ.inv ≫ F₂.map (F₁.map R) ≫ i.inv) ≫ α =
      κ.inv ≫ F₂.map (F₁.map (R ≫ η)) ≫ κ.hom := by
    rw [hα]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, F₁.map_comp, F₂.map_comp]
  refine ⟨?_, ?_⟩
  · rw [hα]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F₂.map_comp_assoc, ← F₁.map_comp, hR, F₁.map_id, F₂.map_id, Category.id_comp,
      Iso.hom_inv_id]
  · intro B φ hRco hφ
    have key := hRco (G.map κ.hom ≫ φ) fun σ ↦ by
      have h := hφ σ
      rw [hρ σ, G.map_comp, G.map_comp] at h
      simp only [Category.assoc] at h
      calc _ = G.map κ.hom ≫ (G.map κ.inv ≫ G.map (F₂.map (F₁.map (u σ))) ≫ G.map κ.hom ≫ φ) := by
            rw [← G.map_comp_assoc κ.hom κ.inv, κ.hom_inv_id, G.map_id, Category.id_comp]
        _ = _ := by rw [h]
    rw [he, G.map_comp, G.map_comp, Category.assoc, Category.assoc, key, ← G.map_comp_assoc,
      Iso.inv_hom_id, G.map_id, Category.id_comp]

end CategoryTheory

namespace CategoryTheory.RetractArrow

variable {C : Type*} [Category* C] {X Y Z W : C} {f : X ⟶ Y} {g : Z ⟶ W}

/-- A retract of a split monomorphism is a split monomorphism: if `f` is a retract of `g`, then
`h.i.right ≫ retraction g ≫ h.r.left` is a retraction of `f`. -/
lemma isSplitMono (h : RetractArrow f g) [IsSplitMono g] : IsSplitMono f :=
  IsSplitMono.mk' ⟨h.i.right ≫ retraction g ≫ h.r.left, by
    rw [← h.i_w_assoc, IsSplitMono.id_assoc, h.retract_left]⟩

end CategoryTheory.RetractArrow

/-- A morphism isomorphic, as an arrow, to a split monomorphism is a split monomorphism. -/
lemma CategoryTheory.Arrow.isSplitMono_of_iso {C : Type*} [Category* C] {X Y X' Y' : C}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g) [IsSplitMono g] : IsSplitMono f :=
  RetractArrow.isSplitMono (Retract.ofIso e)
