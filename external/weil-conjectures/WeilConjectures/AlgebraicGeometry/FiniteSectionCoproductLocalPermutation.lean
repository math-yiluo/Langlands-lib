/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Local permutations between finite coproducts of sections

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-section-coproduct-local-permutation)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Two finite coproduct presentations by sections agree near each point up to a permutation.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-section-coproduct-local-permutation)

Proof. A coproduct presentation of a scheme induces a disjoint open partition of its
underlying space. In the fibre of `p` over `z`, the first presentation identifies the
points with `J₁`: every point belongs to a unique sheet, and the equation `s₁ j ≫ p = 𝟙 S`
identifies that point with `s₁ j z`. The second presentation similarly identifies this
fibre with `J₂`. Composing these bijections gives `e`. For each `j`, take the inverse
image under `s₁ j` of the open image of `s₂ (e j)`. It contains `z`. Intersect these
finitely many opens to obtain `U`. On `U`, `U.ι ≫ s₁ j` factors through the open
immersion `s₂ (e j)`. Composing this factorization with `p` shows that the factor is
`U.ι`, since both maps are sections of `p`. Thus the displayed morphisms are equal.
If one index set is empty and `z` exists, its coproduct presentation is impossible;
if both are empty there is likewise no point `z`. No choice of a point is needed on
an empty scheme, so the statement covers all empty cases. -/
theorem finiteSectionCoproduct_local_permutation (S P : Scheme.{u}) (p : P ⟶ S)
    (J₁ J₂ : Type u) [Finite J₁] [Finite J₂]
    (s₁ : J₁ → (S ⟶ P)) (s₂ : J₂ → (S ⟶ P))
    (hc₁ : IsColimit (Cofan.mk P s₁)) (hc₂ : IsColimit (Cofan.mk P s₂))
    (h₁ : ∀ j, s₁ j ≫ p = 𝟙 S) (h₂ : ∀ j, s₂ j ≫ p = 𝟙 S) (z : S) :
    ∃ (U : S.Opens), z ∈ U ∧ ∃ e : J₁ ≃ J₂,
      ∀ j, U.ι ≫ s₁ j = U.ι ≫ s₂ (e j) := by
  classical
  let q₁ := (coproductIsCoproduct (fun _ : J₁ ↦ S)).coconePointUniqueUpToIso hc₁
  let q₂ := (coproductIsCoproduct (fun _ : J₂ ↦ S)).coconePointUniqueUpToIso hc₂
  have hq₁ (j : J₁) : Sigma.ι (fun _ : J₁ ↦ S) j ≫ q₁.hom = s₁ j := by
    exact (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hc₁ ⟨j⟩
  have hq₂ (j : J₂) : Sigma.ι (fun _ : J₂ ↦ S) j ≫ q₂.hom = s₂ j := by
    exact (coproductIsCoproduct _).comp_coconePointUniqueUpToIso_hom hc₂ ⟨j⟩
  let a₁ := (sigmaMk (fun _ : J₁ ↦ S)).trans q₁.hom.homeomorph
  let a₂ := (sigmaMk (fun _ : J₂ ↦ S)).trans q₂.hom.homeomorph
  have ha₁ (j : J₁) (x : S) : a₁ ⟨j, x⟩ = s₁ j x := by
    dsimp [a₁]
    rw [sigmaMk_mk]
    exact congrArg (fun k : S ⟶ P ↦ k x) (hq₁ j)
  have ha₂ (j : J₂) (x : S) : a₂ ⟨j, x⟩ = s₂ j x := by
    dsimp [a₂]
    rw [sigmaMk_mk]
    exact congrArg (fun k : S ⟶ P ↦ k x) (hq₂ j)
  have hp₁ (j : J₁) (x : S) : p (s₁ j x) = x := by
    simpa using congrArg (fun k : S ⟶ S ↦ k x) (h₁ j)
  have hp₂ (j : J₂) (x : S) : p (s₂ j x) = x := by
    simpa using congrArg (fun k : S ⟶ S ↦ k x) (h₂ j)
  let r₁ : J₁ → J₂ := fun j ↦ (a₂.symm (s₁ j z)).1
  let r₂ : J₂ → J₁ := fun j ↦ (a₁.symm (s₂ j z)).1
  have ha₁' (v : Σ _ : J₁, S) : a₁ v = s₁ v.1 v.2 := by
    cases v
    exact ha₁ _ _
  have ha₂' (v : Σ _ : J₂, S) : a₂ v = s₂ v.1 v.2 := by
    cases v
    exact ha₂ _ _
  have hr₁ (j : J₁) : s₂ (r₁ j) z = s₁ j z := by
    have heq := a₂.apply_symm_apply (s₁ j z)
    rw [ha₂'] at heq
    have hx : (a₂.symm (s₁ j z)).2 = z := by
      simpa only [hp₁, hp₂] using congrArg p heq
    simpa only [hx] using heq
  have hr₂ (j : J₂) : s₁ (r₂ j) z = s₂ j z := by
    have heq := a₁.apply_symm_apply (s₂ j z)
    rw [ha₁'] at heq
    have hx : (a₁.symm (s₂ j z)).2 = z := by
      simpa only [hp₁, hp₂] using congrArg p heq
    simpa only [hx] using heq
  have hinj₁ : Function.Injective (fun j ↦ s₁ j z) := by
    intro j k h
    exact congrArg Sigma.fst (a₁.injective ((ha₁ j z).trans (h.trans (ha₁ k z).symm)))
  have hinj₂ : Function.Injective (fun j ↦ s₂ j z) := by
    intro j k h
    exact congrArg Sigma.fst (a₂.injective ((ha₂ j z).trans (h.trans (ha₂ k z).symm)))
  let e : J₁ ≃ J₂ :=
    { toFun := r₁
      invFun := r₂
      left_inv := fun j ↦ hinj₁ ((hr₂ (r₁ j)).trans (hr₁ j))
      right_inv := fun j ↦ hinj₂ ((hr₁ (r₂ j)).trans (hr₂ j)) }
  have hi₂ (j : J₂) : IsOpenImmersion (s₂ j) := by
    rw [← hq₂ j]
    infer_instance
  let _ (j : J₂) := hi₂ j
  let U : S.Opens := ⨅ j, (s₁ j) ⁻¹ᵁ (s₂ (e j)).opensRange
  refine ⟨U, ?_, e, ?_⟩
  · change z ∈ (U : Set S)
    simp only [U, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    intro j
    exact ⟨z, hr₁ j⟩
  · intro j
    have hU : Set.range (U.ι ≫ s₁ j) ⊆ Set.range (s₂ (e j)) := by
      rintro _ ⟨x, rfl⟩
      have hx : x.1 ∈ (s₁ j) ⁻¹ᵁ (s₂ (e j)).opensRange := IsConcreteLE.le_iff.mp (iInf_le _ j) x.2
      exact hx
    let l := IsOpenImmersion.lift (s₂ (e j)) (U.ι ≫ s₁ j) hU
    have hl : l ≫ s₂ (e j) = U.ι ≫ s₁ j := IsOpenImmersion.lift_fac _ _ hU
    have hl' : l = U.ι := by
      simpa [Category.assoc, h₁, h₂] using congrArg (fun k ↦ k ≫ p) hl
    rw [← hl, hl']


end AlgebraicGeometry
