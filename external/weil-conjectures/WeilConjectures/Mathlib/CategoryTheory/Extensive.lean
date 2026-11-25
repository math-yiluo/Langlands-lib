/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Extensive

/-!
# Split torsors in finitary extensive categories

Let `f : Y ⟶ X` be a morphism with a finite family of endomorphisms `σ i : Y ⟶ Y` over `X`. We
say that `f` is split by the `σ i` if the map `∐ᵢ Y ⟶ Y ×_X Y`, given on the `i`-th summand by
`(𝟙, σ i)`, is an isomorphism; this is the case for a torsor under a finite constant group.
In a finitary extensive category this splitting is stable under base change along any
`v : V ⟶ Y`: the map `∐ᵢ V ⟶ V ×_X Y`, given on the `i`-th summand by `(𝟙, v ≫ σ i)`, is again
an isomorphism, finite coproducts being universal.

## Main statements

- `CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_lift_comp`: the base change of a
  splitting.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

/-- Let `f : Y ⟶ X` and `σ i : Y ⟶ Y` be endomorphisms over `X` such that the map
`∐ᵢ Y ⟶ Y ×_X Y`, `(𝟙, σ i)` on the `i`-th summand, is an isomorphism. Then for every
`v : V ⟶ Y` the map `∐ᵢ V ⟶ V ×_X Y`, `(𝟙, v ≫ σ i)` on the `i`-th summand, is an isomorphism:
it is the base change of the former along `v × 𝟙 : V ×_X Y ⟶ Y ×_X Y`, finite coproducts being
universal:
```
  ∐ᵢ V --(𝟙, v ≫ σ i)ᵢ--> V ×_X Y --v × 𝟙--> Y ×_X Y <--(𝟙, σ i)ᵢ-- ∐ᵢ Y
                              |                  |
                             fst                fst
                              ↓                  ↓
                              V -------v-------> Y
```
where the square is cartesian. -/
lemma FinitaryPreExtensive.isIso_sigmaDesc_lift_comp [FinitaryPreExtensive C] [HasPullbacks C]
    {ι : Type*} [Finite ι] {X Y : C} (f : Y ⟶ X) (σ : ι → (Y ⟶ Y)) (hσ : ∀ i, σ i ≫ f = f)
    [HasCoproduct fun _ : ι ↦ Y]
    [IsIso (Sigma.desc fun i ↦ pullback.lift (f := f) (g := f) (𝟙 Y) (σ i) (by simp [hσ]) :
      ∐ (fun _ : ι ↦ Y) ⟶ pullback f f)]
    {V : C} (v : V ⟶ Y) [HasCoproduct fun _ : ι ↦ V] :
    IsIso (Sigma.desc fun i ↦
      pullback.lift (f := v ≫ f) (g := f) (𝟙 V) (v ≫ σ i) (by simp [hσ]) :
        ∐ (fun _ : ι ↦ V) ⟶ pullback (v ≫ f) f) := by
  let c : Cofan (fun _ : ι ↦ Y) :=
    Cofan.mk _ fun i ↦ pullback.lift (f := f) (g := f) (𝟙 Y) (σ i) (by simp [hσ])
  have : IsIso ((colimit.isColimit _).desc c) := ‹IsIso (Sigma.desc _)›
  have hc : IsColimit c := IsColimit.ofPointIso (colimit.isColimit _)
  let c' : Cofan (fun _ : ι ↦ V) :=
    Cofan.mk _ fun i ↦ pullback.lift (f := v ≫ f) (g := f) (𝟙 V) (v ≫ σ i) (by simp [hσ])
  let w : pullback (v ≫ f) f ⟶ pullback f f :=
    pullback.map _ _ _ _ v (𝟙 Y) (𝟙 X) (by simp) (by simp)
  have hw : IsPullback w (pullback.fst (v ≫ f) f) (pullback.fst f f) v :=
    IsPullback.of_right (h₁₂ := pullback.snd f f) (h₂₂ := f) (v₁₃ := f)
      (by simpa [w] using (IsPullback.of_hasPullback (v ≫ f) f).flip) (by simp [w])
      (IsPullback.of_hasPullback f f).flip
  have hv : 𝟙 V ≫ v = v := Category.id_comp v
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts hc c'
    (Discrete.natTrans fun _ ↦ v) w
    (by ext ⟨i⟩; apply pullback.hom_ext <;> simp [c, c', w, hv])
    (NatTrans.Equifibered.of_discrete _) fun ⟨i⟩ ↦ by
      refine IsPullback.of_right (h₁₂ := pullback.fst (v ≫ f) f) (h₂₂ := pullback.fst f f)
        ?_ (by apply pullback.hom_ext <;> simp [c, c', w, hv]) hw.flip
      simpa [c, c'] using IsPullback.of_id_fst (f := v)
  have : Sigma.desc
      (fun i ↦ pullback.lift (f := v ≫ f) (g := f) (𝟙 V) (v ≫ σ i) (by simp [hσ])) =
      ((colimit.isColimit _).coconePointUniqueUpToIso hc').hom :=
    Sigma.hom_ext _ _ fun i ↦ by
      rw [colimit.ι_desc]
      exact ((colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hc' ⟨i⟩).symm
  rw [this]
  infer_instance

end CategoryTheory
