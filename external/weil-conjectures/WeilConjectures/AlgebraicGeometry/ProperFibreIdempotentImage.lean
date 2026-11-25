/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProperFibreIdempotentImageNoetherian
import WeilConjectures.AlgebraicGeometry.ProperFibreIdempotentDescent

/-!
# Idempotents on a proper fibre come from a neighbourhood

Source: Stacks Project, Tag 0G7X, Lemma 36.32.7
(blueprint: lem-weil-pbc-stein-fibre-idempotent-image).

Image membership in the pushforward stalk is expressed by a representative section on
an open neighbourhood of the base point. No idempotence is required of the representative.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every idempotent on the scheme-theoretic fibre of a proper morphism is the restriction
of a section over the inverse image of an open neighbourhood of the base point. Equivalently,
it belongs to the image of the pushforward structure-sheaf stalk: every germ has such a
representative, and the canonical stalk-to-fibre map restricts that representative.
Source: Stacks Project, Tag 0G7X (blueprint: lem-weil-pbc-stein-fibre-idempotent-image).

Proof:
1. In the locally Noetherian case choose an affine neighbourhood of `s`. Its local ring is
   Noetherian (`pqf-def-locnoeth`, `lem-weil-pbc-localization-noetherian`).
2. Lift `e` uniquely to the infinitesimal thickenings of the fibre; uniqueness makes these
   lifts compatible (`lem-weil-pbc-base-change-nilpotent-thickening-idempotents`).
3. Formal functions identifies the completion of the pushforward stalk with the inverse
   limit of the sections on these thickenings, compatibly with restriction to the fibre
   (`lem-weil-pbc-formal-functions-stalk`).
4. Modulo the maximal ideal, a module and its completion agree. Choose a stalk element
   agreeing with the completed lift modulo that ideal. The ideal kills fibre sections,
   so its image is `e` (`lem-weil-pbc-module-completion-complete`).
5. In general restrict the base to an affine neighbourhood of `s`; properness is preserved
   and the stalk and fibre are unchanged (`lem-weil-pbc-proper-base-change`).
6. Use Noetherian approximation by proper morphisms over finite-type integer algebras
   (`lem-weil-pbc-proper-limit-noetherian`, `lem-weil-pbc-finite-type-algebra-noetherian`).
7. The residue field and fibre are the limits of the corresponding residue fields and
   fibres, with affine transition maps (`lem-weil-pbc-limit-residue-field`,
   `lem-weil-pbc-limit-fibre-products`, `pqf-lem-proper-basic`).
8. Global sections commute with this limit. Descend `e` to a section at a finite stage,
   then descend its equation `e * e = e` at a later stage
   (`lem-weil-pbc-limit-global-sections-colimit`).
9. Apply the Noetherian case there, represent the resulting germ on an open neighbourhood,
   and pull the representative back. Compatibility of fibre maps gives image `e`. -/
theorem Scheme.Hom.exists_section_restricting_to_fiber_idempotent
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (s : S)
    (e : Γ(f.fiber s, ⊤)) (he : IsIdempotentElem e) :
    ∃ (U : S.Opens), s ∈ U ∧
      ∃ (h : (⊤ : (f.fiber s).Opens) ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U))
        (t : Γ(X, f ⁻¹ᵁ U)),
        (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ h t = e := by
  obtain ⟨W, hsW, Y, T, g, hg, hT, p, r, a, q, e₀, hcomm, ha, hq, he₀, hqe⟩ :=
    proper_fibre_idempotent_descent f s e he
  let := hg
  let := hT
  obtain ⟨V, hsV, hV, t, ht⟩ :=
    proper_fibre_idempotent_image_noetherian g (r ⟨s, hsW⟩) e₀ he₀
  let U := W.ι ''ᵁ (r ⁻¹ᵁ V)
  have hU : s ∈ U := ⟨⟨s, hsW⟩, hsV, rfl⟩
  have hp : p ⁻¹ᵁ (g ⁻¹ᵁ V) = (f ∣_ W) ⁻¹ᵁ (r ⁻¹ᵁ V) := by
    ext x
    change g (p x) ∈ V ↔ r ((f ∣_ W) x) ∈ V
    rw [← Scheme.Hom.comp_apply, hcomm, Scheme.Hom.comp_apply]
  have hA : (f ⁻¹ᵁ W).ι ''ᵁ (p ⁻¹ᵁ (g ⁻¹ᵁ V)) = f ⁻¹ᵁ U := by
    rw [hp, image_morphismRestrict_preimage]
  have hi : p ⁻¹ᵁ (g ⁻¹ᵁ V) ≤ (f ⁻¹ᵁ W).ι ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← hA, Scheme.Hom.preimage_image_eq]
  let v := (f ⁻¹ᵁ W).ι.appLE (f ⁻¹ᵁ U) (p ⁻¹ᵁ (g ⁻¹ᵁ V)) hi
  have hv : IsIso v := by
    dsimp [v]
    apply ((f ⁻¹ᵁ W).ι.appLE_congr hi hA.symm rfl
      (fun {_ _} k ↦ IsIso k)).mpr
    rw [← Scheme.Hom.appIso_hom']
    infer_instance
  let := hv
  let t' := inv v (p.app (g ⁻¹ᵁ V) t)
  have ht' : v t' = p.app (g ⁻¹ᵁ V) t := by
    exact ConcreteCategory.congr_hom (IsIso.inv_hom_id v) (p.app (g ⁻¹ᵁ V) t)
  have hf : (⊤ : (f.fiber s).Opens) ≤ (f.fiberι s) ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    intro x hx
    change f (f.fiberι s x) ∈ U
    have hx' : f (f.fiberι s x) = s := by
      have : f.fiberι s x ∈ Set.range (f.fiberι s) := ⟨x, rfl⟩
      rw [f.range_fiberι s] at this
      exact this
    simpa [hx'] using hU
  have haO : (⊤ : (f.fiber s).Opens) ≤ a ⁻¹ᵁ (p ⁻¹ᵁ (g ⁻¹ᵁ V)) := by
    intro x hx
    have hxV := hV (show q x ∈ (⊤ : (g.fiber (r ⟨s, hsW⟩)).Opens) from trivial)
    change g (p (a x)) ∈ V
    change g (g.fiberι (r ⟨s, hsW⟩) (q x)) ∈ V at hxV
    simpa only [← Scheme.Hom.comp_apply, hq] using hxV
  refine ⟨U, hU, hf, t', ?_⟩
  have hmaps : v ≫ a.appLE (p ⁻¹ᵁ (g ⁻¹ᵁ V)) ⊤ haO =
      (f.fiberι s).appLE (f ⁻¹ᵁ U) ⊤ hf := by
    dsimp [v]
    rw [Scheme.Hom.appLE_comp_appLE]
    congr 1
  have hmaps' : p.app (g ⁻¹ᵁ V) ≫ a.appLE (p ⁻¹ᵁ (g ⁻¹ᵁ V)) ⊤ haO =
      (g.fiberι (r ⟨s, hsW⟩)).appLE (g ⁻¹ᵁ V) ⊤ hV ≫ q.appTop := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
      Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact hq.symm
  calc
    _ = a.appLE (p ⁻¹ᵁ (g ⁻¹ᵁ V)) ⊤ haO (v t') :=
      (ConcreteCategory.congr_hom hmaps t').symm
    _ = a.appLE (p ⁻¹ᵁ (g ⁻¹ᵁ V)) ⊤ haO (p.app (g ⁻¹ᵁ V) t) := by rw [ht']
    _ = q.appTop ((g.fiberι (r ⟨s, hsW⟩)).appLE (g ⁻¹ᵁ V) ⊤ hV t) :=
      ConcreteCategory.congr_hom hmaps' t
    _ = e := by rw [ht, hqe]

end AlgebraicGeometry
