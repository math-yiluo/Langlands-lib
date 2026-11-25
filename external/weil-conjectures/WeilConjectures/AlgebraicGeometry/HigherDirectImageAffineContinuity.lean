/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HigherDirectImageTransitions
import WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineClassDescent
import WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineClassVanishing
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-! # Affine sections of higher images under inverse limits

Source: Stacks Project, Tag 09Z1 and Tag 03Q8.
(blueprint: sbc-lem-higher-image-affine-continuity).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

/-- On each affine etale object, the canonical higher-image cocone is a colimit
of modules. Object isomorphisms and the equations on maps and legs present exactly
the canonical diagram; they impose no extra geometric assumption.
Source: Stacks Project, Tags 03Q8 and 09Z1, proof using cohomology continuity 09YQ.
(blueprint: sbc-lem-higher-image-affine-continuity).

Proof: Express higher images as sheafifications of restricted cohomology presheaves
(Tag 03Q8). For an affine etale V over S, base change of the inverse system has qcqs
stages, affine transitions, and limit V times_S c.pt. The sheaves are pulled back
from W; their further pullbacks to the limit form a diagram canonically isomorphic
to the constant diagram with value the pullback of G. The cofiltered index is
nonempty and connected, so its opposite diagram has this pullback as colimit.
Apply continuity for sheaves as degree-zero complexes (09YQ, or 0EZM) on every
affine etale object over V. For a cofiltered category, first use a small cofinal
directed presentation, and transport the limit and colimit along cofinality.
The resulting presheaf colimit comparison is an isomorphism on the affine basis.
These maps commute with restriction because they arise from the canonical derived
adjunction units. Sheafification commutes with colimits, giving the comparison of
sheaves. On the small etale site evaluation on an affine object preserves filtered
colimits: finite affine etale covers suffice, their intersections are quasi-compact,
and the finite equalizer sheaf condition commutes with filtered module colimits.
Evaluating the sheaf comparison therefore gives precisely the displayed cocone.
The same argument works for modules over the constant ring: an injective module
sheaf is acyclic for abelian section cohomology on every etale object (Tag 03FD),
so an injective module resolution computes the underlying abelian cohomology.
This identifies restricted cohomology and derived pushforward after forgetting
scalars. The comparison maps are linear, and forgetting reflects isomorphisms.
For negative q all cohomology objects vanish, so the same conclusion holds. -/
theorem nonempty_isColimit_higher_image_affine
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Over W)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f).left]
    [∀ i, QuasiCompact ((D.obj i).hom ≫ k)]
    [∀ i, QuasiSeparated ((D.obj i).hom ≫ k)]
    (c : Cone D) (hc : IsLimit ((Over.forget W).mapCone c))
    [QuasiCompact (c.pt.hom ≫ k)] [QuasiSeparated (c.pt.hom ≫ k)]
    (K : Iᵒᵖ ⥤ Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (eK : ∀ i : I, K.obj (op i) ≅
      higherDirectImage Λ ((D.obj i).hom ≫ k) q
        ((((D.obj i).hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (hK : ∀ {i j : I} (f : j ⟶ i), K.map f.op =
      (eK i).hom ≫ higherDirectImageOverMap Λ k G q (D.map f) ≫ (eK j).inv)
    (B : Cocone K)
    (eB : B.pt ≅ higherDirectImage Λ (c.pt.hom ≫ k) q
      (((c.pt.hom)^*[ModuleCat.{u + 1} Λ]).obj G))
    (hB : ∀ i : I, B.ι.app (op i) = (eK i).hom ≫
      higherDirectImageOverMap Λ k G q (c.π.app i) ≫ eB.inv)
    (V : S.Etale) [IsAffine V.left] :
    Nonempty (IsColimit
      ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (evaluation S.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op V)).mapCocone B)) := by
  classical
  let E := sheafToPresheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    (evaluation S.Etaleᵒᵖ (ModuleCat.{u + 1} Λ)).obj (op V)
  have := preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1}
    (forget (ModuleCat.{u + 1} Λ))
  have := reflectsColimit_of_reflectsIsomorphisms (K ⋙ E) (forget (ModuleCat.{u + 1} Λ))
  refine ⟨isColimitOfReflects (forget (ModuleCat.{u + 1} Λ)) ?_⟩
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨i, y, hy⟩ := exists_higher_image_affine_class_rep Λ k G q D c hc V
      ((eB.hom.hom.app (op V)) x)
    refine ⟨op i, ((eK i).inv.hom.app (op V)) y, ?_⟩
    change x = ((B.ι.app (op i)).hom.app (op V)) _
    rw [hB]
    change x = (E.map eB.inv) ((E.map (higherDirectImageOverMap Λ k G q
      (c.π.app i))) ((E.map (eK i).hom) ((E.map (eK i).inv) y)))
    have hei : (E.map (eK i).hom) ((E.map (eK i).inv) y) = y := by
      rw [← ModuleCat.comp_apply, ← E.map_comp, Iso.inv_hom_id, E.map_id,
        ModuleCat.id_apply]
    rw [hei]
    change (E.map (higherDirectImageOverMap Λ k G q (c.π.app i))) y =
      (E.map eB.hom) x at hy
    rw [hy, ← ModuleCat.comp_apply, ← E.map_comp, Iso.hom_inv_id, E.map_id,
      ModuleCat.id_apply]
  · intro i x y hxy
    change ((B.ι.app i).hom.app (op V)) x =
      ((B.ι.app i).hom.app (op V)) y at hxy
    have hz : ((B.ι.app i).hom.app (op V)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hcanon : ((higherDirectImageOverMap Λ k G q (c.π.app i.unop)).hom.app
        (op V)) (((eK i.unop).hom.hom.app (op V)) (x - y)) = 0 := by
      have h := congrArg (fun z ↦ (E.map eB.hom) z) hz
      rw [hB i.unop] at h
      change (E.map eB.hom) ((E.map eB.inv)
        ((E.map (higherDirectImageOverMap Λ k G q (c.π.app i.unop)))
          ((E.map (eK i.unop).hom) (x - y)))) = (E.map eB.hom) 0 at h
      have he : ∀ z, (E.map eB.hom) ((E.map eB.inv) z) = z := by
        intro z
        rw [← ModuleCat.comp_apply, ← E.map_comp, Iso.inv_hom_id, E.map_id,
          ModuleCat.id_apply]
      rw [he, map_zero] at h
      exact h
    obtain ⟨j, f, hf⟩ := exists_higher_image_affine_class_eq_zero Λ k G q D c hc V
      i.unop _ hcanon
    refine ⟨op j, f.op, ?_⟩
    change ((K.map f.op).hom.app (op V)) x = ((K.map f.op).hom.app (op V)) y
    apply sub_eq_zero.mp
    rw [← map_sub, hK]
    simpa using congrArg (fun z ↦ (((eK j).inv.hom.app (op V)) z)) hf

end AlgebraicGeometry.Etale
