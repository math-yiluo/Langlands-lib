/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Factorization of étale maps from an affine limit -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- A map from the affine limit to an étale X-scheme factors through an affine stage.
Source: Stacks Project, Limits, Tag 01ZM, morphism descent; Étale Cohomology,
Tag 0EYL, proof of full faithfulness.
(blueprint: affine-open-etale-map-factorization).

Proof: The underlying diagram consists of affine schemes, so its terms are qcqs
and all its transition maps are affine. Its structure maps form a natural transformation
to the constant scheme X, and hp identifies the induced map on the limit with p.
The target U is étale over X, hence locally of finite presentation. Apply Mathlib's
Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation directly to q. It gives
simultaneously the factorization equation and the equation over X. No quasi-compactness
or quasi-separatedness assumption on U or X is required. The theorem includes empty
limits and singleton systems. -/
theorem affineOpenSections_etale_map_factorization
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (U : X.Etale) (q : c.pt ⟶ U.left) (hq : q ≫ U.hom = p) :
    ∃ (j : J) (g : (D.obj j).left ⟶ U.left),
      g ≫ U.hom = (D.obj j).hom ∧ c.π.app j ≫ g = q := by
  let E := D ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  let τ : E ⟶ (Functor.const J).obj X :=
    { app := fun j ↦ (D.obj j).hom
      naturality := fun i j f ↦ by
        change (D.map f).left ≫ (D.obj j).hom = (D.obj i).hom ≫ 𝟙 X
        exact (MorphismProperty.Over.w (D.map f)).trans (Category.comp_id _).symm }
  have : ∀ j, CompactSpace (E.obj j) := fun j ↦ by
    change CompactSpace (D.obj j).left
    infer_instance
  have : ∀ j, QuasiSeparatedSpace (E.obj j) := fun j ↦ by
    change QuasiSeparatedSpace (D.obj j).left
    infer_instance
  have : ∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f) := fun f ↦ by
    change IsAffineHom (D.map f).left
    infer_instance
  have he : c.π ≫ τ = (Functor.const J).map (q ≫ U.hom) := by
    ext j
    change c.π.app j ≫ (D.obj j).hom = q ≫ U.hom
    rw [hp j, hq]
  obtain ⟨j, g, hgj, hg⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation E τ U.hom c hc q he
  exact ⟨j, g, hg, hgj⟩

