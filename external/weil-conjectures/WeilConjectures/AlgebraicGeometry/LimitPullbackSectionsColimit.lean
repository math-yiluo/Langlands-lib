/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.PullbackSectionsDiagram
import WeilConjectures.AlgebraicGeometry.PullbackSectionsIsColimit

/-!
# Sections of a pulled-back module sheaf over a descended affine etale object

Source: Stacks Project, Etale Cohomology, Lemma 09YU, proof, paragraph 'Fully faithful',
a special case of Theorem 09YQ in degree 0
(blueprint: lem-weil-pbc-limit-pullback-sections-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Let `D` be a directed inverse system of quasi-compact quasi-separated schemes with affine
transition morphisms, `c` a limit cone, `i₀` a stage, `G` an etale sheaf of `Λ`-modules on
`X₀ = D.obj (op i₀)` and `V₀ → X₀` an etale morphism with `V₀` affine. For `i ≥ i₀` the
sections of `G_i = f_{i i₀}^{-1} G` over `V_i = V₀ ×_{X₀} X_i` are the sections at `V₀` of
`(f_{i i₀})_* (f_{i i₀})^{-1} G`. The maps `ρ_{i' i}` (unit of `f_{i' i}^{-1} ⊣ f_{i' i,*}` at
`G_i`, then the composition isomorphisms of direct and inverse images) and `ρ_i` (the same with
the limit projection `f_i`) form a directed system with a compatible family; the induced map
`colim_{i ≥ i₀} G_i(V_i) → G_∞(V)` is bijective, stated by the elementwise criterion for
filtered colimits: every section on the limit comes from a stage, and two sections at a stage
with the same image on the limit agree at a later stage.

Source: Stacks Project, Tag 09YU ('Fully faithful'), Tag 09YQ in degree 0
(blueprint: lem-weil-pbc-limit-pullback-sections-colimit).

Proof:
1. The `V_i` are affine, etale over `X_i`, form an inverse system with affine transitions and
   limit `V = V₀ ×_{X₀} X` (`lem-weil-pbc-scheme-over-limit`,
   `lem-weil-pbc-affine-morphism-permanence`).
2. Module inverse images and their units are those of the underlying abelian sheaves
   (`situation-conventions`); the composition isomorphisms are
   `Λ`-linear by uniqueness of adjoints (`situation-conventions`).
3. The sheaves `F_i = w_i^{-1} G` on `V_i` with the composition isomorphisms form a system
   with colimit `w^{-1} G` on `V` (constant connected diagram).
4. Theorem 09YQ in degree 0 (`lem-weil-pbc-etale-cohomology-limit-of-schemes`), translated to
   sections, gives a bijection `colim_i F_i(V_i) → (w^{-1} G)(V)`.
5. Etale restriction isomorphisms and `lem-weil-pbc-etale-restriction-pullback-unit` identify
   that system with the maps `ρ`.
6. Hence the identities of a directed system and the cocone identities hold.
7. The elementwise criterion for filtered colimits of modules
   (`lem-weil-pbc-filtered-colimit-modules-elementwise`) gives bijectivity. -/
theorem limit_pullback_sections_colimit {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (Λ : Type (u + 1)) [CommRing Λ] (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V₀ : (D.obj (op i₀)).Etale) [IsAffine V₀.left] :
    (∀ (i : I) (h : i₀ ≤ i)
      (s : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj (op V₀)),
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (le_refl i)).op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE (le_refl i)).op)
          (D.map (homOfLE h).op) (D.map (homOfLE h).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE (le_refl i)).op)
            (D.map (homOfLE h).op) (D.map (homOfLE h).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s = s) ∧
    (∀ (i i' i'' : I) (h : i₀ ≤ i) (h' : i ≤ i') (h'' : i' ≤ i'')
      (s : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj (op V₀)),
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE h'').op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h'').op)
          (D.map (homOfLE (h.trans h')).op) (D.map (homOfLE ((h.trans h').trans h'')).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE ((h.trans h').trans h'')).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h'').op)
            (D.map (homOfLE (h.trans h')).op) (D.map (homOfLE ((h.trans h').trans h'')).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀)
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE h').op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
          (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
            (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s) =
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (h'.trans h'')).op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h'.trans h'')).op)
          (D.map (homOfLE h).op) (D.map (homOfLE ((h.trans h').trans h'')).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE ((h.trans h').trans h'')).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h'.trans h'')).op)
            (D.map (homOfLE h).op) (D.map (homOfLE ((h.trans h').trans h'')).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s) ∧
    (∀ (i i' : I) (h : i₀ ≤ i) (h' : i ≤ i')
      (s : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj (op V₀)),
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i'))).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i'))
          (D.map (homOfLE (h.trans h')).op) (c.π.app (op i₀))
          (c.w (homOfLE (h.trans h')).op).symm).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i'))
            (D.map (homOfLE (h.trans h')).op) (c.π.app (op i₀))
            (c.w (homOfLE (h.trans h')).op).symm).inv.app G)).hom.app (op V₀)
        (((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE h').op)).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
          (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
            (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s) =
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
          (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀))
            (c.w (homOfLE h).op).symm).inv.app G)).hom.app (op V₀) s) ∧
    (∀ t : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj G)).obj.obj (op V₀),
      ∃ (i : I) (h : i₀ ≤ i)
        (s : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj
            (op V₀)),
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))).unit.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
          (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).hom.app _ ≫
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
              (D.map (homOfLE h).op) (c.π.app (op i₀))
              (c.w (homOfLE h).op).symm).inv.app G)).hom.app (op V₀) s = t) ∧
    (∀ (i : I) (h : i₀ ≤ i)
      (s s' : ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)).obj.obj (op V₀)),
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
          (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀))
            (c.w (homOfLE h).op).symm).inv.app G)).hom.app (op V₀) s =
      ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
          ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i))).unit.app
            ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
        (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
          (D.map (homOfLE h).op) (c.π.app (op i₀)) (c.w (homOfLE h).op).symm).hom.app _ ≫
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i))
            (D.map (homOfLE h).op) (c.π.app (op i₀))
            (c.w (homOfLE h).op).symm).inv.app G)).hom.app (op V₀) s' →
      ∃ (i' : I) (h' : i ≤ i'),
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (D.map (homOfLE h').op)).unit.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
          (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
            (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
            (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
              (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
              (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s =
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
              (D.map (homOfLE h').op)).unit.app
              ((Etale.upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE h).op)).obj G)) ≫
          (Etale.lowerStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
            (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
            (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE (h.trans h')).op)).map
            ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) (D.map (homOfLE h').op)
              (D.map (homOfLE h).op) (D.map (homOfLE (h.trans h')).op)
              (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀) s') := by
  set_option maxRecDepth 2000 in
    let J := {i : I // i₀ ≤ i}
    let S : J → ModuleCat.{u + 1} Λ := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)).obj.obj
          (op V₀)
    let T : ModuleCat.{u + 1} Λ := ((lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj
      ((upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj G)).obj.obj (op V₀)
    let μ : ∀ {i j : J}, (i ⟶ j) → (S i ⟶ S j) := fun {i j} f ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ)
          (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
          (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE j.property).op)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
            (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀)
    let τ : ∀ i : J, S i ⟶ T := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
          (D.map (homOfLE i.property).op) (c.π.app (op i₀))
          (c.w (homOfLE i.property).op).symm).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
            (D.map (homOfLE i.property).op) (c.π.app (op i₀))
            (c.w (homOfLE i.property).op).symm).inv.app G)).hom.app (op V₀)
    obtain ⟨F, B, e, eB, hm, ht⟩ := exists_pullbackSections_diagram D c Λ i₀ G V₀
    obtain ⟨hB⟩ := nonempty_isColimit_pullbackSections D c hc Λ i₀ G V₀ F B e eB hm ht
    change ∀ (i j : J) (f : i ⟶ j), (e i).inv ≫ F.map f ≫ (e j).hom = μ f at hm
    change ∀ i : J, (e i).inv ≫ B.ι.app i ≫ eB.hom = τ i at ht
    let : Nonempty J := ⟨⟨i₀, le_refl i₀⟩⟩
    let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
      obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
      exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
    let : PreservesFilteredColimitsOfSize.{u, u} (forget (ModuleCat.{u + 1} Λ)) :=
      preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
    have hμid (i : J) : μ (𝟙 i) = 𝟙 (S i) := by
      rw [← hm i i (𝟙 i), F.map_id]
      simp only [Category.id_comp, Iso.inv_hom_id]
      rfl
    have hμcomp {i j k : J} (f : i ⟶ j) (g : j ⟶ k) : μ f ≫ μ g = μ (f ≫ g) := by
      rw [← hm i j f, ← hm j k g, ← hm i k (f ≫ g), F.map_comp]
      simp [Category.assoc]
    have hτ {i j : J} (f : i ⟶ j) : μ f ≫ τ j = τ i := by
      rw [← hm i j f, ← ht j, ← ht i]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc (F.map f) (B.ι.app j) eB.hom, B.w f]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i h s
      change μ (𝟙 (⟨i, h⟩ : J)) s = s
      rw [hμid]
      rfl
    · intro i i' i'' h h' h'' s
      let a : J := ⟨i, h⟩
      let b : J := ⟨i', h.trans h'⟩
      let d : J := ⟨i'', (h.trans h').trans h''⟩
      let f : a ⟶ b := homOfLE h'
      let g : b ⟶ d := homOfLE h''
      change μ g (μ f s) = μ (f ≫ g) s
      exact ConcreteCategory.congr_hom (hμcomp f g) s
    · intro i i' h h' s
      let a : J := ⟨i, h⟩
      let b : J := ⟨i', h.trans h'⟩
      let f : a ⟶ b := homOfLE h'
      change τ b (μ f s) = τ a s
      exact ConcreteCategory.congr_hom (hτ f) s
    · intro t
      obtain ⟨i, x, hx⟩ := Concrete.isColimit_exists_rep F hB (eB.inv t)
      refine ⟨i.val, i.property, (e i).hom x, ?_⟩
      change τ i ((e i).hom x) = t
      rw [← ht i]
      have hex : (e i).inv ((e i).hom x) = x :=
        ConcreteCategory.congr_hom (e i).hom_inv_id x
      change eB.hom (B.ι.app i ((e i).inv ((e i).hom x))) = t
      rw [hex]
      have heB : eB.hom (eB.inv t) = t :=
        ConcreteCategory.congr_hom eB.inv_hom_id t
      exact (congrArg eB.hom hx).trans heB
    · intro i h s s' hs
      let a : J := ⟨i, h⟩
      have hrep : B.ι.app a ((e a).inv s) = B.ι.app a ((e a).inv s') := by
        apply (ConcreteCategory.bijective_of_isIso eB.hom).1
        change (eB.hom) (B.ι.app a ((e a).inv s)) =
          (eB.hom) (B.ι.app a ((e a).inv s'))
        change (τ a) s = (τ a) s' at hs
        change ((e a).inv ≫ B.ι.app a ≫ eB.hom) s =
          ((e a).inv ≫ B.ι.app a ≫ eB.hom) s'
        rw [ht a]
        exact hs
      obtain ⟨j, f, g, hj⟩ :=
        (Concrete.isColimit_rep_eq_iff_exists F hB ((e a).inv s) ((e a).inv s')).mp hrep
      have hfg : f = g := Subsingleton.elim _ _
      subst g
      refine ⟨j.val, leOfHom f, ?_⟩
      change μ f s = μ f s'
      rw [← hm a j f]
      exact congrArg (e j).hom hj

end AlgebraicGeometry.Etale
