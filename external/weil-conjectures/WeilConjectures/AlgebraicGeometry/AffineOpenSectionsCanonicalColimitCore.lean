/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsDescent
import WeilConjectures.AlgebraicGeometry.AffineOpenSectionsZeroDetection
import Mathlib.Algebra.Category.Grp.FilteredColimits

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
/-- The affine continuity theorem for a supplied canonical restriction transformation.
Source: Stacks Project, Tag 03Q6, degree-zero continuity on affine neighbourhoods.
The affine-site continuity argument identifies sections on the limiting affine scheme with
the filtered colimit of sections on the affine stages; the displayed component formula
ensures that this identification is the cocone built from ν. The proof uses the limit cone
and the affine/open hypotheses.
(blueprint: affine-open-sections-canonical-colimit-core) -/
theorem affineOpenSections_canonical_colimit_core
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology c.pt.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ν₀ : D.op ⋙ F.obj ⟶ (Functor.const Jᵒᵖ).obj
      ((H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))))
    (hν₀ : ∀ j, ν₀.app (op j) = (hH.unit.app F).hom.app (op (D.obj j)) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (B := p.Etale.obj (D.obj j))
        (pullback.lift (c.π.app j) (𝟙 c.pt) (by
          change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
          rw [Category.id_comp]
          exact hp j))
        (by exact pullback.lift_snd _ _ _)).op) :
    Nonempty (IsColimit (Cocone.mk _ ν₀)) := by
  classical
  let U := forget AddCommGrpCat.{u + 1}
  let C := Cocone.mk _ ν₀
  -- The underlying type colimit is determined by representatives and eventual equality.
  have hdescent := affineOpenSections_descent D c p hp hc H hH F ν₀ hν₀
  have hzero := affineOpenSections_zero_detection D c p hp hc H hH F ν₀ hν₀
  have ht : IsColimit (U.mapCocone C) := by
    apply Types.FilteredColimit.isColimitOf'
    · intro t
      obtain ⟨j, s, hs⟩ := hdescent t
      exact ⟨op j, s, hs.symm⟩
    · intro j a b hab
      have habzero : ν₀.app j (a - b) = 0 := by
        change ν₀.app j a = ν₀.app j b at hab
        simpa only [map_sub, sub_eq_zero] using hab
      obtain ⟨k, f, hf⟩ := hzero j.unop (a - b) habzero
      refine ⟨op k, f.op, ?_⟩
      change F.obj.map (D.map f).op a = F.obj.map (D.map f).op b
      simpa only [map_sub, sub_eq_zero] using hf
  -- Forgetting additive groups preserves filtered colimits and reflects isomorphisms.
  let : ReflectsColimit (D.op ⋙ F.obj) U :=
    reflectsColimit_of_reflectsIsomorphisms _ U
  exact ⟨isColimitOfReflects U ht⟩
