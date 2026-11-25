/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Explicit finite étale splitting data and its sum

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE.
(blueprint: lemma-reduction-unipotent-local-system--2)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- A finite clopen coproduct splitting of `T ×[X] Y`, with explicit inverse projections.
The empty index type is allowed. All data are supplied by the constructor.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE.
(blueprint: lemma-reduction-unipotent-local-system--2) -/
structure FiniteEtaleTraceSplitting {X Y : Scheme.{u}} (f : Y ⟶ X) (T : X.Etale) where
  J : Type u
  finiteIndex : Fintype J
  V : J → Scheme.{u}
  i : ∀ j, V j ⟶ pullback T.hom f
  t : ∀ j, T.left ⟶ V j
  colimit : IsColimit (Cofan.mk (pullback T.hom f) i)
  inv₁ : ∀ j, t j ≫ i j ≫ pullback.fst T.hom f = 𝟙 T.left
  inv₂ : ∀ j, i j ≫ pullback.fst T.hom f ≫ t j = 𝟙 (V j)
  openImmersion : ∀ j, IsOpenImmersion (i j)
  closedImmersion : ∀ j, IsClosedImmersion (i j)

/-- The presieve of arrows with split domain; membership records no chosen splitting.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE.
(blueprint: lemma-reduction-unipotent-local-system--2) -/
def finiteEtaleTraceSplitPresieve {X Y : Scheme.{u}} (f : Y ⟶ X) (W : X.Etale) :
    Presieve W := fun {T} _ ↦ Nonempty (FiniteEtaleTraceSplitting f T)

/-- The section of the pullback associated to a sheet.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE.
(blueprint: lemma-reduction-unipotent-local-system--2) -/
noncomputable def FiniteEtaleTraceSplitting.sectionMap {X Y : Scheme.{u}} {f : Y ⟶ X}
    {T : X.Etale} (D : FiniteEtaleTraceSplitting f T) (hf : Etale f) (j : D.J) :
    T ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f ⋙
      MorphismProperty.Over.map ⊤ hf).obj T :=
  MorphismProperty.Over.homMk (D.t j ≫ D.i j) (by
    change (D.t j ≫ D.i j) ≫ pullback.snd T.hom f ≫ f = T.hom
    rw [← pullback.condition]
    simpa [← Category.assoc] using
      congrArg (fun k ↦ k ≫ T.hom) (D.inv₁ j))

/-- The sum of restrictions along the sections of an explicit splitting.
Source: Stacks Project, Section 03SH, paragraph after Definition 03SE.
(blueprint: lemma-reduction-unipotent-local-system--2) -/
noncomputable def FiniteEtaleTraceSplitting.sum {X Y : Scheme.{u}} {f : Y ⟶ X}
    {T : X.Etale} (D : FiniteEtaleTraceSplitting f T) (hf : Etale f)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (s : F.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f ⋙
      MorphismProperty.Over.map ⊤ hf).obj T))) : F.obj.obj (op T) :=
  letI := D.finiteIndex
  ∑ j, F.obj.map (D.sectionMap hf j).op s

end AlgebraicGeometry.Etale
