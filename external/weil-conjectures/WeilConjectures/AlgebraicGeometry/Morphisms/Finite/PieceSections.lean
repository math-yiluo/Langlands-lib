/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.SplitNeighborhood
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products

/-!
# Sections of an étale sheaf over a split neighbourhood

For a split neighbourhood `s` of a geometric point `y` of `Y` with respect to a finite morphism
`f : X ⟶ Y`, the pieces of the decomposition of `U ×_Y X` are pairwise disjoint open and closed
subschemes covering `U ×_Y X`. Hence for a sheaf `G` on the small étale site of `X`, the
sections of `G` over `U ×_Y X` are the product of the sections over the pieces, naturally in
`s` (`AlgebraicGeometry.Scheme.Hom.SplitNbhd.sectionsIsoPi`).

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.SplitNbhd.pieceIncl`: the inclusion of the `t`-th piece into
  `U ×_Y X`, as a morphism of étale `X`-schemes.
- `AlgebraicGeometry.Scheme.Hom.SplitNbhd.sectionsFunctor`: the sections of `G` over
  `U ×_Y X`, as a functor on the opposite of the category of split neighbourhoods.
- `AlgebraicGeometry.Scheme.Hom.SplitNbhd.pieceSectionsFunctor`: the sections of `G` over the
  `t`-th piece.
- `AlgebraicGeometry.Scheme.Hom.SplitNbhd.sectionsIsoPi`: the natural isomorphism between the
  sections over `U ×_Y X` and the product of the sections over the pieces.

-/

@[expose] public section

universe u u'

open CategoryTheory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom.SplitNbhd

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

/-- The inclusion of the `t`-th piece of a split neighbourhood into `U ×_Y X`, as a morphism
of étale `X`-schemes. -/
def pieceIncl (s : SplitNbhd f y) (t : GeometricFiber f y) :
    s.pieceObj t ⟶ f.Etale.obj s.obj.1 :=
  MorphismProperty.Over.homMk (s.piece t).ι rfl

@[simp]
lemma pieceIncl_left (s : SplitNbhd f y) (t : GeometricFiber f y) :
    (s.pieceIncl t).left = (s.piece t).ι := rfl

instance (s : SplitNbhd f y) (t : GeometricFiber f y) : Mono (s.pieceIncl t) where
  right_cancellation g h hgh := by
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono (s.piece t).ι).mp
    exact congrArg (fun m ↦ m.left) hgh

/-- The point `(u, t)` of the `t`-th piece, seen in `U ×_Y X`, is `(u, t)`. -/
@[reassoc (attr := simp)]
lemma piecePt_comp_pieceIncl (s : SplitNbhd f y) (t : GeometricFiber f y) :
    (s.piecePt t).left ≫ (s.pieceIncl t).left = basePt f s.obj t :=
  s.piecePt_left_ι t

/-- The inclusions of the pieces are compatible with morphisms of split neighbourhoods. -/
@[reassoc]
lemma pieceMap_comp_pieceIncl {s s' : SplitNbhd f y} (g : s ⟶ s') (t : GeometricFiber f y) :
    pieceMap g t ≫ s'.pieceIncl t = s.pieceIncl t ≫ f.Etale.map g.val.val := by
  apply MorphismProperty.Over.Hom.ext
  exact pieceMap_left_ι g t

/-- The pieces of a split neighbourhood cover `U ×_Y X` in the small étale topology. -/
lemma ofArrows_pieceIncl_mem (s : SplitNbhd f y) :
    Sieve.ofArrows (fun t ↦ s.pieceObj t) (fun t ↦ s.pieceIncl t) ∈
      X.smallEtaleTopology (f.Etale.obj s.obj.1) := by
  rw [ofArrows_mem_smallEtaleTopology_iff]
  change ⋃ t, Set.range (s.piece t).ι.base = Set.univ
  simp only [Scheme.Opens.range_ι]
  rw [← TopologicalSpace.Opens.coe_iSup, s.iSup_eq, TopologicalSpace.Opens.coe_top]

/-- The pieces of a split neighbourhood are pairwise disjoint. -/
lemma disjoint_range_pieceIncl (s : SplitNbhd f y) {t t' : GeometricFiber f y} (h : t ≠ t') :
    Disjoint (Set.range (s.pieceIncl t).left.base) (Set.range (s.pieceIncl t').left.base) := by
  change Disjoint (Set.range (s.piece t).ι.base) (Set.range (s.piece t').ι.base)
  simp only [Scheme.Opens.range_ι]
  rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf,
    (s.disjoint t t' h).eq_bot, TopologicalSpace.Opens.coe_bot]

section Sections

variable (f y) {A : Type u'} [Category.{u + 1} A] (G : Sheaf X.smallEtaleTopology A)

/-- The sections of `G` over `U ×_Y X`, as a functor on the opposite of the category of split
neighbourhoods of `y`. -/
def sectionsFunctor : (SplitNbhd f y)ᵒᵖ ⥤ A :=
  (forget f y).op ⋙ (Functor.Elements.π (pointSmallEtale y).fiber).op ⋙ f.Etale.op ⋙ G.obj

/-- The sections of `G` over the `t`-th piece, as a functor on the opposite of the category of
split neighbourhoods of `y`. -/
def pieceSectionsFunctor (t : GeometricFiber f y) : (SplitNbhd f y)ᵒᵖ ⥤ A :=
  (pieceFunctor t).op ⋙ (Functor.Elements.π (pointSmallEtale t.1).fiber).op ⋙ G.obj

@[simp]
lemma sectionsFunctor_obj (s : (SplitNbhd f y)ᵒᵖ) :
    (sectionsFunctor f y G).obj s = G.obj.obj (op (f.Etale.obj s.unop.obj.1)) := rfl

@[simp]
lemma pieceSectionsFunctor_obj (t : GeometricFiber f y) (s : (SplitNbhd f y)ᵒᵖ) :
    (pieceSectionsFunctor f y G t).obj s = G.obj.obj (op (s.unop.pieceObj t)) := rfl

/-- Restriction of sections from `U ×_Y X` to the `t`-th piece. -/
@[simps]
def restrictToPiece (t : GeometricFiber f y) :
    sectionsFunctor f y G ⟶ pieceSectionsFunctor f y G t where
  app s := G.obj.map (s.unop.pieceIncl t).op
  naturality s s' g := by
    change G.obj.map (f.Etale.map g.unop.val.val).op ≫ G.obj.map (s'.unop.pieceIncl t).op =
      G.obj.map (s.unop.pieceIncl t).op ≫ G.obj.map (pieceMap g.unop t).op
    rw [← G.obj.map_comp, ← G.obj.map_comp, ← op_comp, ← op_comp, pieceMap_comp_pieceIncl]

variable [HasLimitsOfShape (Discrete (GeometricFiber f y)) A]

/-- The sections over `U ×_Y X` are the product of the sections over the pieces: the
components of the restriction maps to the pieces form an isomorphism. -/
instance isIso_piLift_restrictToPiece : IsIso (Pi.lift (restrictToPiece f y G)) := by
  have : ∀ s, IsIso ((Pi.lift (restrictToPiece f y G)).app s) := fun s ↦ by
    have h : (Pi.lift (restrictToPiece f y G)).app s ≫ (piObjIso _ s).hom =
        Pi.lift fun t ↦ (restrictToPiece f y G t).app s := by
      apply Pi.hom_ext
      intro t
      rw [Category.assoc, piObjIso_hom_comp_π, ← NatTrans.comp_app, Pi.lift_comp_π, Pi.lift_comp_π]
    rw [← Iso.eq_comp_inv] at h
    rw [h]
    have : IsIso (Pi.lift fun t ↦ (restrictToPiece f y G t).app s) :=
      Etale.isIso_piLift_of_disjoint G _ _ s.unop.ofArrows_pieceIncl_mem
        (fun t t' h ↦ s.unop.disjoint_range_pieceIncl h)
    exact inferInstance
  exact NatIso.isIso_of_isIso_app _

/-- **The sections over a split neighbourhood are the product of the sections over its
pieces**, naturally in the split neighbourhood. -/
def sectionsIsoPi : sectionsFunctor f y G ≅ ∏ᶜ pieceSectionsFunctor f y G :=
  asIso (Pi.lift (restrictToPiece f y G))

@[simp]
lemma sectionsIsoPi_hom : (sectionsIsoPi f y G).hom = Pi.lift (restrictToPiece f y G) := rfl

end Sections

end AlgebraicGeometry.Scheme.Hom.SplitNbhd

end
