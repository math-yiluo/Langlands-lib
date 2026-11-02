import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationOffDiagonalCartesian
import Langlands.AlgebraicGeometry.AbsoluteNoetherianApproximation.AffinePinching
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationAffineQuotientDescent

/-! # A finite type level from an open-extension model -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

/-- An actual cartesian first level whose object scheme is affine and of finite
 type over the integers and whose arrow scheme is affine. -/
structure AffineFiniteTypeFirstLevel (E : EtaleEquivalenceRelation.{u}) where
  relation : EtaleEquivalenceRelation.{u}
  comparison : E ⟶ relation
  object_isAffine : IsAffine relation.U
  object_finiteType : LocallyOfFiniteType (terminal.from relation.U)
  arrows_isAffine : IsAffine relation.R

attribute [instance] AffineFiniteTypeFirstLevel.object_isAffine
  AffineFiniteTypeFirstLevel.object_finiteType AffineFiniteTypeFirstLevel.arrows_isAffine

instance {E : EtaleEquivalenceRelation.{u}} (M : AffineFiniteTypeFirstLevel E) :
    IsNoetherian M.relation.U := by
  have := AbsoluteNoetherianApproximation.isLocallyNoetherian_of_locallyOfFiniteType M.relation.U
  exact ⟨⟩

/-- Finite type over the integers, using the chosen absolute terminal scheme. -/
lemma locallyOfFiniteType_terminal_spec (A : CommRingCat.{u}) [Algebra.FiniteType ℤ A] :
    LocallyOfFiniteType (terminal.from (Spec A)) := by
  have := locallyOfFinitePresentation_toSpecULiftZ A
  let e : Spec (CommRingCat.of (ULift.{u} ℤ)) ≅ ⊤_ Scheme.{u} :=
    specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal
  have h : terminal.from (Spec A) = specULiftZIsTerminal.from (Spec A) ≫ e.hom :=
    terminal.hom_ext _ _
  rw [h]
  infer_instance

namespace AffineFiniteTypeFirstLevel

/-- Pull a first level back along an actual cartesian morphism. -/
def ofCartesian {E F : EtaleEquivalenceRelation.{u}} (a : E ⟶ F)
    (M : AffineFiniteTypeFirstLevel F) : AffineFiniteTypeFirstLevel E where
  relation := M.relation
  comparison := a ≫ M.comparison
  object_isAffine := M.object_isAffine
  object_finiteType := M.object_finiteType
  arrows_isAffine := M.arrows_isAffine

end AffineFiniteTypeFirstLevel

namespace CartesianDiagram

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ EtaleEquivalenceRelation.{u}) (c : Cone D)
  [∀ i, IsSeparated (D.obj i).s] [IsSeparated c.pt.s]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a).objMap]
  [∀ i, CompactSpace (D.obj i).U]
  [∀ i, LocallyOfFiniteType (terminal.from (D.obj i).U)]
  [∀ i, CompactSpace (D.obj i).R] [∀ i, QuasiSeparatedSpace (D.obj i).R]
  [IsAffine (OpenExtension.offDiagonalOpen c.pt).toScheme]
  {S : Scheme.{u}} [IsAffine S] (ι : c.pt.U ⟶ S) [IsOpenImmersion ι]

include c in
/-- The affine open-model theorem and eventual nonidentity-arrow affineness give
 an actual affine finite type first level of the open extension. -/
lemma nonempty_affineFiniteTypeFirstLevel_openExtension
    (hc : IsLimit (objectFunctor.mapCone c)) :
    Nonempty (AffineFiniteTypeFirstLevel (OpenExtension.relation c.pt ι)) := by
  have (i : I) : IsAffineHom ((D ⋙ objectFunctor).map (𝟙 i)) := by
    change IsAffineHom (D.map (𝟙 i)).objMap
    infer_instance
  have hmap {i j : I} (a : i ⟶ j) : IsAffineHom ((D ⋙ objectFunctor).map a) :=
    inferInstanceAs (IsAffineHom (D.map a).objMap)
  have hcompact (i : I) : CompactSpace ((D ⋙ objectFunctor).obj i) :=
    inferInstanceAs (CompactSpace (D.obj i).U)
  have hft (i : I) : LocallyOfFiniteType (terminal.from ((D ⋙ objectFunctor).obj i)) :=
    inferInstanceAs (LocallyOfFiniteType (terminal.from (D.obj i).U))
  obtain ⟨i, hi⟩ := OffDiagonal.exists_isAffine D c hc
  obtain ⟨j, a, ⟨M⟩⟩ := AbsoluteNoetherianApproximation.exists_finiteTypeOpenModel_of_isLimit
    (D ⋙ objectFunctor) (objectFunctor.mapCone c) hc ι ∅ Set.finite_empty i
  have : IsAffine (OpenExtension.offDiagonalOpen (D.obj i)).toScheme := hi
  have : IsAffine (OpenExtension.offDiagonalOpen (D.obj j)).toScheme :=
    OffDiagonal.isAffine_of_map D a
  let F := OpenExtension.relation (D.obj j) M.e
  have hF : IsAffine F.R := OpenExtension.arrows_isAffine_of_offDiagonal (D.obj j) M.e
  let f : OpenExtension.relation c.pt ι ⟶ F :=
    { objMap := M.φ
      relMap := OpenExtension.Comparison.map
        (E := c.pt) (F := D.obj j) (f := (c.π.app j).objMap) (g := (c.π.app j).relMap)
        ι M.e M.φ (c.π.app j).isCartesian.1 (c.π.app j).isCartesian.2.w M.isPullback.w.symm
      isCartesian := OpenExtension.Comparison.isCartesianHom
        (E := c.pt) (F := D.obj j) (f := (c.π.app j).objMap) (g := (c.π.app j).relMap)
        (ι := ι) (κ := M.e) (v := M.φ) M.isPullback.w.symm
        (c.π.app j).isCartesian M.isPullback }
  exact ⟨⟨F, f, inferInstanceAs (IsAffine (Spec M.A)),
    locallyOfFiniteType_terminal_spec M.A, hF⟩⟩

end CartesianDiagram

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
