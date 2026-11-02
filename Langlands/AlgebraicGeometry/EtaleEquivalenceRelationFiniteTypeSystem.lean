import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationStableSystem
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationOpenExtensionFiniteType

/-! # Finite type systems and recovery of finite tuple tails -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

namespace IsCartesianHom

open RingEtaleGroupoid

variable {E F : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ F.U} {g : E.R ⟶ F.R}
  (h : IsCartesianHom E F f g) [IsAffine E.U] [IsAffine F.U] [IsAffine F.R]

/-- Absolute finite type is preserved at the stable affine levels. -/
lemma stableDiagram_locallyOfFiniteType [LocallyOfFiniteType (terminal.from F.U)]
    (i : (h.stableIndex)ᵒᵖ) :
    LocallyOfFiniteType (terminal.from (h.stableDiagram.obj i).U) := by
  let := F.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  let : Algebra.FiniteType ℤ Γ(F.U, ⊤) :=
    AbsoluteNoetherianApproximation.finiteType_of_locallyOfFiniteType (isAffineOpen_top F.U)
  let := StableSystem.finiteType_int (θ := h.coaction) i.unop
  exact locallyOfFiniteType_terminal_spec (CommRingCat.of i.unop.1)

end IsCartesianHom

/-- The precise finite type diagram needed for the open-extension step. Its
cone point is the supplied relation itself. -/
structure FiniteTypeCartesianSystem (E : EtaleEquivalenceRelation.{u}) where
  Index : Type u
  [category : Category.{u} Index]
  [cofiltered : IsCofiltered Index]
  diagram : Index ⥤ EtaleEquivalenceRelation.{u}
  comparison : (Functor.const Index).obj E ⟶ diagram
  isLimitObject : IsLimit (objectFunctor.mapCone (Cone.mk E comparison))
  object_compact : ∀ i, CompactSpace (diagram.obj i).U
  object_finiteType : ∀ i, LocallyOfFiniteType (terminal.from (diagram.obj i).U)
  relation_compact : ∀ i, CompactSpace (diagram.obj i).R
  relation_quasiSeparated : ∀ i, QuasiSeparatedSpace (diagram.obj i).R
  source_isSeparated : ∀ i, IsSeparated (diagram.obj i).s
  objectMap_isAffine : ∀ {i j} (a : i ⟶ j), IsAffineHom (diagram.map a).objMap

attribute [instance] FiniteTypeCartesianSystem.category FiniteTypeCartesianSystem.cofiltered
  FiniteTypeCartesianSystem.object_compact FiniteTypeCartesianSystem.object_finiteType
  FiniteTypeCartesianSystem.relation_compact FiniteTypeCartesianSystem.relation_quasiSeparated
  FiniteTypeCartesianSystem.source_isSeparated FiniteTypeCartesianSystem.objectMap_isAffine

namespace FiniteTypeCartesianSystem

variable {E : EtaleEquivalenceRelation.{u}} (D : FiniteTypeCartesianSystem E)

/-- The actual cone, with point definitionally equal to `E`. -/
def cone : Cone D.diagram := Cone.mk E D.comparison

include D in
/-- An affine open extension of the supplied limit relation has a finite type
affine first level when its nonidentity arrows are affine. -/
lemma nonempty_firstLevel_openExtension [IsSeparated E.s]
    [IsAffine (OpenExtension.offDiagonalOpen E).toScheme]
    {S : Scheme.{u}} [IsAffine S] (ι : E.U ⟶ S) [IsOpenImmersion ι] :
    Nonempty (AffineFiniteTypeFirstLevel (OpenExtension.relation E ι)) := by
  let : IsSeparated D.cone.pt.s := inferInstanceAs (IsSeparated E.s)
  let : IsAffine (OpenExtension.offDiagonalOpen D.cone.pt).toScheme :=
    inferInstanceAs (IsAffine (OpenExtension.offDiagonalOpen E).toScheme)
  exact CartesianDiagram.nonempty_affineFiniteTypeFirstLevel_openExtension
    D.diagram D.cone ι D.isLimitObject

end FiniteTypeCartesianSystem

namespace AffineFiniteTypeFirstLevel

variable {E : EtaleEquivalenceRelation.{u}} [IsAffine E.U]
  (M : AffineFiniteTypeFirstLevel E)

/-- Reconstruct a finite type cofiltered system from one actual first level. -/
def system : FiniteTypeCartesianSystem E := by
  let h := M.comparison.isCartesian
  letI : IsNoetherianRing Γ(M.relation.U, ⊤) := inferInstance
  letI := h.stableIndex_isCofiltered
  refine
    { Index := h.stableIndexᵒᵖ
      category := inferInstance
      cofiltered := inferInstance
      diagram := h.stableDiagram
      comparison := h.stableCone.π
      isLimitObject := h.stableCone_isLimitObject
      object_compact := fun _ => inferInstance
      object_finiteType := h.stableDiagram_locallyOfFiniteType
      relation_compact := fun _ => inferInstance
      relation_quasiSeparated := fun _ => inferInstance
      source_isSeparated := fun _ => inferInstance
      objectMap_isAffine := fun _ => inferInstance }

end AffineFiniteTypeFirstLevel

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

/-- A finite type system on the actual next-threshold restriction produces
a finite type first level of the whole finite tuple tail. -/
lemma nonempty_affineFiniteTypeFirstLevel_tupleTail (N p : ℕ) (hp : p < N + 1)
    (D : FiniteTypeCartesianSystem (E.tupleTailNextRelation N p)) :
    Nonempty (AffineFiniteTypeFirstLevel (E.tupleTailPresentation N p)) := by
  let := E.tupleTailNextRelation_offDiagonal_isAffine N p hp
  obtain ⟨M⟩ := D.nonempty_firstLevel_openExtension (E.tupleTailNextOpen N p).ι
  let a : E.tupleTailPresentation N p ⟶ E.tupleTailOpenExtension N p :=
    { objMap := 𝟙 _
      relMap := (E.tupleTailOpenExtensionArrowsIso N p hp).inv
      isCartesian := E.tupleTailOpenExtension_inv_isCartesianHom N p hp }
  exact ⟨AffineFiniteTypeFirstLevel.ofCartesian a M⟩

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
