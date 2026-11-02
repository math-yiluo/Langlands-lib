import Langlands.Sheaf.Equivariant.LocallyConstantSmooth
import Langlands.Sheaf.Equivariant.LocallyConstantCompactSupport
import Langlands.Sheaf.Equivariant.LocalSupportComparison
import Langlands.Sheaf.Equivariant.SmoothSheafCompactSections

/-! # Full compact functions as compact sections of the smooth locally constant sheaf -/

noncomputable section

universe u v

namespace Langlands.Sheaf.Equivariant.LocallyConstantSheaf.CompactSections

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {G : Type v} [Group G]
  {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]
  {M : Type u} [AddCommGroup M] [Module R M]

/-- Compose the actual function/section and local/stalk support equivalences. -/
def stalkEquiv (ρ : Representation R G M) :
    (FunctionModule.representation (X := X) ρ).Equiv
      (Langlands.Sheaf.Equivariant.CompactSections.representation (presheaf (X := X) ρ)) :=
  (equiv ρ).trans (LocalCompactSections.stalkEquiv (presheaf ρ))

variable (R G X)

/-- The function comparison reaches the existing stalk-supported compact-section functor. -/
def algebraicStalkComparison :
    functionFunctor R G X ≅
      LocallyConstantSheaf.functor R G X ⋙
        Langlands.Sheaf.Equivariant.CompactSections.functor R G X :=
  comparison R G X ≪≫
    Functor.isoWhiskerLeft (LocallyConstantSheaf.functor R G X)
      (LocalCompactSections.stalkComparison R G X)

variable [TopologicalSpace G] [HasStableNeighbourhoods G X]

/-- Construct the full smooth sheaf, then apply the published whole compact-section functor. -/
def smoothSheafSectionsFunctor :
    Langlands.SmoothRep.{u, v, u} R G ⥤ Langlands.SmoothRep.{u, v, u} R G :=
  LocallyConstantSheaf.smoothFunctor R G X ⋙ smoothSheafCompactSections R G X

variable {R G X}

/-- Smoothness of all compact functions follows from the actual smooth sheaf and
support comparisons, using stable neighborhoods rather than joint continuity. -/
theorem functionRepresentation_isSmooth_of_hasStableNeighbourhoods
    (ρ : Representation R G M) (hρ : Langlands.IsSmooth ρ) :
    Langlands.IsSmooth (FunctionModule.representation (X := X) ρ) :=
  Langlands.isSmooth_of_surjective (stalkEquiv ρ).symm.toIntertwiningMap
    (stalkEquiv ρ).symm.toLinearEquiv.surjective
    (Langlands.Sheaf.Equivariant.CompactSections.isSmooth_representation_of_isSmoothSheaf
      (LocallyConstantSheaf.isSmoothSheaf ρ hρ))

variable (R G X)

/-- Retain all compact functions and original coefficient maps with the derived smoothness. -/
def functionFunctorOfStableNeighbourhoods :
    Langlands.SmoothRep.{u, v, u} R G ⥤ Langlands.SmoothRep.{u, v, u} R G :=
  (Langlands.smoothRepProperty R G).lift
    (Langlands.SmoothRep.toRep ⋙ functionFunctor R G X)
    (fun A => functionRepresentation_isSmooth_of_hasStableNeighbourhoods
      A.representation A.isSmooth)

/-- Every compact function corresponds naturally to an actual compact section
of the constructed full smooth locally constant sheaf. -/
def smoothSheafComparison :
    functionFunctorOfStableNeighbourhoods R G X ≅ smoothSheafSectionsFunctor R G X :=
  NatIso.ofComponents (fun A => Langlands.SmoothRep.mkIso (stalkEquiv (X := X) A.representation))
    (by
      intro A B a
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      apply LocallyConstant.ext
      intro x
      rfl)

/-- Forgetting smoothness gives exactly the algebraic comparison, including all maps. -/
theorem smoothSheafComparison_toRep :
    Functor.isoWhiskerRight (smoothSheafComparison R G X) Langlands.SmoothRep.toRep =
      Functor.isoWhiskerLeft Langlands.SmoothRep.toRep (algebraicStalkComparison R G X) := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  rfl

end Langlands.Sheaf.Equivariant.LocallyConstantSheaf.CompactSections
