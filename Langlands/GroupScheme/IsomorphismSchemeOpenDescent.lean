import Langlands.GroupScheme.IsomorphismSheaf
import Langlands.GroupScheme.IsomorphismSchemeLocalChart
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget

/-! # Open descent and local geometry of full Isom representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.GroupScheme.GroupIsomorphismScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- Full all-test Isom representatives over an open cover glue to an actual
representative over the original base. -/
def ofOpenCover (𝒰 : Scheme.OpenCover.{u} S)
    (J : ∀ i, GroupIsomorphismScheme
      ((GroupScheme.baseChange (𝒰.f i)).obj G)
      ((GroupScheme.baseChange (𝒰.f i)).obj H)) : GroupIsomorphismScheme G H := by
  apply Classical.choice
  obtain ⟨V, ⟨e⟩⟩ := LocalRepresentation.exists_representation
    (LocalGroupIso.isSheaf (G := G) (H := H) (fppfTopology S))
    𝒰 (fun i => (J i).parameter) (fun i => (J i).localRepresentationIso (𝒰.f i))
  exact ⟨ofRepresentableBy ((Functor.RepresentableBy.equivUliftYonedaIso _ _).symm e)⟩

/-- Any full global representative has the same parameter after restriction
as any supplied full local representative. -/
def localParameterIso (I : GroupIsomorphismScheme G H) {U : Scheme.{u}} (b : U ⟶ S)
    (J : GroupIsomorphismScheme
      ((GroupScheme.baseChange b).obj G) ((GroupScheme.baseChange b).obj H)) :
    (Over.pullback b).obj I.parameter ≅ J.parameter :=
  LocalRepresentation.localRepresentativeIso b I.parameter
    (Functor.RepresentableBy.equivUliftYonedaIso _ _ I.representableBy)
    J.parameter (J.localRepresentationIso b)

/-- Morphism properties local on the target can be read from full local
representatives over any base open cover. -/
theorem property_of_openCover (I : GroupIsomorphismScheme G H)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (𝒰 : Scheme.OpenCover.{u} S)
    (J : ∀ i, GroupIsomorphismScheme
      ((GroupScheme.baseChange (𝒰.f i)).obj G)
      ((GroupScheme.baseChange (𝒰.f i)).obj H))
    (hJ : ∀ i, P (J i).parameter.hom) : P I.parameter.hom :=
  LocalRepresentation.property_of_local_representations P I.parameter
    (Functor.RepresentableBy.equivUliftYonedaIso _ _ I.representableBy)
    𝒰 (fun i => (J i).parameter) (fun i => (J i).localRepresentationIso (𝒰.f i)) hJ

/-- Properties satisfying fppf target descent can be read from full local
representatives over an arbitrary étale covering family. -/
theorem property_of_etaleCover (I : GroupIsomorphismScheme G H)
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective.{u} ⊓ @Flat.{u} ⊓ @LocallyOfFinitePresentation.{u})]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (J : ∀ i, GroupIsomorphismScheme
      ((GroupScheme.baseChange (𝒰.f i)).obj G)
      ((GroupScheme.baseChange (𝒰.f i)).obj H))
    (hJ : ∀ i, P (J i).parameter.hom) : P I.parameter.hom := by
  let 𝒱 := Scheme.Cover.changeProp 𝒰
    (Q := @Flat ⊓ @LocallyOfFinitePresentation)
    (fun i => by
      have := 𝒰.map_prop i
      exact ⟨inferInstance, inferInstance⟩)
  let : P.IsLocalAtTarget (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage P
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd 𝒱.mem₀
  intro U b _ hb
  obtain ⟨i⟩ := hb
  let e := I.localParameterIso (𝒰.f i) (J i)
  change P ((Over.pullback (𝒰.f i)).obj I.parameter).hom
  rw [← Over.w e.hom, P.cancel_left_of_respectsIso]
  exact hJ i

end Langlands.GroupScheme.GroupIsomorphismScheme
