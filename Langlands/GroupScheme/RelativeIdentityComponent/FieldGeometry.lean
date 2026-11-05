import Langlands.GroupScheme.RelativeIdentityComponent.OpenGeometry
import Langlands.AlgebraicGeometry.LocallyNoetherianComponentSchemes

/-! # Identity-component geometry over fields without affineness -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeIdentityComponent

open Langlands.AlgebraicGeometry
open Langlands.GroupScheme.FiniteEtaleImage (liftOver)

variable {k : Type u} [Field k] (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom]

/-- The raw connected-component restriction at the unit of a smooth field group,
without any affineness assumption. -/
def fieldIdentityOver : Over (Spec (CommRingCat.of k)) := by
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  exact Over.mk (componentι H.X.left (.mk (IdentityComponent.identityPoint H)) ≫ H.X.hom)

/-- Inclusion of the raw field identity restriction into the ambient group. -/
def fieldIdentityInclusion : fieldIdentityOver H ⟶ H.X := by
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  exact Over.homMk (componentι H.X.left (.mk (IdentityComponent.identityPoint H)))

instance : IsOpenImmersion (fieldIdentityInclusion H).left := by
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  exact inferInstanceAs
    (IsOpenImmersion (componentι H.X.left (.mk (IdentityComponent.identityPoint H))))

theorem range_fieldIdentityInclusion :
    Set.range (fieldIdentityInclusion H).left = IdentityComponent.identitySet H := by
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  exact (Scheme.Opens.range_ι _).trans
    (componentOpen_mk H.X.left (IdentityComponent.identityPoint H))

instance fieldIdentityOver_connectedSpace : ConnectedSpace (fieldIdentityOver H).left := by
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  exact inferInstanceAs
    (ConnectedSpace (componentScheme H.X.left (.mk (IdentityComponent.identityPoint H))))

instance : Smooth (fieldIdentityOver H).hom := by
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  exact inferInstanceAs
    (Smooth (componentι H.X.left (.mk (IdentityComponent.identityPoint H)) ≫ H.X.hom))

/-- The raw field identity restriction is integral. -/
theorem fieldIdentityOver_isIntegral : IsIntegral (fieldIdentityOver H).left :=
  P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.isIntegral_of_smooth_of_connectedSpace (fieldIdentityOver H).hom

/-- The raw field identity restriction is irreducible. -/
theorem fieldIdentityOver_irreducibleSpace : IrreducibleSpace (fieldIdentityOver H).left :=
  irreducibleSpace_of_smooth_connected (fieldIdentityOver H).hom

/-- A smooth field group's identity component is irreducible as a subset,
without relative openness or affineness assumptions. -/
theorem isIrreducible_identitySet : IsIrreducible (IdentityComponent.identitySet H) := by
  have := fieldIdentityOver_irreducibleSpace H
  rw [← range_fieldIdentityInclusion H]
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (fieldIdentityOver H).left).image
      (fieldIdentityInclusion H).left (fieldIdentityInclusion H).left.continuous.continuousOn

/-- The unit section factors through the raw field identity restriction. -/
def fieldIdentityOne : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ fieldIdentityOver H :=
  liftOver (fieldIdentityInclusion H) η[H.X] (by
    rw [range_fieldIdentityInclusion]
    rintro _ ⟨x, rfl⟩
    rw [IdentityComponent.unit_left_apply]
    exact mem_connectedComponent)

instance fieldIdentityOver_geometricallyConnected :
    GeometricallyConnected (fieldIdentityOver H).hom :=
  geometricallyConnected_of_smooth_connected_section (fieldIdentityOver H).hom
    (fieldIdentityOne H).left (Over.w (fieldIdentityOne H))

/-- Every residue-fibre identity component of a smooth relative group is
irreducible, before establishing openness of their total union. -/
theorem isIrreducible_residueIdentitySet {S : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] (s : S) :
    IsIrreducible (IdentityComponent.identitySet (residueFiber G s)) := by
  have : Smooth (residueFiber G s).X.hom :=
    inferInstanceAs (Smooth (pullback.snd G.X.hom (S.fromSpecResidueField s)))
  exact isIrreducible_identitySet (residueFiber G s)

end Langlands.GroupScheme.RelativeIdentityComponent
