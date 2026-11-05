import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry
import Langlands.AlgebraicGeometry.SectionComponentFunctoriality

/-! # Base change of the actual components selected by a section -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Scalar extension preserves the full connected component through a rational point. -/
theorem preimage_connectedComponent_of_field_isPullback
    {k K : Type u} [Field k] [Field K]
    {X X' : Scheme.{u}} [IsLocallyNoetherian X]
    {f : X ⟶ Spec (CommRingCat.of k)}
    {f' : X' ⟶ Spec (CommRingCat.of K)}
    {a : X' ⟶ X} {b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)}
    (h : IsPullback a f' f b)
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ f = 𝟙 _)
    (x' : X') (hx' : a x' = e (IsLocalRing.closedPoint k)) :
    a ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent x' := by
  let U := connectedComponentOpen X (e (IsLocalRing.closedPoint k))
  have hgc : GeometricallyConnected (U.ι ≫ f) :=
    geometricallyConnected_connectedComponentOpen f e he
  have hrect := (IsPullback.of_hasPullback U.ι a).flip.paste_horiz h.flip
  have : GeometricallyConnected (pullback.snd U.ι a ≫ f') :=
    MorphismProperty.of_isPullback hrect.flip hgc
  have : ConnectedSpace ↥(pullback U.ι a) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd U.ι a ≫ f')
  have hconn : _root_.IsConnected
      (a ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k))) := by
    change _root_.IsConnected (a ⁻¹' (U : Set X))
    rw [← Scheme.Opens.range_ι U, ← Scheme.Pullback.range_snd, ← Set.image_univ]
    exact isConnected_univ.image _ (pullback.snd U.ι a).continuous.continuousOn
  apply Set.Subset.antisymm
  · apply hconn.subset_connectedComponent
    change a x' ∈ connectedComponent (e (IsLocalRing.closedPoint k))
    rw [hx']
    exact mem_connectedComponent
  · intro z hz
    have hz' := a.continuous.mapsTo_connectedComponent x' hz
    change a z ∈ connectedComponent (e (IsLocalRing.closedPoint k))
    simpa only [hx'] using hz'

namespace SectionComponent

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {e : Y ⟶ X}
  {he : e ≫ f = 𝟙 Y} {f' : X' ⟶ Y'} {e' : Y' ⟶ X'}
  {he' : e' ≫ f' = 𝟙 Y'}

/-- In any Cartesian square, the selected fibre component is exactly the inverse image
of the selected component over the original residue field. -/
theorem preimage_fiberComponent_of_isPullback [LocallyOfFiniteType f]
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b)
    (hsection : e' ≫ g = b ≫ e) (y' : Y') :
    fiberMap g b h.w y' ⁻¹' connectedComponent (fiberPoint f e he (b y')) =
      connectedComponent (fiberPoint f' e' he' y') := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField (b y')) :=
    MorphismProperty.pullback_snd f (Y.fromSpecResidueField (b y')) inferInstance
  let := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (b y'))
  exact preimage_connectedComponent_of_field_isPullback
    (isPullback_fiberToSpecResidueField_of_isPullback h y')
    (fiberSection f e he (b y')) (fiberSection_toSpec f e he (b y'))
    (fiberPoint f' e' he' y') (fiberMap_fiberPoint g b h.w hsection y')

/-- The union selected by a section commutes with arbitrary base change. -/
theorem preimage_componentSet_of_isPullback_locallyOfFiniteType [LocallyOfFiniteType f]
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b)
    (hsection : e' ≫ g = b ≫ e) :
    g ⁻¹' componentSet f e he = componentSet f' e' he' := by
  ext x'
  have hx : x' ∈ Set.range (f'.fiberι (f' x')) := by
    rw [Scheme.Hom.range_fiberι]
    rfl
  obtain ⟨z, hz⟩ := hx
  have hmap := congrArg (fun q : f'.fiber (f' x') ⟶ X => q z)
    (fiberMap_fiberι g b h.w (f' x'))
  change f.fiberι (b (f' x')) (fiberMap g b h.w (f' x') z) =
    g (f'.fiberι (f' x') z) at hmap
  change g x' ∈ componentSet f e he ↔ x' ∈ componentSet f' e' he'
  rw [← hz, ← hmap, fiberι_mem_componentSet_iff, fiberι_mem_componentSet_iff]
  exact Set.ext_iff.mp (preimage_fiberComponent_of_isPullback h hsection (f' x')) z

/-- The actual selected component in a new residue fibre is the pullback of the
original selected open component along the actual residue-fibre comparison. -/
def fiberComponentBaseChangeIso [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b)
    (hsection : e' ≫ g = b ≫ e) (y' : Y') :
    (fiberComponentOpen f' e' he' y').toScheme ≅
      pullback (fiberComponentOpen f e he (b y')).ι (fiberMap g b h.w y') :=
  IsOpenImmersion.isoOfRangeEq (fiberComponentOpen f' e' he' y').ι
    (pullback.snd (fiberComponentOpen f e he (b y')).ι (fiberMap g b h.w y')) (by
      rw [Scheme.Opens.range_ι, Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
      exact (preimage_fiberComponent_of_isPullback h hsection y').symm)

@[reassoc (attr := simp)]
theorem fiberComponentBaseChangeIso_hom_snd
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b)
    (hsection : e' ≫ g = b ≫ e) (y' : Y') :
    (fiberComponentBaseChangeIso h hsection y').hom ≫
        pullback.snd (fiberComponentOpen f e he (b y')).ι (fiberMap g b h.w y') =
      (fiberComponentOpen f' e' he' y').ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

end SectionComponent

end Langlands.AlgebraicGeometry
