import Langlands.AlgebraicGeometry.SectionComponent

/-! # Functoriality of fibre components selected by sections -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SectionComponent

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {e : Y ⟶ X}
  {he : e ≫ f = 𝟙 Y} {f' : X' ⟶ Y'} {e' : Y' ⟶ X'}
  {he' : e' ≫ f' = 𝟙 Y'}
  (g : X' ⟶ X) (b : Y' ⟶ Y) (hcomm : g ≫ f = f' ≫ b)

/-- The actual map of residue fibres in a commuting square. -/
def fiberMap (y' : Y') : f'.fiber y' ⟶ f.fiber (b y') :=
  pullback.map _ _ _ _ g (Spec.map (b.residueFieldMap y')) b hcomm.symm (by simp)

@[reassoc (attr := simp)]
theorem fiberMap_fiberι (y' : Y') :
    fiberMap g b hcomm y' ≫ f.fiberι (b y') = f'.fiberι y' ≫ g := by
  dsimp [fiberMap, Scheme.Hom.fiberι, pullback.map]
  exact pullback.lift_fst _ _ _

variable (hsection : e' ≫ g = b ≫ e)

include hsection

/-- A map respecting the sections sends the selected residue-fibre point
into the selected residue-fibre point. -/
theorem fiberMap_fiberPoint (y' : Y') :
    fiberMap g b hcomm y' (fiberPoint f' e' he' y') =
      fiberPoint f e he (b y') := by
  apply (f.fiberι (b y')).isEmbedding.injective
  change (fiberMap g b hcomm y' ≫ f.fiberι (b y')) _ = _
  rw [fiberMap_fiberι, Scheme.Hom.comp_apply, fiberι_fiberPoint, fiberι_fiberPoint]
  change (e' ≫ g) y' = (b ≫ e) y'
  rw [hsection]

/-- Every point of the selected fibre component maps to the selected component. -/
theorem fiberMap_mem_connectedComponent (y' : Y') (z : f'.fiber y')
    (hz : z ∈ connectedComponent (fiberPoint f' e' he' y')) :
    fiberMap g b hcomm y' z ∈ connectedComponent (fiberPoint f e he (b y')) := by
  have h := (fiberMap g b hcomm y').continuous.mapsTo_connectedComponent
    (fiberPoint f' e' he' y') hz
  rwa [fiberMap_fiberPoint g b hcomm hsection] at h

include b hcomm

/-- A morphism respecting structure maps and sections sends the relative
union of selected fibre components into the corresponding union. -/
theorem image_componentSet_subset :
    g '' componentSet f' e' he' ⊆ componentSet f e he := by
  rintro _ ⟨x', ⟨y', z, hz, rfl⟩, rfl⟩
  refine ⟨b y', fiberMap g b hcomm y' z,
    fiberMap_mem_connectedComponent g b hcomm hsection y' z hz, ?_⟩
  exact congrArg (fun q : f'.fiber y' ⟶ X => q z)
    (fiberMap_fiberι g b hcomm y')

end Langlands.AlgebraicGeometry.SectionComponent
