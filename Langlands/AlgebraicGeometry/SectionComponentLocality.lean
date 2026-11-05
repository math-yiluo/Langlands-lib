import Langlands.AlgebraicGeometry.SectionComponentFunctoriality
import Langlands.AlgebraicGeometry.SectionComponentOpennessStatement
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Restricting the union of fibre components to an open base -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SectionComponent

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {e : Y ⟶ X}
  {he : e ≫ f = 𝟙 Y} {f' : X' ⟶ Y'} {e' : Y' ⟶ X'}
  {he' : e' ≫ f' = 𝟙 Y'}

/-- The selected components agree whenever the actual map of residue fibres is an isomorphism. -/
theorem fiberMap_mem_connectedComponent_iff
    (g : X' ⟶ X) (b : Y' ⟶ Y) (hcomm : g ≫ f = f' ≫ b)
    (hsection : e' ≫ g = b ≫ e) (y' : Y')
    [IsIso (fiberMap g b hcomm y')] (z : f'.fiber y') :
    fiberMap g b hcomm y' z ∈ connectedComponent (fiberPoint f e he (b y')) ↔
      z ∈ connectedComponent (fiberPoint f' e' he' y') := by
  constructor
  · intro hz
    have h := (inv (fiberMap g b hcomm y')).continuous.mapsTo_connectedComponent
      (fiberPoint f e he (b y')) hz
    rw [← fiberMap_fiberPoint (he := he) (he' := he') g b hcomm hsection y'] at h
    simp only [← Scheme.Hom.comp_apply, IsIso.hom_inv_id] at h
    simpa using h
  · exact fiberMap_mem_connectedComponent g b hcomm hsection y' z

/-- In a Cartesian square over an open immersion, the map of actual residue fibres is an
isomorphism, since open immersions induce isomorphisms of residue fields. -/
theorem isIso_fiberMap_of_isPullback
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b)
    [IsOpenImmersion b] (y' : Y') : IsIso (fiberMap g b h.w y') :=
  (isPullback_fiberToSpecResidueField_of_isPullback h y').isIso_fst_of_isIso

/-- The union selected by a section commutes with restriction along an open immersion
of the base. -/
theorem preimage_componentSet_of_isPullback
    {g : X' ⟶ X} {b : Y' ⟶ Y} (h : IsPullback g f' f b)
    (hsection : e' ≫ g = b ≫ e) [IsOpenImmersion b] :
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
  rw [← hz]
  rw [← hmap, fiberι_mem_componentSet_iff, fiberι_mem_componentSet_iff]
  let := isIso_fiberMap_of_isPullback h (f' x')
  exact fiberMap_mem_connectedComponent_iff g b h.w hsection (f' x') z

variable (f e he)

/-- The actual section after an arbitrary base change. -/
def baseChangeSection (b : Y' ⟶ Y) : Y' ⟶ pullback f b :=
  pullback.lift (b ≫ e) (𝟙 _) (by simp [Category.assoc, he])

@[reassoc (attr := simp)]
theorem baseChangeSection_fst (b : Y' ⟶ Y) :
    baseChangeSection f e he b ≫ pullback.fst f b = b ≫ e :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem baseChangeSection_snd (b : Y' ⟶ Y) :
    baseChangeSection f e he b ≫ pullback.snd f b = 𝟙 _ :=
  pullback.lift_snd ..

/-- The pullback section over an open base selects exactly the preimage of the original
component union. -/
theorem preimage_componentSet_baseChange (b : Y' ⟶ Y) [IsOpenImmersion b] :
    pullback.fst f b ⁻¹' componentSet f e he =
      componentSet (pullback.snd f b) (baseChangeSection f e he b)
        (baseChangeSection_snd f e he b) :=
  preimage_componentSet_of_isPullback (.of_hasPullback f b)
    (baseChangeSection_fst f e he b)

/-- Openness of the selected-component union can be checked on any open cover of the base. -/
theorem isOpen_componentSet_iff_openCover (𝒰 : Y.OpenCover) :
    IsOpen (componentSet f e he) ↔
      ∀ i, IsOpen (componentSet (pullback.snd f (𝒰.f i))
        (baseChangeSection f e he (𝒰.f i))
        (baseChangeSection_snd f e he (𝒰.f i))) := by
  constructor
  · intro h i
    rw [← preimage_componentSet_baseChange]
    exact h.preimage (pullback.fst f (𝒰.f i)).continuous
  · intro h
    have heq : componentSet f e he =
        ⋃ i, pullback.fst f (𝒰.f i) ''
          componentSet (pullback.snd f (𝒰.f i)) (baseChangeSection f e he (𝒰.f i))
            (baseChangeSection_snd f e he (𝒰.f i)) := by
      ext x
      constructor
      · intro hx
        obtain ⟨i, z, rfl⟩ := Scheme.Cover.exists_eq (𝒰.pullback₁ f) x
        apply Set.mem_iUnion.mpr
        refine ⟨i, z, ?_, rfl⟩
        rw [← preimage_componentSet_baseChange]
        exact hx
      · intro hx
        obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
        rw [← preimage_componentSet_baseChange] at hz
        exact hz
    rw [heq]
    exact isOpen_iUnion fun i =>
      (pullback.fst f (𝒰.f i)).isOpenEmbedding.isOpenMap _ (h i)

/-- The affine-base specialization of the finite-presentation openness theorem. -/
def AffineBaseOpennessStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X : Scheme.{u}) (f : X ⟶ Spec R)
    (e : Spec R ⟶ X) (he : e ≫ f = 𝟙 (Spec R)),
    Flat f → LocallyOfFinitePresentation f → QuasiCompact f → QuasiSeparated f →
      GeometricallyReduced f → IsOpen (componentSet f e he)

/-- The exact arbitrary-base target is equivalent to its affine-base specialization. -/
theorem flatFinitePresentationOpenness_iff_affineBase :
    FlatFinitePresentationOpennessStatement.{u} ↔ AffineBaseOpennessStatement.{u} := by
  constructor
  · intro h R X f e he
    exact h X (Spec R) f e he
  · intro h X Y f e he hflat hlfp hqc hqs hgr
    let := hflat
    let := hlfp
    let := hqc
    let := hqs
    let := hgr
    rw [isOpen_componentSet_iff_openCover f e he Y.affineCover]
    intro i
    exact h _ _ _ _ _ inferInstance inferInstance inferInstance inferInstance inferInstance

end Langlands.AlgebraicGeometry.SectionComponent
