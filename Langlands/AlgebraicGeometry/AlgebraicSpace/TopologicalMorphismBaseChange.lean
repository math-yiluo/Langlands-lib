import Langlands.AlgebraicGeometry.AlgebraicSpace.FibreRestrictionTopology

/-! # Base change of topological morphism properties of algebraic spaces -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} {g : T ⟶ S} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

/-- Choose an actual compact scheme atlas of the fibre after changing the base. -/
def compactFibreAtlasBaseChange (hf : IsQuasiCompactMorphism f)
    (V : Over T) (hV : IsAffine V.left)
    (y : (schemeYoneda T).obj V ⟶ (baseChange g Y).presheaf) :
    {a : FibreRestrictionAtlas g (hom f) y // CompactSpace a.source.left} :=
  Classical.choice (by
    obtain ⟨W, b, hW, hbe, hbs⟩ := hf ((Over.map g).obj V) hV (originalBaseChart g y)
    let a := FibreRestrictionAtlas.of_original g (hom f) y b hbe hbs
    refine ⟨⟨a, ?_⟩⟩
    change CompactSpace W.left
    exact hW)

/-- Compact fibre atlases stay compact when only their scheme base is changed. -/
theorem IsQuasiCompactMorphism.baseChangeMap (hf : IsQuasiCompactMorphism f) :
    IsQuasiCompactMorphism (AlgebraicSpace.baseChangeMap g f) := by
  intro V hV y
  let a := compactFibreAtlasBaseChange hf V hV y
  exact ⟨a.val.source, a.val.map, a.property, a.val.etale, a.val.surjective⟩

/-- Universal closedness is preserved under arbitrary change of scheme base. -/
theorem IsUniversallyClosedMorphism.baseChangeMap (hf : IsUniversallyClosedMorphism f) :
    IsUniversallyClosedMorphism (AlgebraicSpace.baseChangeMap g f) := by
  intro V y
  let := pointTopology (Limits.pullback (hom (AlgebraicSpace.baseChangeMap g f)) y)
  let := pointTopology (Limits.pullback (hom f) (originalBaseChart g y))
  let := pointTopology ((schemeYoneda T).obj V)
  let := pointTopology ((schemeYoneda S).obj ((Over.map g).obj V))
  let eF := fibreRestrictionPointsHomeomorph g f y
  let eV := forgetBaseSchemePointsHomeomorph g V
  have h := eV.symm.isClosedMap.comp
    ((hf ((Over.map g).obj V) (originalBaseChart g y)).comp eF.isClosedMap)
  have he : eV.symm ∘ Points.map (Limits.pullback.snd (hom f) (originalBaseChart g y)) ∘ eF =
      Points.map (Limits.pullback.snd (hom (AlgebraicSpace.baseChangeMap g f)) y) := by
    funext x
    change eV.symm (Points.map (Limits.pullback.snd (hom f) (originalBaseChart g y)) (eF x)) = _
    rw [fibreRestrictionPointsHomeomorph_snd]
    exact eV.symm_apply_apply _
  rwa [he] at h

/-- Nonempty geometrically connected fibres are preserved under arbitrary
change of scheme base. -/
theorem HasGeometricallyConnectedFibres.baseChangeMap (hf : HasGeometricallyConnectedFibres f) :
    HasGeometricallyConnectedFibres (AlgebraicSpace.baseChangeMap g f) := by
  intro K _ s y
  let := pointTopology (Limits.pullback (hom (AlgebraicSpace.baseChangeMap g f)) y)
  let := pointTopology (Limits.pullback (hom f) (originalBaseChart g y))
  exact (fibreRestrictionPointsHomeomorph g f y).connectedSpace_iff.mpr
    (hf K (s ≫ g) (originalBaseChart g y))

/-- Properness is preserved under arbitrary change of scheme base. -/
theorem IsProperMorphism.baseChangeMap (hf : IsProperMorphism f) :
    IsProperMorphism (AlgebraicSpace.baseChangeMap g f) :=
  ⟨hf.1.baseChangeMap, hf.2.1.baseChangeMap, hf.2.2.1.baseChangeMap,
    hf.2.2.2.baseChangeMap⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
