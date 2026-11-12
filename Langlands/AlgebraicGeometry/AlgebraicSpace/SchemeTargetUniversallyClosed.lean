import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeTargetConnectedFibres
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineTargetFamily
import Langlands.AlgebraicGeometry.AlgebraicSpace.UniversallyClosedTargetAtlas
import Langlands.AlgebraicGeometry.AlgebraicSpace.TopologicalMorphismBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteTypeMorphismAtlas

/-! # Universal closedness after rebasing to a represented target -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Separatedness is preserved in an actual cartesian square of spaces. -/
theorem IsSeparatedMorphism.of_isPullback
    {S : Scheme.{u}} {X' Y' X Y : AlgebraicSpace S}
    {a : X' ⟶ X} {p : X' ⟶ Y'} {f : X ⟶ Y} {b : Y' ⟶ Y}
    (h : IsPullback (hom a) (hom p) (hom f) (hom b))
    (hf : IsSeparatedMorphism f) : IsSeparatedMorphism p := by
  let P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (Over.forget S)).relative (schemeYoneda S)
  have : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
  have : P.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  exact P.diagonal.of_isPullback h hf

namespace SchemeTargetRebase

variable {S : Scheme.{u}} {V : Over S} {X : AlgebraicSpace S}
    (f : X ⟶ (schemeToSpace S).obj V)

/-- The fibre topology comparison keeps projection to the same underlying test scheme. -/
theorem fibrePointsHomeomorph_snd {U : Over V.left}
    (y : (schemeYoneda V.left).obj U ⟶
      (schemeYoneda V.left).obj (Over.mk (𝟙 V.left)))
    (x : Points (Limits.pullback (hom (structuralMorphism (space f))) y)) :
    Points.map (pullback.snd (hom f) (originalBaseChart V.hom (y ≫ sectionMap V)))
      (fibrePointsHomeomorph f y x) =
      forgetBaseSchemePointsHomeomorph V.hom U
        (Points.map (pullback.snd (hom (structuralMorphism (space f))) y) x) := by
  change Points.map _ (fibreRestrictionPointsHomeomorph V.hom f (y ≫ sectionMap V)
    (Points.map (iteratedFibrePullbackIso (structuralSquare f) y).hom x)) = _
  rw [fibreRestrictionPointsHomeomorph_snd]
  congr 1
  rw [← Points.map_comp]
  exact congrArg (fun k => Points.map k x)
    ((IsPullback.of_hasPullback (hom (structuralMorphism (space f))) y).paste_horiz
      (structuralSquare f)).isoPullback_hom_snd

/-- Recover the original test's point topology from the same scheme over the new base. -/
def testSchemePointsHomeomorph {U : Over S} (t : U ⟶ V) :
    @Homeomorph (Points ((schemeYoneda V.left).obj (Over.mk t.left)))
      (Points ((schemeYoneda S).obj U)) (pointTopology _) (pointTopology _) := by
  let := pointTopology ((schemeYoneda V.left).obj (Over.mk t.left))
  let := pointTopology ((schemeYoneda S).obj ((Over.map V.hom).obj (Over.mk t.left)))
  let := pointTopology ((schemeYoneda S).obj U)
  exact (forgetBaseSchemePointsHomeomorph V.hom (Over.mk t.left)).trans
    (Points.isoHomeomorph ((schemeYoneda S).mapIso (testBaseIso t)))

/-- The rebased structural fibre and the original fibre over a represented test agree. -/
def testFibrePointsHomeomorph {U : Over S} (t : U ⟶ V) :
    @Homeomorph
      (Points (Limits.pullback (hom (structuralMorphism (space f)))
        ((schemeYoneda V.left).map (baseTest t.left))))
      (Points (Limits.pullback (hom f) ((schemeYoneda S).map t)))
      (pointTopology _) (pointTopology _) := by
  let y := (schemeYoneda V.left).map (baseTest t.left)
  let e₀ := pullback.congrHom (f₁ := hom f) rfl (originalBaseChart_baseTest t.left)
  let := pointTopology (Limits.pullback (hom (structuralMorphism (space f))) y)
  let := pointTopology (Limits.pullback (hom f) (originalBaseChart V.hom (y ≫ sectionMap V)))
  let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map (originalTest t.left)))
  let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map t))
  exact (fibrePointsHomeomorph f y).trans
    ((Points.isoHomeomorph e₀).trans (Points.isoHomeomorph (originalTestFibreIso f t)))

/-- The recovered fibre comparison is a comparison over the recovered test scheme. -/
theorem testFibrePointsHomeomorph_snd {U : Over S} (t : U ⟶ V)
    (x : Points (Limits.pullback (hom (structuralMorphism (space f)))
      ((schemeYoneda V.left).map (baseTest t.left)))) :
    Points.map (pullback.snd (hom f) ((schemeYoneda S).map t))
      (testFibrePointsHomeomorph f t x) =
      testSchemePointsHomeomorph t
        (Points.map (pullback.snd (hom (structuralMorphism (space f)))
          ((schemeYoneda V.left).map (baseTest t.left))) x) := by
  let y := (schemeYoneda V.left).map (baseTest t.left)
  let e₀ := pullback.congrHom (f₁ := hom f) rfl (originalBaseChart_baseTest t.left)
  have h₁ : (originalTestFibreIso f t).hom ≫
      pullback.snd (hom f) ((schemeYoneda S).map t) =
      pullback.snd (hom f) ((schemeYoneda S).map (originalTest t.left)) ≫
        (schemeYoneda S).map (testBaseIso t).hom := by
    simp [originalTestFibreIso, pullback.map]
  have h₀ : e₀.hom ≫
      pullback.snd (hom f) ((schemeYoneda S).map (originalTest t.left)) =
      pullback.snd (hom f) (originalBaseChart V.hom (y ≫ sectionMap V)) := by
    simp only [e₀, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
      Category.comp_id]
    rfl
  have hx₀ : Points.map
      (pullback.snd (hom f) ((schemeYoneda S).map (originalTest t.left)))
      (Points.map e₀.hom (fibrePointsHomeomorph f y x)) =
      forgetBaseSchemePointsHomeomorph V.hom (Over.mk t.left)
        (Points.map (pullback.snd (hom (structuralMorphism (space f))) y) x) := by
    erw [← Points.map_comp, h₀]
    exact fibrePointsHomeomorph_snd f y x
  change Points.map _ (Points.map (originalTestFibreIso f t).hom
    (Points.map e₀.hom (fibrePointsHomeomorph f y x))) =
      Points.map ((schemeYoneda S).map (testBaseIso t).hom)
        (forgetBaseSchemePointsHomeomorph V.hom (Over.mk t.left)
          (Points.map (pullback.snd (hom (structuralMorphism (space f))) y) x))
  erw [← Points.map_comp, h₁, Points.map_comp]
  exact congrArg (Points.map ((schemeYoneda S).map (testBaseIso t).hom)) hx₀

/-- Universal closedness agrees before and after rebasing to the represented target. -/
theorem isUniversallyClosedMorphism_iff :
    IsUniversallyClosedMorphism f ↔
      IsUniversallyClosedMorphism (structuralMorphism (space f)) := by
  constructor
  · intro hf
    exact IsUniversallyClosedMorphism.of_isPullback
      (a := FibreProduct.fst (baseChangeMap V.hom f) (sectionMorphism V))
      (b := sectionMorphism V) (structuralSquare f) (hf.baseChangeMap (g := V.hom))
  · intro hf U y
    obtain ⟨t, rfl⟩ := (schemeYoneda S).map_surjective y
    let y' := (schemeYoneda V.left).map (baseTest t.left)
    let := pointTopology (Limits.pullback (hom (structuralMorphism (space f))) y')
    let := pointTopology (Limits.pullback (hom f) ((schemeYoneda S).map t))
    let := pointTopology ((schemeYoneda V.left).obj (Over.mk t.left))
    let := pointTopology ((schemeYoneda S).obj U)
    let eF := testFibrePointsHomeomorph f t
    let eU := testSchemePointsHomeomorph t
    have h := eU.isClosedMap.comp ((hf (Over.mk t.left) y').comp eF.symm.isClosedMap)
    have he : eU ∘ Points.map (pullback.snd (hom (structuralMorphism (space f))) y') ∘
        eF.symm = Points.map (pullback.snd (hom f) ((schemeYoneda S).map t)) := by
      funext z
      change eU (Points.map _ (eF.symm z)) = _
      rw [← testFibrePointsHomeomorph_snd]
      exact congrArg (Points.map _) (eF.apply_symm_apply z)
    rwa [he] at h

/-- Separatedness of the original morphism passes to the actual rebased structural map. -/
theorem isSeparatedMorphism (hf : IsSeparatedMorphism f) :
    IsSeparatedMorphism (structuralMorphism (space f)) := by
  let P := (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (Over.forget V.left)).relative (schemeYoneda V.left)
  have : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
      (Over.forget V.left)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
  have : P.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  exact P.diagonal.of_isPullback (structuralSquare f) hf.baseChangeMap

/-- Properness passes to the rebased structural morphism under the finite-presentation
atlas hypotheses used by the host theorem. -/
theorem isProperMorphism [IsAffine S] [IsAffine V.left] [LocallyOfFiniteType V.hom]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hf : IsProperMorphism f) : IsProperMorphism (structuralMorphism (space f)) := by
  have : LocallyOfFinitePresentation (Over.mk (𝟙 V.left)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 V.left))
  have : QuasiCompact (Over.mk (𝟙 V.left)).hom :=
    inferInstanceAs (QuasiCompact (𝟙 V.left))
  have : QuasiSeparated (Over.mk (𝟙 V.left)).hom :=
    inferInstanceAs (QuasiSeparated (𝟙 V.left))
  apply (isProperMorphism_iff_separated_universallyClosed
    (hasAtlasProperty_finitePresentation f hX)
    (HasAtlasProperty.of_scheme (Over.mk (𝟙 V.left)) ⟨inferInstance, inferInstance⟩)
    (isQuasiSeparated_schemeToSpace (Over.mk (𝟙 V.left))) _).mpr
  exact ⟨isSeparatedMorphism f hf.1, (isUniversallyClosedMorphism_iff f).mp hf.2.2.2⟩

end SchemeTargetRebase

namespace AffineTargetFamily

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : (schemeYoneda S).obj V ⟶ Y.presheaf)

/-- A target-atlas family tests exactly the universal closedness of the original map. -/
theorem isUniversallyClosedMorphism_iff (hb : IsEtale b) (hs : IsSurjective b) :
    IsUniversallyClosedMorphism f ↔
      IsUniversallyClosedMorphism (structuralMorphism (space f b)) :=
  (isUniversallyClosedMorphism_iff_targetAtlas f b hb hs).trans
    (SchemeTargetRebase.isUniversallyClosedMorphism_iff _)

/-- A proper morphism gives a proper structural family over an affine target chart. -/
theorem isProperMorphism_structural [IsAffine S] [IsAffine V.left]
    [LocallyOfFinitePresentation V.hom]
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (hf : IsProperMorphism f) :
    IsProperMorphism (structuralMorphism (space f b)) := by
  let p := FibreProduct.snd f (homMk b : (schemeToSpace S).obj V ⟶ Y)
  have hpS : IsSeparatedMorphism p := IsSeparatedMorphism.of_isPullback
    (FibreProduct.isPullback_presheaf f (homMk b : (schemeToSpace S).obj V ⟶ Y)) hf.1
  have hpU : IsUniversallyClosedMorphism p := IsUniversallyClosedMorphism.of_isPullback
    (FibreProduct.isPullback_presheaf f (homMk b : (schemeToSpace S).obj V ⟶ Y)) hf.2.2.2
  have : LocallyOfFinitePresentation (Over.mk (𝟙 V.left)).hom :=
    inferInstanceAs (LocallyOfFinitePresentation (𝟙 V.left))
  have : QuasiCompact (Over.mk (𝟙 V.left)).hom :=
    inferInstanceAs (QuasiCompact (𝟙 V.left))
  have : QuasiSeparated (Over.mk (𝟙 V.left)).hom :=
    inferInstanceAs (QuasiSeparated (𝟙 V.left))
  apply (isProperMorphism_iff_separated_universallyClosed
    (hasAtlasProperty_finitePresentation f b hX hY hYqs)
    (HasAtlasProperty.of_scheme (Over.mk (𝟙 V.left)) ⟨inferInstance, inferInstance⟩)
    (isQuasiSeparated_schemeToSpace (Over.mk (𝟙 V.left))) _).mpr
  exact ⟨SchemeTargetRebase.isSeparatedMorphism p hpS,
    (SchemeTargetRebase.isUniversallyClosedMorphism_iff p).mp hpU⟩

end AffineTargetFamily

end Langlands.AlgebraicGeometry.AlgebraicSpace
