import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeStageModel
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProperSchemeCoverStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedSurjectivityLimitDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.UniversallyClosedSourceCover

/-! # Descending a supplied proper scheme cover to an actual affine stage -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredPoints
open Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitUniqueness

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- An actual proper finitely presented scheme cover of a stage's base-changed space. -/
structure ProperSchemeCoverAtStage
    {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u})
    {S : Scheme.{u}} (t : D ⟶ (Functor.const I).obj S) (X : AlgebraicSpace S) where
  index : I
  source : Over (D.obj index)
  map : (schemeYoneda (D.obj index)).obj source ⟶ (baseChange (t.app index) X).presheaf
  surjective : IsSurjective map
  proper : _root_.AlgebraicGeometry.IsProper source.hom
  locallyOfFinitePresentation : LocallyOfFinitePresentation source.hom

/-- A morphism from a space isomorphic to an actual scheme is represented over every target. -/
theorem isRepresentableMorphism_of_sourceIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : Over S) (e : (schemeToSpace S).obj U ≅ X) (f : X ⟶ Y) :
    IsRepresentableMorphism (hom f) := by
  have h := Y.representable_from_scheme (hom e.hom ≫ hom f)
  exact (MorphismProperty.cancel_left_of_respectsIso
    (schemeYoneda S).relativelyRepresentable (hom e.hom) (hom f)).mp h

/-- A given proper finitely presented scheme cover of the limit space descends to
an actual original stage, including eventual geometric surjectivity of its map. -/
theorem exists_properSchemeCoverAtStage_of_limit_cover
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    {S : Scheme.{u}} [IsAffine S] (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (X : AlgebraicSpace S) (hXqs : IsQuasiSeparated X)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (U : Over c.pt) (a : (schemeYoneda c.pt).obj U ⟶ (baseChange p X).presheaf)
    (ha : IsSurjective a) (hUp : _root_.AlgebraicGeometry.IsProper U.hom)
    (hUl : LocallyOfFinitePresentation U.hom) :
    Nonempty (ProperSchemeCoverAtStage D t X) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let := hUp
  let := hUl
  obtain ⟨m⟩ := exists_properSchemeStageModel D c hc U.left U.hom hUp
  let i := m.index
  let Z := (schemeToSpace (D.obj i)).obj m.schemeOver
  let Xi := baseChange (t.app i) X
  have : LocallyOfFinitePresentation m.schemeOver.hom := m.locallyOfFinitePresentation
  have : _root_.AlgebraicGeometry.IsProper m.schemeOver.hom := m.proper
  have : LocallyOfFinitePresentation m.structureMap := m.locallyOfFinitePresentation
  have : _root_.AlgebraicGeometry.IsProper m.structureMap := m.proper
  have hZqs : IsQuasiSeparated Z := isQuasiSeparated_schemeToSpace m.schemeOver
  have hZ : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Z :=
    HasAtlasProperty.of_scheme m.schemeOver ⟨inferInstance, inferInstance⟩
  have hXiqs : IsQuasiSeparated Xi := hXqs.baseChange
  have hXi : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Xi :=
    hX.baseChange
  let eX := (baseChangeCompNatIso (t.app i) (c.π.app i) p (hp i)).app X
  let φ : baseChange (c.π.app i) Z ⟶ baseChange (c.π.app i) Xi :=
    m.spaceIso.inv ≫ homMk a ≫ eX.inv
  let R := (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget c.pt)).relative
    (schemeYoneda c.pt)
  have hφS : IsSurjective (hom φ) := by
    change R (hom m.spaceIso.inv ≫ (a ≫ hom eX.inv))
    apply (MorphismProperty.cancel_left_of_respectsIso R _ _).mpr
    exact ha.comp_iso ((forgetToPresheaf c.pt).mapIso eX.symm)
  have (j : Over i) : IsAffine ((overDiagram D i).obj j) := by
    change IsAffine (D.obj j.left)
    infer_instance
  obtain ⟨j, b, hb⟩ := exists_rebase_map (overDiagram D i) (overStructure D i)
    (c.whisker (Over.forget i)) (overConeIsLimit i c hc) (c.π.app i)
    (overCone_π_comp i c) hZqs (hZ.mono (fun _ _ _ h => h.2))
    (hXi.mono (fun _ _ _ h => h.1)) φ
  have hb' : rebase (Over.homMk (c.π.app j.left) (c.w j.hom) :
      Over.mk (c.π.app i) ⟶ Over.mk (D.map j.hom)) b = φ := hb
  have hlim : IsSurjective (hom (baseChangeMap (c.π.app j.left) b)) := by
    have h := hφS
    rw [← hb'] at h
    change R (hom (BaseChangeComparison.compIso (D.map j.hom) (c.π.app j.left)
        (c.π.app i) (c.w j.hom) Z).inv ≫
      (hom (baseChangeMap (c.π.app j.left) b) ≫
        hom (BaseChangeComparison.compIso (D.map j.hom) (c.π.app j.left)
          (c.π.app i) (c.w j.hom) Xi).hom)) at h
    rw [MorphismProperty.cancel_left_of_respectsIso R,
      MorphismProperty.cancel_right_of_respectsIso R] at h
    exact h
  let Uj := (Over.pullback (D.map j.hom)).obj m.schemeOver
  let ej := baseChangeSchemeIso (D.map j.hom) m.schemeOver
  have hbj : IsRepresentableMorphism (hom b) :=
    isRepresentableMorphism_of_sourceIso Uj ej b
  obtain ⟨k, r, hks⟩ :=
    (isSurjective_limit_iff_of_representable D c hc j.left
      (hZqs.baseChange (g := D.map j.hom)) (hZ.baseChange (g := D.map j.hom))
      (hXiqs.baseChange (g := D.map j.hom)) (hXi.baseChange (g := D.map j.hom)) b hbj).mp hlim
  let Uk := (Over.pullback (D.map r)).obj Uj
  let eU : (schemeToSpace (D.obj k)).obj Uk ≅
      baseChange (D.map r) (baseChange (D.map j.hom) Z) :=
    baseChangeSchemeIso (D.map r) Uj ≪≫ (baseChangeFunctor (D.map r)).mapIso ej
  have hw : D.map (r ≫ j.hom) ≫ t.app i = t.app k := by
    have h := t.naturality (r ≫ j.hom)
    change D.map (r ≫ j.hom) ≫ t.app i = t.app k ≫ 𝟙 S at h
    exact h.trans (Category.comp_id (t.app k))
  let eY : baseChange (D.map r) (baseChange (D.map j.hom) Xi) ≅
      baseChange (t.app k) X :=
    (baseChangeCompNatIso (D.map j.hom) (D.map r) (D.map (r ≫ j.hom))
      (D.map_comp r j.hom).symm).app Xi ≪≫
        (baseChangeCompNatIso (t.app i) (D.map (r ≫ j.hom)) (t.app k) hw).app X
  let ak : (schemeToSpace (D.obj k)).obj Uk ⟶ baseChange (t.app k) X :=
    eU.hom ≫ baseChangeMap (D.map r) b ≫ eY.hom
  have hak : IsSurjective (hom ak) := by
    change ((MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget (D.obj k))).relative
      (schemeYoneda (D.obj k)))
      (hom eU.hom ≫ (hom (baseChangeMap (D.map r) b) ≫ hom eY.hom))
    apply (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr
    exact hks.comp_iso ((forgetToPresheaf (D.obj k)).mapIso eY)
  have : _root_.AlgebraicGeometry.IsProper Uj.hom := by
    change _root_.AlgebraicGeometry.IsProper (pullback.snd m.structureMap (D.map j.hom))
    infer_instance
  have : LocallyOfFinitePresentation Uj.hom := by
    change LocallyOfFinitePresentation (pullback.snd m.structureMap (D.map j.hom))
    infer_instance
  refine ⟨⟨k, Uk, hom ak, hak, ?_, ?_⟩⟩
  · change _root_.AlgebraicGeometry.IsProper (pullback.snd Uj.hom (D.map r))
    infer_instance
  · change LocallyOfFinitePresentation (pullback.snd Uj.hom (D.map r))
    infer_instance

/-- The independent scheme-cover existence statement reduces eventual structural
universal closedness to descent of a supplied proper scheme cover. -/
theorem exists_structuralUniversallyClosed_of_properSchemeCover
    (hcover : ProperSchemeCoverStatement.{u})
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    {S : Scheme.{u}} [IsAffine S] (t : D ⟶ (Functor.const I).obj S)
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (X : AlgebraicSpace S) (hXqs : IsQuasiSeparated X)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hproper : IsProperMorphism (structuralMorphism (baseChange p X))) :
    ∃ i, IsUniversallyClosedMorphism (structuralMorphism (baseChange (t.app i) X)) := by
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  obtain ⟨U, a, ha, hUp, hUl⟩ := hcover c.pt (baseChange p X)
    hXqs.baseChange hX.baseChange hproper
  obtain ⟨m⟩ := exists_properSchemeCoverAtStage_of_limit_cover D t c hc p hp X hXqs hX
    U a ha hUp hUl
  refine ⟨m.index, isUniversallyClosed_structural_of_scheme_cover _ m.source m.map m.surjective ?_⟩
  let := m.proper
  infer_instance

end Langlands.AlgebraicGeometry.AlgebraicSpace
