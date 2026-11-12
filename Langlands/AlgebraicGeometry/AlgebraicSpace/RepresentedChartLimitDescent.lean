import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeDiagonalLimitDescent
import Langlands.AlgebraicGeometry.SchemeLimitAffineProof
import Langlands.AlgebraicGeometry.SchemeLimitOpenImmersionProof
import Langlands.AlgebraicGeometry.SchemeLimitRelativeFiniteProof

/-! # Limit descent using a fixed represented pullback over a target atlas -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S T : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- A scheme presentation of the pullback of a representable morphism along
one surjective étale target atlas. Representability is an explicit premise. -/
structure RepresentedMorphismAtlas (f : X ⟶ Y) where
  representable : IsRepresentableMorphism (hom f)
  source : Over S
  target : Over S
  sourceMap : (schemeYoneda S).obj source ⟶ X.presheaf
  targetMap : (schemeYoneda S).obj target ⟶ Y.presheaf
  schemeMap : source ⟶ target
  targetEtale : IsEtale targetMap
  targetSurjective : IsSurjective targetMap
  square : IsPullback sourceMap ((schemeYoneda S).map schemeMap) (hom f) targetMap

namespace RepresentedMorphismAtlas

variable {f : X ⟶ Y} (a : RepresentedMorphismAtlas f)

/-- Restriction carries the actual represented pullback square to its scheme
base change, using the natural Yoneda comparison on both scheme corners. -/
def baseChange (g : T ⟶ S) : RepresentedMorphismAtlas (baseChangeMap g f) where
  representable := relativelyRepresentable_restrictPresheaf_map a.representable
  source := (Over.pullback g).obj a.source
  target := (Over.pullback g).obj a.target
  sourceMap := restrictAtlas g a.sourceMap
  targetMap := restrictAtlas g a.targetMap
  schemeMap := (Over.pullback g).map a.schemeMap
  targetEtale := relative_restrictAtlas _ a.targetEtale
  targetSurjective := relative_restrictAtlas _ a.targetSurjective
  square := by
    apply (a.square.map (restrictPresheaf g)).of_iso'
      (schemeYonedaBaseChangeIso g a.source) (Iso.refl _)
      (schemeYonedaBaseChangeIso g a.target) (Iso.refl _)
    · simp [restrictAtlas]
    · exact ((schemeYonedaBaseChangeNatIso g).hom.naturality a.schemeMap).symm
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · simp [restrictAtlas]

/-- A represented property after scheme base change is equivalent to the
property of the base change of the original fixed scheme map. -/
theorem property_baseChange_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u})] (g : T ⟶ S) :
    (MorphismProperty.inverseImage P (Over.forget T)).relative (schemeYoneda T)
        (hom (baseChangeMap g f)) ↔
      P (AffineLimit.baseChangeMap a.source.hom a.target.hom a.schemeMap.left
        (Over.w a.schemeMap) g) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let b := a.baseChange g
  exact (relativeProperty_iff_of_etale_atlas P b.representable
    b.targetMap b.targetEtale b.targetSurjective b.sourceMap b.schemeMap b.square).trans
    (MorphismProperty.arrow_mk_iso_iff P (overPullbackSchemeArrowIso a.schemeMap g))

end RepresentedMorphismAtlas

/-- A common sufficient scheme theorem for a property, keeping finite
presentation, quasi-compactness and quasi-separatedness of both structural
maps. The four specializations below are proved from published scheme descent. -/
def SchemeStructuralPropertyDescent (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) {S U V : Scheme.{u}}
    [IsAffine S] [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S)
    (a : U ⟶ S) (b : V ⟶ S) (q : U ⟶ V) (w : q ≫ b = a)
    [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a]
    [LocallyOfFinitePresentation b] [QuasiCompact b] [QuasiSeparated b]
    (c : Cone D) (_hc : IsLimit c) (p : c.pt ⟶ S)
    (_hp : ∀ i, c.π.app i ≫ t.app i = p),
      P (AffineLimit.baseChangeMap a b q w p) ↔
        ∃ i, P (AffineLimit.baseChangeMap a b q w (t.app i))

private theorem schemeMap_finiteness {S U V : Scheme.{u}} [IsAffine S]
    (a : U ⟶ S) (b : V ⟶ S) (q : U ⟶ V) (w : q ≫ b = a)
    [LocallyOfFinitePresentation a] [QuasiCompact a] [QuasiSeparated a]
    [QuasiSeparated b] :
    LocallyOfFiniteType q ∧ QuasiCompact q ∧ QuasiSeparated q := by
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated a
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated b
  have : LocallyOfFiniteType (q ≫ b) := by rw [w]; infer_instance
  exact ⟨locallyOfFiniteType_of_comp q b, inferInstance, inferInstance⟩

theorem closedImmersion_schemeStructuralPropertyDescent :
    SchemeStructuralPropertyDescent.{u} @_root_.AlgebraicGeometry.IsClosedImmersion := by
  intro I _ _ D S U V _ _ t a b q w _ _ _ _ _ _ c hc p hp
  obtain ⟨hqt, hqc, hqs⟩ := schemeMap_finiteness a b q w
  let := hqt
  let := hqc
  let := hqs
  exact AffineLimit.relativeClosedImmersionDescent D t a b q w c hc p hp

theorem affine_schemeStructuralPropertyDescent :
    SchemeStructuralPropertyDescent.{u} @IsAffineHom := by
  intro I _ _ D S U V _ _ t a b q w _ _ _ _ _ _ c hc p hp
  obtain ⟨_, hqc, hqs⟩ := schemeMap_finiteness a b q w
  let := hqc
  let := hqs
  exact AffineLimit.relativeAffinenessDescent D t a b q w c hc p hp

theorem openImmersion_schemeStructuralPropertyDescent :
    SchemeStructuralPropertyDescent.{u} @_root_.AlgebraicGeometry.IsOpenImmersion := by
  intro I _ _ D S U V _ _ t a b q w _ _ _ _ _ _ c hc p hp
  exact AffineLimit.relativeOpenImmersionDescent D t a b q w c hc p hp

theorem finite_schemeStructuralPropertyDescent :
    SchemeStructuralPropertyDescent.{u} @_root_.AlgebraicGeometry.IsFinite := by
  intro I _ _ D S U V _ _ t a b q w _ _ _ _ _ _ c hc p hp
  obtain ⟨hqt, hqc, hqs⟩ := schemeMap_finiteness a b q w
  let := hqt
  let := hqc
  let := hqs
  exact AffineLimit.relativeFiniteDescent D t a b q w c hc p hp

namespace RepresentedMorphismAtlas

/-- Scheme descent on one fixed represented target-atlas pullback gives
space descent, retaining the actual representability and scheme finiteness
premises of that chart. -/
theorem property_limit_iff
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u})]
    (hP : SchemeStructuralPropertyDescent P)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : AlgebraicSpace (D.obj i)} {f : X ⟶ Y} (a : RepresentedMorphismAtlas f)
    [LocallyOfFinitePresentation a.source.hom] [QuasiCompact a.source.hom]
    [QuasiSeparated a.source.hom] [LocallyOfFinitePresentation a.target.hom]
    [QuasiCompact a.target.hom] [QuasiSeparated a.target.hom] :
    (MorphismProperty.inverseImage P (Over.forget c.pt)).relative (schemeYoneda c.pt)
        (hom (baseChangeMap (c.π.app i) f)) ↔
      ∃ (j : I) (r : j ⟶ i),
        (MorphismProperty.inverseImage P (Over.forget (D.obj j))).relative
          (schemeYoneda (D.obj j)) (hom (baseChangeMap (D.map r) f)) := by
  let E := Over.forget i ⋙ D
  let t : E ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app := fun j => D.map j.hom
      naturality := by
        intro j k r
        change D.map r.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
        rw [← D.map_comp, Over.w r, Category.comp_id] }
  have (j : Over i) : IsAffine (E.obj j) := by dsimp [E]; infer_instance
  let c' := c.whisker (Over.forget i)
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have hdesc := hP E t a.source.hom a.target.hom a.schemeMap.left
    (Over.w a.schemeMap) c' hc' (c.π.app i) (fun j => c.w j.hom)
  constructor
  · intro hf
    obtain ⟨j, hj⟩ := hdesc.mp ((a.property_baseChange_iff P (c.π.app i)).mp hf)
    exact ⟨j.left, j.hom, (a.property_baseChange_iff P (D.map j.hom)).mpr hj⟩
  · rintro ⟨j, r, hj⟩
    have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact relative_baseChangeMap_of_stage D c r f P hj

variable {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : AlgebraicSpace (D.obj i)} {f : X ⟶ Y} (a : RepresentedMorphismAtlas f)
    [LocallyOfFinitePresentation a.source.hom] [QuasiCompact a.source.hom]
    [QuasiSeparated a.source.hom] [LocallyOfFinitePresentation a.target.hom]
    [QuasiCompact a.target.hom] [QuasiSeparated a.target.hom]

include hc a

theorem closedImmersion_limit_iff :
    IsClosedImmersion (hom (baseChangeMap (c.π.app i) f)) ↔
      ∃ (j : I) (r : j ⟶ i), IsClosedImmersion (hom (baseChangeMap (D.map r) f)) :=
  a.property_limit_iff @_root_.AlgebraicGeometry.IsClosedImmersion
    closedImmersion_schemeStructuralPropertyDescent D c hc i

theorem affine_limit_iff :
    IsAffineMorphism (hom (baseChangeMap (c.π.app i) f)) ↔
      ∃ (j : I) (r : j ⟶ i), IsAffineMorphism (hom (baseChangeMap (D.map r) f)) :=
  a.property_limit_iff @IsAffineHom affine_schemeStructuralPropertyDescent D c hc i

theorem openImmersion_limit_iff :
    IsOpenImmersion (hom (baseChangeMap (c.π.app i) f)) ↔
      ∃ (j : I) (r : j ⟶ i), IsOpenImmersion (hom (baseChangeMap (D.map r) f)) :=
  a.property_limit_iff @_root_.AlgebraicGeometry.IsOpenImmersion
    openImmersion_schemeStructuralPropertyDescent D c hc i

theorem finite_limit_iff :
    IsFinite (hom (baseChangeMap (c.π.app i) f)) ↔
      ∃ (j : I) (r : j ⟶ i), IsFinite (hom (baseChangeMap (D.map r) f)) :=
  a.property_limit_iff @_root_.AlgebraicGeometry.IsFinite
    finite_schemeStructuralPropertyDescent D c hc i

end RepresentedMorphismAtlas

end Langlands.AlgebraicGeometry.AlgebraicSpace
