import Langlands.AlgebraicGeometry.AlgebraicSpace.EventualTargetAtlasDescent
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitUniquenessProof
import Langlands.AlgebraicGeometry.SchemeLimitFiberLoci
import Langlands.AlgebraicGeometry.ConstructibleAffineLimit

/-! # Eventual surjectivity of represented finite-presentation morphisms -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action.TargetLimit
open Langlands.AlgebraicGeometry.SchemeFiberGeometry
open Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Fullness of the actual nonempty-fibre locus is scheme surjectivity. -/
theorem nonemptyFiberLocus_eq_univ_iff_surjective {U V : Scheme.{u}} (q : U ⟶ V) :
    nonemptyFiberLocus q = Set.univ ↔ Surjective q := by
  rw [nonemptyFiberLocus_eq_range, Set.range_eq_univ, surjective_iff]

/-- Surjectivity of actual scheme model maps is detected by the constructible
nonempty-fibre locus at an incoming stage. -/
theorem surjective_schemeStructuralPropertyDescent :
    SchemeStructuralPropertyDescent.{u} @Surjective := by
  intro I _ _ D S U V _ _ t a b q w _ _ _ _ _ _ c hc p hp
  have : LocallyOfFinitePresentation (q ≫ b) := by rw [w]; infer_instance
  have hq : LocallyOfFinitePresentation q :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp q b
  let := hq
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace a
  have : QuasiSeparatedSpace V := quasiSeparatedSpace_of_quasiSeparated b
  have : QuasiCompact q := inferInstance
  have {j k : I} (r : j ⟶ k) : IsAffineHom (D.map r) := inferInstance
  have hlevel (k : I) : IsConstructible
      (nonemptyFiberLocus (AffineLimit.baseChangeMap a b q w (t.app k))) := by
    have : QuasiSeparatedSpace (Limits.pullback (t.app k) b : Scheme.{u}) :=
      quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app k) b)
    have : LocallyOfFinitePresentation (AffineLimit.baseChangeMap a b q w (t.app k)) :=
      MorphismProperty.of_isPullback
        (baseChangeMap_cartesian a b q w (t.app k)).flip hq
    have : QuasiCompact (AffineLimit.baseChangeMap a b q w (t.app k)) :=
      MorphismProperty.of_isPullback
        (baseChangeMap_cartesian a b q w (t.app k)).flip inferInstance
    exact isConstructible_nonemptyFiberLocus _
  constructor
  · intro H
    obtain ⟨k⟩ := IsCofiltered.nonempty (C := I)
    have H' := (nonemptyFiberLocus_eq_univ_iff_surjective _).mpr H
    rw [nonemptyFiberLocus_cone a b q w D t c p hp k] at H'
    obtain ⟨j, r, hj⟩ := exists_map_preimage_eq_univ_of_isConstructible
      (diagram D t b) (cone D t b c p hp) (isLimitCone D t b c p hp hc)
      k _ (hlevel k) H'
    refine ⟨j, (nonemptyFiberLocus_eq_univ_iff_surjective _).mp ?_⟩
    rw [nonemptyFiberLocus_baseChange (morphismDiagram_cartesian a b q w D t r).flip]
    exact hj
  · rintro ⟨j, hj⟩
    exact MorphismProperty.of_isPullback
      (coneMorphism_cartesian a b q w D t c p hp j).flip hj

namespace SchemeTargetAtlas

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

/-- An independently known representability witness upgrades the actual scheme
square without any effective descent premise. -/
def toRepresented (a : SchemeTargetAtlas f) (hr : IsRepresentableMorphism (hom f)) :
    RepresentedMorphismAtlas f where
  representable := hr
  source := a.source
  target := a.target
  sourceMap := a.sourceMap
  targetMap := a.targetMap
  schemeMap := a.schemeMap
  targetEtale := a.targetEtale
  targetSurjective := a.targetSurjective
  square := a.square

end SchemeTargetAtlas

/-- For a morphism already representable at the original stage, scheme
structural descent needs no further atlas-effectivity premise. -/
theorem spaceLimitRelativePropertyDescent_of_representable
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Etale.{u} ⊓ @Surjective.{u})]
    (hP : SchemeStructuralPropertyDescent P)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : AlgebraicSpace (D.obj i)}
    (hXqs : IsQuasiSeparated X)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hYqs : IsQuasiSeparated Y)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (f : X ⟶ Y) (hr : IsRepresentableMorphism (hom f)) :
    (MorphismProperty.inverseImage P (Over.forget c.pt)).relative (schemeYoneda c.pt)
      (hom (baseChangeMap (c.π.app i) f)) ↔
      ∃ (j : I) (r : j ⟶ i),
        (MorphismProperty.inverseImage P (Over.forget (D.obj j))).relative
          (schemeYoneda (D.obj j)) (hom (baseChangeMap (D.map r) f)) := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  constructor
  · intro hf
    obtain ⟨j, r, ⟨a⟩⟩ := exists_finitePresentation_schemeTargetAtlas_of_modelUniqueness
      spaceLimitModelUniqueness D c hc i hXqs hX hYqs hY f hf.1
    let b := a.atlas.toRepresented (relativelyRepresentable_restrictPresheaf_map hr)
    let : LocallyOfFinitePresentation b.source.hom := a.sourceLocallyOfFinitePresentation
    let : QuasiCompact b.source.hom := a.sourceQuasiCompact
    let : QuasiSeparated b.source.hom := a.sourceQuasiSeparated
    let : LocallyOfFinitePresentation b.target.hom := a.targetLocallyOfFinitePresentation
    let : QuasiCompact b.target.hom := a.targetQuasiCompact
    let : QuasiSeparated b.target.hom := a.targetQuasiSeparated
    have hfj := (relative_baseChangeMap_comp_iff (D.map r) (c.π.app j)
      (c.π.app i) P (c.w r) f).mpr hf
    obtain ⟨k, s, hk⟩ := (b.property_limit_iff P hP D c hc j).mp hfj
    refine ⟨k, s ≫ r, ?_⟩
    exact (relative_baseChangeMap_comp_iff (D.map r) (D.map s)
      (D.map (s ≫ r)) P (D.map_comp s r).symm f).mp hk
  · rintro ⟨j, r, hj⟩
    exact relative_baseChangeMap_of_stage D c r f P hj

/-- Geometric surjectivity of a represented morphism of the stage spaces is
eventually detected along any cofiltered affine limit. -/
theorem isSurjective_limit_iff_of_representable
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X Y : AlgebraicSpace (D.obj i)}
    (hXqs : IsQuasiSeparated X)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hYqs : IsQuasiSeparated Y)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (f : X ⟶ Y) (hr : IsRepresentableMorphism (hom f)) :
    IsSurjective (hom (baseChangeMap (c.π.app i) f)) ↔
      ∃ (j : I) (r : j ⟶ i), IsSurjective (hom (baseChangeMap (D.map r) f)) :=
  by
    let : MorphismProperty.DescendsAlong (@Surjective.{u})
        (@Etale.{u} ⊓ @Surjective.{u}) :=
      SchemeFlatPropertyDescent.descendsAlong_etale_surjective _
    exact spaceLimitRelativePropertyDescent_of_representable @Surjective
      surjective_schemeStructuralPropertyDescent D c hc i hXqs hX hYqs hY f hr

end Langlands.AlgebraicGeometry.AlgebraicSpace
