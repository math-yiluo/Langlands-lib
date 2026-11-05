import Langlands.AlgebraicGeometry.SchemeFilteredFiberGeometryStatement
import Langlands.AlgebraicGeometry.SchemeLimitFiberLoci
import Langlands.AlgebraicGeometry.ConstructibleAffineLimit
import Langlands.AlgebraicGeometry.SchemePureDimensionProof
import Langlands.AlgebraicGeometry.RelativeDimensionSublevelRetrocompactnessProof
import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberConstructibilityProof
import Langlands.AbelianScheme.TorsionFiniteEtale

/-! # Filtered descent of nonempty geometrically connected pure-dimensional fibres -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
  {f : X ⟶ Z} {g : Y ⟶ Z} [LocallyOfFiniteType f]

/-- Componentwise pure dimension commutes with the actual fibre base change. -/
theorem pureDimensionFiberLocus_baseChange (h : IsPullback a b f g) (d : ℕ) :
    pureDimensionFiberLocus d b = g ⁻¹' pureDimensionFiberLocus d f := by
  ext y
  exact hasPureDimension_locallyFiniteType_fiberBaseChange_iff h y d

/-- The full source-qualified conjunction has the same inverse-image comparison. -/
theorem nonemptyGeometricallyConnectedPureDimensionFiberLocus_baseChange
    (h : IsPullback a b f g) (d : ℕ) :
    nonemptyGeometricallyConnectedPureDimensionFiberLocus d b =
      g ⁻¹' nonemptyGeometricallyConnectedPureDimensionFiberLocus d f := by
  rw [nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq,
    nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq,
    preimage_inter, geometricallyConnectedFiberLocus_baseChange h,
    pureDimensionFiberLocus_baseChange h]

end Langlands.AlgebraicGeometry.SchemeFiberGeometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry

open AffineLimit EtaleEquivalenceRelation.Action.TargetLimit SchemeFiberGeometry

variable {S X Y T : Scheme.{u}}
  (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
  [LocallyOfFiniteType f]

theorem pureDimensionFiberLocus_baseChangeMap (p : T ⟶ S) (d : ℕ) :
    pureDimensionFiberLocus d (baseChangeMap a b f w p) =
      (pullback.snd p b) ⁻¹' pureDimensionFiberLocus d f :=
  pureDimensionFiberLocus_baseChange (baseChangeMap_cartesian a b f w p).flip d

theorem nonemptyGeometricallyConnectedPureDimensionFiberLocus_baseChangeMap
    (p : T ⟶ S) (d : ℕ) :
    nonemptyGeometricallyConnectedPureDimensionFiberLocus d (baseChangeMap a b f w p) =
      (pullback.snd p b) ⁻¹' nonemptyGeometricallyConnectedPureDimensionFiberLocus d f :=
  nonemptyGeometricallyConnectedPureDimensionFiberLocus_baseChange
    (baseChangeMap_cartesian a b f w p).flip d

variable {I : Type u} [Category.{u} I]
  (D : I ⥤ Scheme.{u}) (t : D ⟶ (Functor.const I).obj S)
  (c : Cone D) (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)

theorem pureDimensionFiberLocus_cone (i : I) (d : ℕ) :
    pureDimensionFiberLocus d (baseChangeMap a b f w p) =
      ((cone D t b c p hp).π.app i) ⁻¹'
        pureDimensionFiberLocus d (baseChangeMap a b f w (t.app i)) := by
  have : LocallyOfFiniteType (baseChangeMap a b f w (t.app i)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
  exact pureDimensionFiberLocus_baseChange
    (coneMorphism_cartesian a b f w D t c p hp i).flip d

theorem nonemptyGeometricallyConnectedPureDimensionFiberLocus_cone (i : I) (d : ℕ) :
    nonemptyGeometricallyConnectedPureDimensionFiberLocus d (baseChangeMap a b f w p) =
      ((cone D t b c p hp).π.app i) ⁻¹'
        nonemptyGeometricallyConnectedPureDimensionFiberLocus d
          (baseChangeMap a b f w (t.app i)) := by
  have : LocallyOfFiniteType (baseChangeMap a b f w (t.app i)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
  exact nonemptyGeometricallyConnectedPureDimensionFiberLocus_baseChange
    (coneMorphism_cartesian a b f w D t c p hp i).flip d

end Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry

namespace Langlands.AlgebraicGeometry.SchemeLimitModel

open AffineLimit EtaleEquivalenceRelation.Action.TargetLimit SchemeFiberGeometry
open Langlands.AlgebraicGeometry.SchemeLimitModel.Geometry

/-- Constructible-set detection supplies the eventual combined condition once
the actual stage loci have been proved constructible. -/
private theorem relativeFiberGeometryDescent_of_isConstructible
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {S X Y : Scheme.{u}} (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S)
    [∀ {i j} (r : i ⟶ j), IsAffineHom (D.map r)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [QuasiCompact b] [QuasiSeparated b] [LocallyOfFiniteType f]
    (d : ℕ)
    (hlevel : ∀ i, IsConstructible
      (nonemptyGeometricallyConnectedPureDimensionFiberLocus d
        (baseChangeMap a b f w (t.app i))))
    (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) :
    NonemptyGeometricallyConnectedPureDimensionFibers d (baseChangeMap a b f w p) ↔
      ∃ i, NonemptyGeometricallyConnectedPureDimensionFibers d
        (baseChangeMap a b f w (t.app i)) := by
  constructor
  · intro H
    obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
    have H' := (nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq_univ_iff d _).mpr H
    rw [nonemptyGeometricallyConnectedPureDimensionFiberLocus_cone a b f w D t c p hp i d]
      at H'
    obtain ⟨j, r, hj⟩ := exists_map_preimage_eq_univ_of_isConstructible
      (diagram D t b) (cone D t b c p hp) (isLimitCone D t b c p hp hc)
      i _ (hlevel i) H'
    have : LocallyOfFiniteType (baseChangeMap a b f w (t.app i)) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
        (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
    refine ⟨j, (nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq_univ_iff d _).mp ?_⟩
    rw [nonemptyGeometricallyConnectedPureDimensionFiberLocus_baseChange
      (morphismDiagram_cartesian a b f w D t r).flip]
    exact hj
  · rintro ⟨i, hi⟩
    apply (nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq_univ_iff d _).mp
    rw [nonemptyGeometricallyConnectedPureDimensionFiberLocus_cone a b f w D t c p hp i d,
      (nonemptyGeometricallyConnectedPureDimensionFiberLocus_eq_univ_iff d _).mpr hi,
      preimage_univ]

/-- The two general constructibility prerequisites supply all stage loci in
the actual model-limit reduction. -/
private theorem relativeFiberGeometryDescent_of_constructibilityProperties
    (hconn : GeometricallyConnectedFiberLocalConstructibility.{u})
    (hdim : RelativeDimensionSublevelProperties.{u})
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {S X Y : Scheme.{u}} (D : I ⥤ Scheme.{u})
    (t : D ⟶ (Functor.const I).obj S)
    [∀ {i j} (r : i ⟶ j), IsAffineHom (D.map r)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (a : X ⟶ S) (b : Y ⟶ S) (f : X ⟶ Y) (w : f ≫ b = a)
    [QuasiCompact b] [QuasiSeparated b]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (d : ℕ) (c : Cone D) (hc : IsLimit c) (p : c.pt ⟶ S)
    (hp : ∀ i, c.π.app i ≫ t.app i = p) :
    NonemptyGeometricallyConnectedPureDimensionFibers d (baseChangeMap a b f w p) ↔
      ∃ i, NonemptyGeometricallyConnectedPureDimensionFibers d
        (baseChangeMap a b f w (t.app i)) := by
  apply relativeFiberGeometryDescent_of_isConstructible D t a b f w d ?_ c hc p hp
  intro i
  have : LocallyOfFinitePresentation (baseChangeMap a b f w (t.app i)) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation)
      (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
  have : QuasiCompact (baseChangeMap a b f w (t.app i)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
  have : QuasiSeparated (baseChangeMap a b f w (t.app i)) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (baseChangeMap_cartesian a b f w (t.app i)).flip inferInstance
  have : QuasiSeparatedSpace (pullback (t.app i) b : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (t.app i) b)
  exact isConstructible_nonemptyGeometricallyConnectedPureDimensionFiberLocus_of_factors
    _ d (isConstructible_geometricallyConnectedFiberLocus_of_localConstructibility hconn _)
    (isConstructible_pureDimensionFiberLocus_of_sublevelProperties hdim _ d)

private theorem spectrumFiberGeometryDescent_of_constructibilityProperties
    (hconn : GeometricallyConnectedFiberLocalConstructibility.{u})
    (hdim : RelativeDimensionSublevelProperties.{u})
    (R : Type u) [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F) (hc : IsColimit c)
    (X Y : Over (Spec (CommRingCat.of R))) (f : X ⟶ Y)
    [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    [LocallyOfFinitePresentation f.left] [QuasiCompact f.left] [QuasiSeparated f.left]
    (d : ℕ) :
    NonemptyGeometricallyConnectedPureDimensionFibers d
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (spectrumBaseMap R F c)) ↔
      ∃ j : J, NonemptyGeometricallyConnectedPureDimensionFibers d
        (baseChangeMap X.hom Y.hom f.left (Over.w f)
          ((spectrumStructure R F).app (op j))) := by
  refine (relativeFiberGeometryDescent_of_constructibilityProperties hconn hdim
    (spectrumDiagram R F) (spectrumStructure R F) X.hom Y.hom f.left (Over.w f)
    d (spectrumCone R F c) (spectrumConeIsLimit R F c hc) (spectrumBaseMap R F c)
    (spectrumCone_compat R F c)).trans ?_
  exact ⟨fun ⟨j, h⟩ ↦ ⟨j.unop, h⟩, fun ⟨j, h⟩ ↦ ⟨op j, h⟩⟩

private theorem initialRingFiberGeometryDescent_of_constructibilityProperties
    (hconn : GeometricallyConnectedFiberLocalConstructibility.{u})
    (hdim : RelativeDimensionSublevelProperties.{u})
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c) (j₀ : J)
    (X Y : Over (Spec (F.obj j₀))) (f : X ⟶ Y)
    [QuasiCompact Y.hom] [QuasiSeparated Y.hom]
    [LocallyOfFinitePresentation f.left] [QuasiCompact f.left] [QuasiSeparated f.left]
    (d : ℕ) :
    NonemptyGeometricallyConnectedPureDimensionFibers d
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (c.ι.app j₀))) ↔
      ∃ j : Under j₀, NonemptyGeometricallyConnectedPureDimensionFibers d
        (baseChangeMap X.hom Y.hom f.left (Over.w f) (Spec.map (F.map j.hom))) :=
  spectrumFiberGeometryDescent_of_constructibilityProperties hconn hdim
    (F.obj j₀) (initialRingAlgebraDiagram F j₀) (initialRingAlgebraCocone F j₀ c)
    (initialRingAlgebraCoconeIsColimit F j₀ c hc) X Y f d

/-- Reduce the original-ring target to the two general constructibility properties. -/
private theorem finitePresentationInitialRingFiberGeometryDescent_of_constructibilityProperties
    (hconn : GeometricallyConnectedFiberLocalConstructibility.{u})
    (hdim : RelativeDimensionSublevelProperties.{u}) :
    FinitePresentationInitialRingFiberGeometryDescent.{u} := by
  intro d J _ _ F c hc j₀ X Y f _ _ _ _ _ _
  have : LocallyOfFinitePresentation (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiCompact (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : QuasiSeparated (f.left ≫ Y.hom) := by
    rw [Over.w f]
    infer_instance
  have : LocallyOfFinitePresentation f.left :=
    Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_comp f.left Y.hom
  have : QuasiCompact f.left := QuasiCompact.of_comp f.left Y.hom
  have : QuasiSeparated f.left := QuasiSeparated.of_comp f.left Y.hom
  exact initialRingFiberGeometryDescent_of_constructibilityProperties hconn hdim
    F c hc j₀ X Y f d

/-- The final property clause of Conrad's Theorem 3.4(2), for arbitrary
small filtered ring diagrams and the actual original outgoing transitions. -/
theorem finitePresentationInitialRingFiberGeometryDescent :
    FinitePresentationInitialRingFiberGeometryDescent.{u} :=
  finitePresentationInitialRingFiberGeometryDescent_of_constructibilityProperties
    geometricallyConnectedFiberLocalConstructibility relativeDimensionSublevelProperties_proof

end Langlands.AlgebraicGeometry.SchemeLimitModel
