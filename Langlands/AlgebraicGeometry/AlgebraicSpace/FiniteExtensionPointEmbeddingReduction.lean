import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianFiniteExtensionPointEmbeddingStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianCompletionPointEmbeddingProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison
import Langlands.AlgebraicGeometry.PointTopology.FiniteExtensionCompletion

/-!
# Reduction of finite-extension point embeddings to complete fields

Coefficient change is continuous for the étale-chart topologies. Its compatibility
with towers and the embeddings into completions reduce Conrad's finite-extension
assertion to the same assertion for complete fields.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
  (RingPoint ringBaseChange ringPointBaseChangeEquiv schemePointTopology
    schemeBaseChangeTopology_proof isEmbedding_schemeChangeRing IsHenselianValuedField
    completionNontriviallyNormedField)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Local separatedness is preserved by arbitrary base change. -/
theorem IsLocallySeparated.baseChange {S T : Scheme.{u}} {X : AlgebraicSpace S}
    (hX : IsLocallySeparated X) (g : T ⟶ S) :
    IsLocallySeparated (baseChange g X) := by
  have : MorphismProperty.RespectsIso (@_root_.AlgebraicGeometry.IsImmersion.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact relative_diag_restrictPresheaf (g := g) _ hX

section PointMaps

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The coefficient-change map, written on rational points of the base-changed space. -/
def fieldExtensionPointMap (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    RingPoints K X K →
      RingPoints L (baseChange (Spec.algebraMap K L) X) L :=
  fun x => (baseChangeRingPointsEquiv K L L X).symm
    (RingPoints.changeRing (Algebra.ofId K L) x)

/-- The corresponding coefficient-change map on actual scheme points. -/
def fieldExtensionSchemePointMap (U : Over (Spec (CommRingCat.of K))) :
    RingPoint K U K → RingPoint L (ringBaseChange K L U) L :=
  fun x => ringPointBaseChangeEquiv K L L U
    (PointTopology.RingPoint.changeRing (Algebra.ofId K L) x)

end PointMaps

section Charts

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {X : AlgebraicSpace (Spec (CommRingCat.of K))}

/-- Base change of a finite-type étale chart along a field extension. -/
abbrev EtaleFiniteTypeChart.fieldExtension (c : EtaleFiniteTypeChart K X) :
    EtaleFiniteTypeChart L (baseChange (Spec.algebraMap K L) X) where
  scheme := ringBaseChange K L c.scheme
  hom := homMk (restrictAtlas (Spec.algebraMap K L) (AlgebraicSpace.hom c.hom))
  isEtale := by
    have : MorphismProperty.RespectsIso (@Etale.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact relative_restrictAtlas _ c.isEtale
  locallyOfFiniteType := by
    have := c.locallyOfFiniteType
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd c.scheme.hom (Spec.algebraMap K L))
    infer_instance
  quasiCompact := by
    have := c.quasiCompact
    change QuasiCompact
      (CategoryTheory.Limits.pullback.snd c.scheme.hom (Spec.algebraMap K L))
    infer_instance

/-- The point equivalence reads a base-changed chart as its original chart. -/
theorem baseChangeRingPointsEquiv_fieldExtension_pointMap (c : EtaleFiniteTypeChart K X)
    (p : RingPoint L (ringBaseChange K L c.scheme) L) :
    baseChangeRingPointsEquiv K L L X (c.fieldExtension.pointMap p) =
      RingPoints.map c.hom ((schemeRingPointsEquiv K c.scheme L).symm
        ((ringPointBaseChangeEquiv K L L c.scheme).symm p)) := by
  rw [baseChangeRingPointsEquiv_apply]
  refine (mapSections_naturality c.hom
    (PointTopology.ringTestRestrictScalarsIso K L L).inv _).trans ?_
  change mapSections c.hom _ (ULift.up _) = mapSections c.hom _ (ULift.up _)
  congr 2

/-- Coefficient change commutes with chart maps. -/
theorem fieldExtensionPointMap_pointMap (c : EtaleFiniteTypeChart K X)
    (x : RingPoint K c.scheme K) :
    fieldExtensionPointMap K L X (c.pointMap x) =
      c.fieldExtension.pointMap (fieldExtensionSchemePointMap K L c.scheme x) := by
  apply (baseChangeRingPointsEquiv K L L X).injective
  rw [fieldExtensionPointMap, Equiv.apply_symm_apply,
    baseChangeRingPointsEquiv_fieldExtension_pointMap,
    fieldExtensionSchemePointMap, Equiv.symm_apply_apply,
    EtaleFiniteTypeChart.pointMap, RingPoints.changeRing_map]
  rfl

end Charts

section Topology

variable (K L : Type u) [NontriviallyNormedField K] [NontriviallyNormedField L]
variable [NormedAlgebra K L]

/-- The map on points of any scheme embeds under a normed extension of fields. -/
theorem isEmbedding_fieldExtensionSchemePointMap
    (U : Over (Spec (CommRingCat.of K))) :
    @IsEmbedding _ _ (schemePointTopology K U K)
      (schemePointTopology L (ringBaseChange K L U) L)
      (fieldExtensionSchemePointMap K L U) := by
  let : TopologicalSpace (RingPoint K U K) := schemePointTopology K U K
  let : TopologicalSpace (RingPoint K U L) := schemePointTopology K U L
  let : TopologicalSpace (RingPoint L (ringBaseChange K L U) L) :=
    schemePointTopology L (ringBaseChange K L U) L
  have hι : IsEmbedding (Algebra.ofId K L) :=
    (PointTopology.FiniteExtensionCompletion.isometry_algebraMap K L).isEmbedding
  exact (schemeBaseChangeTopology_proof K L L U).isEmbedding.comp
    (isEmbedding_schemeChangeRing K K L U (Algebra.ofId K L) hι)

/-- Coefficient change is continuous on algebraic-space points for the independently
defined étale-chart topologies. -/
theorem continuous_fieldExtensionPointMap
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) :
    @Continuous _ _ (etaleChartTopology K X)
      (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
      (fieldExtensionPointMap K L X) := by
  let : TopologicalSpace
      (RingPoints L (baseChange (Spec.algebraMap K L) X) L) :=
    etaleChartTopology L _
  rw [etaleChartTopology_continuous_iff]
  intro c
  let : TopologicalSpace (RingPoint K c.scheme K) := schemePointTopology K c.scheme K
  let : TopologicalSpace (RingPoint L (ringBaseChange K L c.scheme) L) :=
    schemePointTopology L (ringBaseChange K L c.scheme) L
  have heq : fieldExtensionPointMap K L X ∘ c.pointMap =
      c.fieldExtension.pointMap ∘ fieldExtensionSchemePointMap K L c.scheme :=
    funext (fieldExtensionPointMap_pointMap c)
  rw [heq]
  exact c.fieldExtension.continuous_pointMap.comp
    (isEmbedding_fieldExtensionSchemePointMap K L c.scheme).continuous

end Topology

section Towers

variable {C A B D : Type u} [CommRing C] [CommRing A] [CommRing B] [CommRing D]
variable [Algebra C A] [Algebra C B] [Algebra C D]

/-- Successive coefficient changes equal coefficient change along the composite. -/
theorem RingPoints.changeRing_comp
    (X : AlgebraicSpace (Spec (CommRingCat.of C))) (φ : A →ₐ[C] B) (ψ : B →ₐ[C] D)
    (x : RingPoints C X A) :
    RingPoints.changeRing ψ (RingPoints.changeRing φ x) =
      RingPoints.changeRing (ψ.comp φ) x := by
  unfold RingPoints.changeRing
  rw [PointTopology.ringTestMap_comp]
  exact (pullback_comp X _ _ x).symm

variable (K L M : Type u) [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]

/-- The point maps for a tower agree after the canonical iterated-base-change isomorphism. -/
theorem fieldExtensionPointMap_tower
    (X : AlgebraicSpace (Spec (CommRingCat.of K))) (x : RingPoints K X K) :
    RingPoints.map (towerIso K L M X).hom
      (fieldExtensionPointMap L M (baseChange (Spec.algebraMap K L) X)
        (fieldExtensionPointMap K L X x)) =
      fieldExtensionPointMap K M X x := by
  apply (baseChangeRingPointsEquiv K M M X).injective
  rw [baseChangeRingPointsEquiv_towerIso]
  simp only [fieldExtensionPointMap, Equiv.apply_symm_apply]
  rw [baseChangeRingPointsEquiv_changeRing, Equiv.apply_symm_apply,
    RingPoints.changeRing_comp]
  congr 1
  ext

end Towers

/-- The complete-field case needed for Conrad's finite-extension supplement. This
internal target retains locally separated, quasi-separated, locally finite-type spaces. -/
def CompleteFiniteExtensionPointEmbeddingStatement : Prop :=
  ∀ (K L : Type u) [NontriviallyNormedField K] [NontriviallyNormedField L]
    [NormedAlgebra K L] [FiniteDimensional K L] [CompleteSpace K] [CompleteSpace L],
    ∀ X : AlgebraicSpace (Spec (CommRingCat.of K)),
      IsLocallySeparatedLocallyFiniteType K X →
        @IsEmbedding _ _ (etaleChartTopology K X)
          (etaleChartTopology L (baseChange (Spec.algebraMap K L) X))
          (fieldExtensionPointMap K L X)

/-- The complete finite-degree case implies the full henselian finite-degree assertion. -/
theorem henselianFiniteExtensionPointEmbedding_of_complete
    (hcomplete : CompleteFiniteExtensionPointEmbeddingStatement.{u}) :
    HenselianFiniteExtensionPointEmbeddingStatement.{u} := by
  intro K L _ _ _ _ hK hL X hX
  let Kc := UniformSpace.Completion K
  let Lc := UniformSpace.Completion L
  let := completionNontriviallyNormedField K
  let := completionNontriviallyNormedField L
  let := PointTopology.FiniteExtensionCompletion.algebra K L
  let := PointTopology.FiniteExtensionCompletion.normedAlgebra K L
  have := PointTopology.FiniteExtensionCompletion.finiteDimensional K L
  let XKc := baseChange (Spec.algebraMap K Kc) X
  let XL := baseChange (Spec.algebraMap K L) X
  let XLc := baseChange (Spec.algebraMap K Lc) X
  have hXKc : IsLocallySeparatedLocallyFiniteType Kc XKc :=
    ⟨⟨hX.1.1.baseChange, hX.1.2.baseChange⟩, hX.2.baseChange _⟩
  have hXL : IsQuasiSeparatedLocallyFiniteType L XL :=
    ⟨hX.1.1.baseChange, hX.1.2.baseChange⟩
  let : TopologicalSpace (RingPoints K X K) := etaleChartTopology K X
  let : TopologicalSpace (RingPoints Kc XKc Kc) := etaleChartTopology Kc XKc
  let : TopologicalSpace (RingPoints L XL L) := etaleChartTopology L XL
  let : TopologicalSpace (RingPoints Lc XLc Lc) := etaleChartTopology Lc XLc
  let : TopologicalSpace
      (RingPoints Lc (baseChange (Spec.algebraMap Kc Lc) XKc) Lc) :=
    etaleChartTopology Lc _
  let : TopologicalSpace
      (RingPoints Lc (baseChange (Spec.algebraMap L Lc) XL) Lc) :=
    etaleChartTopology Lc _
  let g := RingPoints.map (A := Lc) (towerIso K L Lc X).hom ∘ completionPointMap XL
  have hg : IsEmbedding g :=
    (isHomeomorph_ringPointsMap_of_iso (towerIso K L Lc X)).isEmbedding.comp
      (henselianCompletionPointEmbedding L hL XL hXL)
  have htop : IsEmbedding
      (RingPoints.map (A := Lc) (towerIso K Kc Lc X).hom ∘
        fieldExtensionPointMap Kc Lc XKc ∘ completionPointMap X) :=
    (isHomeomorph_ringPointsMap_of_iso (towerIso K Kc Lc X)).isEmbedding.comp
      ((hcomplete Kc Lc XKc hXKc).comp
        (henselianCompletionPointEmbedding K hK X hX.1))
  have heq : g ∘ fieldExtensionPointMap K L X =
      RingPoints.map (A := Lc) (towerIso K Kc Lc X).hom ∘
        fieldExtensionPointMap Kc Lc XKc ∘ completionPointMap X := by
    funext x
    exact (fieldExtensionPointMap_tower K L Lc X x).trans
      (fieldExtensionPointMap_tower K Kc Lc X x).symm
  change IsEmbedding (fieldExtensionPointMap K L X)
  apply hg.of_comp_iff.mp
  rw [heq]
  exact htop

end Langlands.AlgebraicGeometry.AlgebraicSpace
