import Langlands.Geometry.Analytic.AnalyticDomainSpaces
import Langlands.Geometry.Analytic.GroundFieldChangingSpaceFunctor

/-! # Continuity tests for actions on analytic spaces with varying fields -/

noncomputable section

open CategoryTheory Filter Opposite Set
open scoped Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v z

namespace Langlands.Analytic.SpaceOverField

open CompleteUltrametricField
open CompatibleAtlasPresentation (localizationFunctor localizedSaturationFunctor)
open AffinoidAtlasPresentation.GroundFieldExtension.CompleteField (compatibleExtend compatibleExtendId)
open IndexedAffinoidAtlas.GroundFieldExtension (chartSystem projection projection_image_chart
  range_chart_subset_iff unitCompatibleMap_isQuasiIso)
open PresentedAffinoidAlgebra.GroundFieldExtension (iota unitEquiv_apply)

private abbrev fibreInclusion (K : CompleteUltrametricField.{u}) :
    K.CompatibleAnalyticCategory.{u, v} ⥤ SpaceOverField.{u, v} :=
  Pseudofunctor.CoGrothendieck.ι scalarExtensionPseudofunctor (op K)

variable (X : SpaceOverField.{u, v})

/-- An affinoid domain of `X` with a presentation having a greatest chart.
The domain embedding is measured in the saturated analytic localization. -/
structure SemilinearAffinoidProbe where
  atlas : X.field.CompatibleCategory.{u, v}
  chart : atlas.presentation.atlas.Index
  contains : ∀ i, range (atlas.presentation.atlas.chart i) ⊆
    range (atlas.presentation.atlas.chart chart)
  inclusion : localizationFunctor.obj atlas ⟶ X.space
  isAffinoidDomain : SaturatedAtlasPresentation.IsAffinoidDomainEmbedding
    (localizedSaturationFunctor.map inclusion)

namespace SemilinearAffinoidProbe

variable {X} (U : SemilinearAffinoidProbe X)

/-- The analytic inclusion with identity field map. -/
abbrev arrow :
    withField X.field (localizationFunctor.obj U.atlas) ⟶ X :=
  (fibreInclusion X.field).map U.inclusion

/-- The full algebra of analytic functions on the probe. -/
abbrev algebra := U.atlas.presentation.atlas.algebra U.chart

/-- A single compact function test. The given automorphism preserves the
domain by the analytic square. On a common representative of the source, the
two bounded pullbacks are compared after the actual coefficient embedding. -/
def IsNearIdentity (σ : Aut X) (s : U.algebra) (ε : ℝ) : Prop :=
  ∃ a : Aut (withField X.field (localizationFunctor.obj U.atlas)),
    a.asIso.hom ≫ U.arrow = U.arrow ≫ σ.asIso.hom ∧
    let e := fieldMap a.asIso.hom
    letI := e.normedAlgebra
    let B := (compatibleExtend e).obj U.atlas
    ∃ (T : X.field.CompatibleCategory.{u, v}) (q : T ⟶ U.atlas) (f : T ⟶ B),
      q.toStrongHom.IsQuasiIso ∧
      localizationFunctor.map q ≫ analyticMap a.asIso.hom = localizationFunctor.map f ∧
      ∃ (hq : ∀ i, q.baseMap '' range (T.presentation.atlas.chart i) ⊆
          range (U.atlas.presentation.atlas.chart U.chart))
        (hf : ∀ i, f.baseMap '' range (T.presentation.atlas.chart i) ⊆
          range (B.presentation.atlas.chart U.chart)),
        ∀ i (x : BanachSpectrum (T.presentation.atlas.algebra i)),
          x (f.pullback i U.chart (hf i) (iota X.field X.field U.algebra s) -
            q.pullback i U.chart (hq i) s) ≤ ε

/-- The identity acts trivially on every bounded function test. -/
theorem isNearIdentity_one (s : U.algebra) {ε : ℝ} (hε : 0 ≤ ε) :
    U.IsNearIdentity 1 s ε := by
  let K := X.field
  let A := U.atlas.presentation.atlas
  let T := (compatibleExtend (𝟙 K)).obj U.atlas
  let q : T ⟶ U.atlas := (compatibleExtendId K).app U.atlas
  let : NormedAlgebra K K := (𝟙 K : K ⟶ K).normedAlgebra
  have hq (i : T.presentation.atlas.Index) :
      q.baseMap '' range (T.presentation.atlas.chart i) ⊆ range (A.chart U.chart) := by
    change projection K K A '' range ((chartSystem K K A).chart i) ⊆ range (A.chart U.chart)
    exact (projection_image_chart K K A i).le.trans (U.contains i)
  have hf (i : T.presentation.atlas.Index) :
      (𝟙 T : T ⟶ T).baseMap '' range (T.presentation.atlas.chart i) ⊆
        range (T.presentation.atlas.chart U.chart) := by
    change id '' range (T.presentation.atlas.chart i) ⊆
      range (T.presentation.atlas.chart U.chart)
    rw [image_id]
    exact (range_chart_subset_iff K K A i U.chart).2 (U.contains i)
  refine ⟨1, ?_, T, q, 𝟙 T, unitCompatibleMap_isQuasiIso K U.atlas.presentation,
    ?_, hq, hf, ?_⟩
  · change 𝟙 _ ≫ U.arrow = U.arrow ≫ 𝟙 _
    simp
  · let e := (localizedExtendId K).app (localizationFunctor.obj U.atlas)
    change localizationFunctor.map q ≫ e.inv = localizationFunctor.map (𝟙 T)
    have he : localizationFunctor.map q = e.hom := (localizedExtendId_hom_app U.atlas).symm
    calc
      _ = e.hom ≫ e.inv :=
        congrArg (fun m : localizationFunctor.obj T ⟶ localizationFunctor.obj U.atlas =>
          m ≫ e.inv) he
      _ = 𝟙 (localizationFunctor.obj T) := e.hom_inv_id
      _ = _ := (localizationFunctor.map_id T).symm
  · intro i x
    have h (j : A.Index) := U.contains j
    change x (((IndexedAffinoidAtlas.GroundFieldExtension.restriction K K A
      i U.chart (h i)) (iota K K U.algebra s)) -
      PresentedAffinoidAlgebra.GroundFieldExtension.unitEquiv K (A.algebra i)
        (A.restriction i U.chart (h i) s)) ≤ ε
    rw [unitEquiv_apply, IndexedAffinoidAtlas.GroundFieldExtension.restriction,
      PresentedAffinoidAlgebra.GroundFieldExtension.map_iota, sub_self, map_zero]
    exact hε

/-- A passing test preserves the image of the probe on analytic points. -/
theorem image_eq_of_isNearIdentity {σ : Aut X} {s : U.algebra} {ε : ℝ}
    (h : U.IsNearIdentity σ s ε) :
    underlyingMap σ.asIso.hom '' range (underlyingMap U.arrow) =
      range (underlyingMap U.arrow) := by
  obtain ⟨a, ha, _⟩ := h
  have he := congrArg (fun f => underlyingSpaceFunctor.map f) ha
  rw [Functor.map_comp, Functor.map_comp] at he
  let e := TopCat.homeoOfIso (underlyingSpaceFunctor.mapIso a.asIso)
  have hcomm x : underlyingMap U.arrow (e x) =
      underlyingMap σ.asIso.hom (underlyingMap U.arrow x) :=
    congrArg (fun (f : _ ⟶ underlyingSpaceFunctor.obj X) => f x) he
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, hcomm x⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective y
    exact ⟨underlyingMap U.arrow x, mem_range_self x, (hcomm x).symm⟩

end SemilinearAffinoidProbe

variable {X} {G : Type z} [Group G] [TopologicalSpace G]

/-- The compact-domain and function criterion at the identity, tested on
affinoid probes with their full bounded section algebras. -/
def IsContinuousSemilinearAction (ρ : G →* Aut X) : Prop :=
  ∀ (U : SemilinearAffinoidProbe X) (s : U.algebra) (ε : ℝ), 0 < ε →
    ∀ᶠ g in 𝓝 (1 : G), U.IsNearIdentity (ρ g) s ε

end Langlands.Analytic.SpaceOverField
