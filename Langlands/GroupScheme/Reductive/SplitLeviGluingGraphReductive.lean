import Langlands.GroupScheme.Reductive.SplitLeviGluingRankOneGraphClosure
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGeneration
import Langlands.GroupScheme.CentralIsogeny.SemisimpleTransfer
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.HomImage

/-! # Faithfully flat graph projections and reductivity of the actual graph -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]

section SimpleProjection

variable {G D : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth D.X.hom] [IsAffineHom D.X.hom] [ConnectedSpace D.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    {J : Type v} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

/-- A smooth connected affine homomorphism containing the simple-root Levi
factors of its target is faithfully flat, quasi-compact and locally finitely presented. -/
theorem projection_geometry_of_contains_simpleRootLevis
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hP : IsRootDatumOf i P) {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (p : D ⟶ G)
    (hpos : ∀ a ∈ simpleRelativeRoots i ν,
      RelativeRoot.subgroup i a ≤ SubgroupFunctor.range p)
    (hneg : ∀ a ∈ simpleRelativeRoots i ν,
      RelativeRoot.subgroup i (-a) ≤ SubgroupFunctor.range p)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) ≤ SubgroupFunctor.range p) :
    Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      LocallyOfFinitePresentation p.hom.hom.left ∧ QuasiCompact p.hom.hom.left := by
  obtain ⟨E, j, q, hj, hqj, hflat, hsurj, hqc, hlfp, _, _, _⟩ := HomImage.exists_image p
  have hle : SubgroupFunctor.range p ≤ SubgroupFunctor.range j := by
    rw [← hqj]
    intro W x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ q.hom.hom, by
      rw [Grp.comp_hom_hom, Category.assoc]⟩
  let : IsIso j := isIso_of_simpleRootLevis hT hi hP hν j hj
    (fun a ha => (hpos a ha).trans hle) (fun a ha => (hneg a ha).trans hle) (hZ.trans hle)
  let : IsIso j.hom := inferInstanceAs (IsIso ((Grp.forget₂Mon _).map j))
  let : IsIso j.hom.hom := inferInstanceAs (IsIso ((Mon.forget _).map j.hom))
  let : IsIso j.hom.hom.left := inferInstanceAs (IsIso ((Over.forget _).map j.hom.hom))
  let : Flat q.hom.hom.left := hflat
  let : Surjective q.hom.hom.left := hsurj
  let : QuasiCompact q.hom.hom.left := hqc
  let : LocallyOfFinitePresentation q.hom.hom.left := hlfp
  have heq : q.hom.hom.left ≫ j.hom.hom.left = p.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) hqj
  rw [← heq]
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end SimpleProjection

section NormalUnipotentImage

variable [IsAlgClosed k]
    {D C U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom D.X.hom] [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (p : D ⟶ C) [Epi p.hom.hom.left]
    (hC : HasTrivialUnipotentRadical C)
    (i : U ⟶ D) (hi : IsClosedSubgroup i)
    (hs : Smooth U.X.hom) (hc : ConnectedSpace U.X.left)
    (hu : IsUnipotent U) (hn : (SubgroupFunctor.range i).IsNormal)

omit [IsAlgClosed k] in
include hC hi hs hc hu hn in
/-- An epimorphic homomorphism to a group with trivial unipotent radical kills
every smooth connected normal unipotent closed subgroup of its source. -/
theorem normal_unipotent_comp_eq_one : i.hom.hom ≫ p.hom.hom = 1 := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : Smooth U.X.hom := hs
  let : IsAffineHom U.X.hom := hi.isAffineHom
  let : IsAffine U.X.left := isAffine_of_isAffineHom U.X.hom
  have hUint : GeometricallyIntegral U.X.hom :=
    smoothConnectedAffineGeometry.1 k U hs inferInstance hc
  let f : U ⟶ C := i ≫ p
  have horigin : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X) ≫ f.hom.hom = 1 :=
    MonObj.one_comp _
  obtain ⟨E, hE⟩ := ImageGeneration.pointedImageGeneration k C inferInstance inferInstance U.X
    inferInstance inferInstance hUint 1 f.hom.hom horigin
  let : Smooth E.group.X.hom := hE.1
  let : IsAffineHom E.group.X.hom := hE.2.1
  let : GeometricallyConnected E.group.X.hom := hE.2.2.1
  have hEc : ConnectedSpace E.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := E.group.X.hom)
  let q := E.factorGroupHom f
  obtain ⟨n, _, hDom⟩ := hE.2.2.2
  let : IsDominant q.hom.hom.left := E.factorGroupHom_isDominant f n hDom
  let : IsReduced E.group.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k E.group.X.left E.group.X.hom
  let : IsSchemeTheoreticallyDominant q.hom.hom.left :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  let : IsAffine E.group.X.left := isAffine_of_isAffineHom E.group.X.hom
  let : QuasiCompact q.hom.hom.left := inferInstance
  have hEu : IsUnipotent E.group :=
    hu.of_appTop_injective q (q.hom.hom.left.app_injective ⊤)
  let c : AutomorphicAction D D := AutomorphicAction.conjugation (𝟙 D)
  have hrep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hstab : c.IsStable (SubgroupFunctor.range i) := by
    intro W h g hg
    rw [AutomorphicAction.conjugation_act, Grp.id_hom_hom, Category.comp_id]
    exact hn W h g (Subgroup.mem_top _) hg
  let a := c.onRepresentedSubgroup i hrep hstab
  let b : AutomorphicAction D C := AutomorphicAction.conjugation p
  have hif : a.toPointwiseSchemeAction.IsEquivariant b.toPointwiseSchemeAction f.hom.hom := by
    intro W s x
    change a.act s x ≫ (i.hom.hom ≫ p.hom.hom) = b.act s (x ≫ (i.hom.hom ≫ p.hom.hom))
    rw [← Category.assoc, AutomorphicAction.onRepresentedSubgroup_act_comp,
      AutomorphicAction.conjugation_act, AutomorphicAction.conjugation_act,
      Grp.id_hom_hom, Category.comp_id, MonObj.mul_comp, MonObj.mul_comp,
      GrpObj.inv_comp, Category.assoc]
  have hstabE : b.IsStable (closedImageEnvelope f.hom.hom) :=
    b.closedImageEnvelope_isStable inferInstance a.toPointwiseSchemeAction f.hom.hom hif
  have hN : (SubgroupFunctor.range E.inclusion).normalizer.HasClosedRepresentative :=
    (hasClosedRepresentative_normalizer_centralizer_range E.inclusion E.closed).1
  let : Epi p.hom.hom := Over.epi_of_epi_left _
  have hpN : SubgroupFunctor.range p ≤ (SubgroupFunctor.range E.inclusion).normalizer := by
    intro W x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    intro V a' z hz
    rw [E.represents.2] at hz ⊢
    constructor
    · have h := hstabE V (a' ≫ y) z hz
      rw [AutomorphicAction.conjugation_act] at h
      simpa only [Category.assoc] using h
    · have h := hstabE V (a' ≫ y)⁻¹ z hz
      rw [AutomorphicAction.conjugation_act, GrpObj.inv_comp, inv_inv] at h
      simpa only [Category.assoc] using h
  have hNtop := SubgroupFunctor.eq_top_of_hasClosedRepresentative_of_range_le hN p hpN
  have hEn : (SubgroupFunctor.range E.inclusion).IsNormal :=
    SubgroupFunctor.isNormal_of_normalizer_eq_top hNtop
  have hEbot := hC E.group E.inclusion E.closed hE.1 hEc hEu hEn
  have hincl : E.inclusion.hom.hom = 1 := by
    have h1 : 𝟙 E.group.X ≫ E.inclusion.hom.hom ∈
        (SubgroupFunctor.range E.inclusion).carrier E.group.X :=
      SubgroupFunctor.mem_range.mpr ⟨𝟙 _, rfl⟩
    rw [hEbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot, Category.id_comp] at h1
    exact h1
  have h := congrArg (fun g => g.hom.hom) (E.factorGroupHom_comp f)
  change q.hom.hom ≫ E.inclusion.hom.hom = i.hom.hom ≫ p.hom.hom at h
  rw [← h, hincl, MonObj.comp_one]

end NormalUnipotentImage

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}
    (D : SimpleComparisonGraph i₁ i₂)

namespace SimpleComparisonGraph

/-- The first actual projection contains every positive simple-root functor. -/
theorem positive_le_range_first (a : D.SimpleIndex) :
    RelativeRoot.subgroup i₁ (a : characterLattice T) ≤ SubgroupFunctor.range D.envelope.first := by
  rw [← (D.positive_first_rep a).2]
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ (D.positiveHom a).hom.hom, by
    rw [Grp.comp_hom_hom, Category.assoc]⟩

theorem negative_le_range_first (a : D.SimpleIndex) :
    RelativeRoot.subgroup i₁ (-(a : characterLattice T)) ≤ SubgroupFunctor.range D.envelope.first := by
  rw [← (D.negative_first_rep a).2]
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ (D.negativeHom a).hom.hom, by
    rw [Grp.comp_hom_hom, Category.assoc]⟩

theorem positive_le_range_second (a : D.SimpleIndex) :
    RelativeRoot.subgroup i₂ (a : characterLattice T) ≤ SubgroupFunctor.range D.envelope.second := by
  rw [← (D.positive_second_rep a).2]
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ (D.positiveHom a).hom.hom, by
    rw [Grp.comp_hom_hom, Category.assoc]⟩

theorem negative_le_range_second (a : D.SimpleIndex) :
    RelativeRoot.subgroup i₂ (-(a : characterLattice T)) ≤ SubgroupFunctor.range D.envelope.second := by
  rw [← (D.negative_second_rep a).2]
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ (D.negativeHom a).hom.hom, by
    rw [Grp.comp_hom_hom, Category.assoc]⟩

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
theorem torus_le_range_first : SubgroupFunctor.range i₁ ≤ SubgroupFunctor.range D.envelope.first := by
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ D.envelope.torusLift.hom.hom, by
    rw [Category.assoc, ← Grp.comp_hom_hom, D.envelope.torusLift_first]⟩

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
theorem torus_le_range_second : SubgroupFunctor.range i₂ ≤ SubgroupFunctor.range D.envelope.second := by
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ D.envelope.torusLift.hom.hom, by
    rw [Category.assoc, ← Grp.comp_hom_hom, D.envelope.torusLift_second]⟩

variable {J₁ : Type v} {J₂ : Type w}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁) (hP₂ : IsRootDatumOf i₂ P₂)
    (hroots : roots i₁ = roots i₂)

include hP₁ in
/-- First projection geometry, with the ambient middle-factor identity explicit. -/
theorem first_geometry [ConnectedSpace G₁.X.left] (hi₁ : IsClosedSubgroup i₁)
    (hZ₁ : Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i₁) =
      SubgroupFunctor.range i₁) :
    Flat D.envelope.first.hom.hom.left ∧ Surjective D.envelope.first.hom.hom.left ∧
      LocallyOfFinitePresentation D.envelope.first.hom.hom.left ∧
        QuasiCompact D.envelope.first.hom.hom.left := by
  exact projection_geometry_of_contains_simpleRootLevis D.split hi₁ hP₁ D.directions.generic
    D.envelope.first (fun a ha => D.positive_le_range_first ⟨a, ha⟩)
    (fun a ha => D.negative_le_range_first ⟨a, ha⟩) (by rw [hZ₁]; exact D.torus_le_range_first)

include hP₂ hroots in
/-- Second projection geometry; equal root sets transport the actual simple indices. -/
theorem second_geometry [ConnectedSpace G₂.X.left] (hi₂ : IsClosedSubgroup i₂)
    (hZ₂ : Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i₂) =
      SubgroupFunctor.range i₂) :
    Flat D.envelope.second.hom.hom.left ∧ Surjective D.envelope.second.hom.hom.left ∧
      LocallyOfFinitePresentation D.envelope.second.hom.hom.left ∧
        QuasiCompact D.envelope.second.hom.hom.left := by
  have hsimp : simpleRelativeRoots i₁ D.directions.chamber =
      simpleRelativeRoots i₂ D.directions.chamber := by
    unfold simpleRelativeRoots positiveRelativeRoots
    rw [show relativeRoots i₁ = relativeRoots i₂ from hroots]
  have hν₂ : IsGenericCocharacter i₂ D.directions.chamber := by
    intro a ha
    apply D.directions.generic a
    change a ∈ roots i₁
    rw [hroots]
    exact ha
  exact projection_geometry_of_contains_simpleRootLevis D.split hi₂ hP₂ hν₂
    D.envelope.second (fun a ha => D.positive_le_range_second ⟨a, hsimp.symm ▸ ha⟩)
    (fun a ha => D.negative_le_range_second ⟨a, hsimp.symm ▸ ha⟩)
    (by rw [hZ₂]; exact D.torus_le_range_second)

variable [IsAlgClosed k]
    (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (hmax₁ : IsMaximalTorus i₁) (hmax₂ : IsMaximalTorus i₂)

omit [IsAlgClosed k] in
include hP₁ hG₁ hmax₁ in
theorem first_geometry_of_reductive :
    Flat D.envelope.first.hom.hom.left ∧ Surjective D.envelope.first.hom.hom.left ∧
      LocallyOfFinitePresentation D.envelope.first.hom.hom.left ∧
        QuasiCompact D.envelope.first.hom.hom.left := by
  let : ConnectedSpace G₁.X.left := hG₁.connectedSpace
  exact D.first_geometry P₁ hP₁ hmax₁.2.1
    (D.chamber_centralizer_eq_range_of_reductiveCentralizers
      dynamicCentralizerReductive hG₁ hmax₁)

omit [IsAlgClosed k] in
include hP₂ hroots hG₂ hmax₂ in
theorem second_geometry_of_reductive :
    Flat D.envelope.second.hom.hom.left ∧ Surjective D.envelope.second.hom.hom.left ∧
      LocallyOfFinitePresentation D.envelope.second.hom.hom.left ∧
        QuasiCompact D.envelope.second.hom.hom.left := by
  let : ConnectedSpace G₂.X.left := hG₂.connectedSpace
  have hν₂ : IsGenericCocharacter i₂ D.directions.chamber := by
    intro a ha
    apply D.directions.generic a
    change a ∈ roots i₁
    rw [hroots]
    exact ha
  have hself := maximalTorusCentralizer_of_structuralInputs dynamicCentralizerReductive
    noTorusUnipotent solvableTorusQuotient k G₂ hG₂ T i₂ hmax₂
  have hZ₂ : Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i₂) =
      SubgroupFunctor.range i₂ :=
    (genericCentralizer k G₂ hG₂ T i₂ (hmax₂.isMaximalSplitTorus D.split)
      D.directions.chamber hν₂).trans hself
  exact D.second_geometry P₂ hP₂ hroots hmax₂.2.1 hZ₂

include hP₁ hP₂ hroots hG₁ hG₂ hmax₁ hmax₂ in
/-- The actual generated graph is reductive: normal unipotent subgroups map
trivially in both faithfully flat reductive projections and hence are trivial. -/
theorem isConnectedReductive : IsConnectedReductive D.envelope.group := by
  have hg₁ := D.first_geometry_of_reductive P₁ hP₁ hG₁ hmax₁
  have hg₂ := D.second_geometry_of_reductive P₂ hP₂ hroots hG₂ hmax₂
  let : Flat D.envelope.first.hom.hom.left := hg₁.1
  let : Surjective D.envelope.first.hom.hom.left := hg₁.2.1
  let : Flat D.envelope.second.hom.hom.left := hg₂.1
  let : Surjective D.envelope.second.hom.hom.left := hg₂.2.1
  let : Epi D.envelope.first.hom.hom.left := Flat.epi_of_flat_of_surjective _
  let : Epi D.envelope.second.hom.hom.left := Flat.epi_of_flat_of_surjective _
  apply IsPseudoReductive.isConnectedReductive_of_isAlgClosed
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro U j hj hs hc hu hn
  have h₁ := normal_unipotent_comp_eq_one D.envelope.first
    hG₁.isPseudoReductive.hasTrivialUnipotentRadical j hj hs hc hu hn
  have h₂ := normal_unipotent_comp_eq_one D.envelope.second
    hG₂.isPseudoReductive.hasTrivialUnipotentRadical j hj hs hc hu hn
  have hj1 : j.hom.hom = 1 := by
    apply D.envelope.points_ext
    · rw [h₁, MonObj.one_comp]
    · rw [h₂, MonObj.one_comp]
  apply SubgroupFunctor.ext
  intro W
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change y ≫ j.hom.hom = 1
    rw [hj1, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

end SimpleComparisonGraph

/-- An actual comparison graph certified reductive, together with the
faithfully flat geometry of both actual projections. -/
structure ReductiveSimpleComparisonGraph where
  graph : SimpleComparisonGraph i₁ i₂
  reductive : IsConnectedReductive graph.envelope.group
  firstGeometry : Flat graph.envelope.first.hom.hom.left ∧
    Surjective graph.envelope.first.hom.hom.left ∧
    LocallyOfFinitePresentation graph.envelope.first.hom.hom.left ∧
    QuasiCompact graph.envelope.first.hom.hom.left
  secondGeometry : Flat graph.envelope.second.hom.hom.left ∧
    Surjective graph.envelope.second.hom.hom.left ∧
    LocallyOfFinitePresentation graph.envelope.second.hom.hom.left ∧
    QuasiCompact graph.envelope.second.hom.hom.left

/-- Construct the certified actual reductive graph directly from the split
common-torus local comparison hypothesis and realizing ambient root data. -/
def reductiveSimpleComparisonGraph [IsAlgClosed k]
    (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (hT : IsSplitTorus T.toGrp) (hmax₁ : IsMaximalTorus i₁) (hmax₂ : IsMaximalTorus i₂)
    {J₁ : Type v} {J₂ : Type w}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁) (hP₂ : IsRootDatumOf i₂ P₂)
    (hroots : roots i₁ = roots i₂) (hlocal : RankOneLeviHypothesis i₁ i₂) :
    ReductiveSimpleComparisonGraph (i₁ := i₁) (i₂ := i₂) := by
  let : ConnectedSpace G₁.X.left := hG₁.connectedSpace
  let D := simpleComparisonGraph i₁ i₂ hT hlocal
  exact ⟨D, D.isConnectedReductive P₁ P₂ hP₁ hP₂ hroots hG₁ hG₂ hmax₁ hmax₂,
    D.first_geometry_of_reductive P₁ hP₁ hG₁ hmax₁,
    D.second_geometry_of_reductive P₂ hP₂ hroots hG₂ hmax₂⟩

end Langlands.GroupScheme.LeviGluing
