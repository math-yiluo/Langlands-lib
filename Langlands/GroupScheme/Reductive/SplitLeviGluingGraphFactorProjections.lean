import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphDynamicFactors
import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphReductive
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleUnipotent
import Langlands.GroupScheme.Dynamic.SignedParabolicComparison

/-! # Actual faithfully flat maps on graph unipotent factors -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]

section Restriction

variable {H G A B : GroupScheme (Spec (CommRingCat.of k))}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ H)
    (f : H ⟶ G) (a : A ⟶ H) (b : B ⟶ G)
    (ha : (Dynamic.unipotent χ).IsRepresentedBy a)
    (hb : (Dynamic.unipotent (χ ≫ f)).IsRepresentedBy b)

/-- The actual restriction of a group homomorphism to supplied representatives
of its source and target dynamic unipotent factors. -/
def unipotentRestriction : A ⟶ B :=
  hb.factorHom (a ≫ f) (by
    intro W x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    have hy : y ≫ a.hom.hom ∈ (Dynamic.unipotent χ).carrier W := by
      rw [← ha.2]
      exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
    have h := Dynamic.unipotent_le_comap χ f W hy
    simpa only [SubgroupFunctor.mem_comap, Grp.comp_hom_hom, Category.assoc] using h)

@[reassoc (attr := simp)]
theorem unipotentRestriction_comp : unipotentRestriction χ f a b ha hb ≫ b = a ≫ f :=
  hb.factorHom_comp _ _

end Restriction

section Geometry

variable [IsAlgClosed k]
    {G A B : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth A.X.hom] [IsAffineHom A.X.hom] [ConnectedSpace A.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    {J : Type v} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    {ν : cocharacterLattice T}
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hP : IsRootDatumOf i P) (hν : IsGenericCocharacter i ν)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = SubgroupFunctor.range i)
    (b : B ⟶ G) (hb : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy b)
    (hbc : IsClosedSubgroup b) (p : A ⟶ B)
    (hpos : ∀ a ∈ simpleRelativeRoots i ν,
      RelativeRoot.subgroup i a ≤ SubgroupFunctor.range (p ≫ b))

include hT hi hP hν hZ hb hbc hpos in
/-- A map into a dynamic unipotent representative is faithfully flat once
its ambient composite contains every simple root subgroup. -/
theorem unipotent_projection_geometry :
    Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
      LocallyOfFinitePresentation p.hom.hom.left ∧ QuasiCompact p.hom.hom.left := by
  let : IsAffineHom B.X.hom := hbc.isAffineHom
  let : Smooth B.X.hom := (dynamicSmooth k G _ _ b).2.2 hb
  obtain ⟨E, j, q, hj, hqj, hflat, hsurj, hqc, hlfp, _, _, _⟩ := HomImage.exists_image p
  have hjb : IsClosedSubgroup (j ≫ b) := hj.comp hbc
  have hle : SubgroupFunctor.range (p ≫ b) ≤ SubgroupFunctor.range (j ≫ b) := by
    rw [← hqj]
    intro W x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ q.hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  have hfull := unipotent_le_range_of_simpleRoots_of_centralizer_eq hT hi hP hν hZ
    (j ≫ b) hjb (fun a ha => (hpos a ha).trans hle)
  have hjle : SubgroupFunctor.range (j ≫ b) ≤ Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i) := by
    rw [← hb.2]
    intro W x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ j.hom.hom, by
      rw [Grp.comp_hom_hom, Category.assoc]⟩
  let : IsClosedImmersion (j ≫ b).hom.hom.left := hjb
  have hjrep : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy
      (j ≫ b) := ⟨Over.mono_of_mono_left _, le_antisymm hjle hfull⟩
  let e := hjrep.isoOfIsRepresentedBy hb
  have hej : e.hom = j := hb.hom_ext (hjrep.isoOfIsRepresentedBy_hom_comp hb)
  let : IsIso j := hej ▸ (inferInstance : IsIso e.hom)
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

end Geometry

section OppositeSimple

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    {J : Type v} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}

/-- Negating a simple root and its chamber preserves simplicity. -/
theorem neg_mem_simpleRelativeRoots (hP : IsRootDatumOf i P)
    {ν : cocharacterLattice T} {a : characterLattice T}
    (ha : a ∈ simpleRelativeRoots i ν) : -a ∈ simpleRelativeRoots i (-ν) := by
  have hpos : ∀ b ∈ positiveRelativeRoots i ν, -b ∈ positiveRelativeRoots i (-ν) := by
    intro b hb
    exact ⟨neg_mem_roots hP hb.1, by
      simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hb.2⟩
  have hneg : ∀ b ∈ positiveRelativeRoots i (-ν), -b ∈ positiveRelativeRoots i ν := by
    intro b hb
    refine ⟨neg_mem_roots hP hb.1, ?_⟩
    simpa only [map_neg, LinearMap.neg_apply] using hb.2
  refine ⟨hpos a ha.1, ?_⟩
  rintro ⟨b, hb, c, hc, he⟩
  apply ha.2
  refine ⟨-b, hneg b hb, -c, hneg c hc, ?_⟩
  simpa only [neg_neg, neg_add] using congrArg Neg.neg he

end OppositeSimple

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}
    (D : SimpleComparisonGraph i₁ i₂)

namespace SimpleComparisonGraph
namespace GraphDynamicFactors

variable {D} (E : D.GraphDynamicFactors)

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
/-- A generic actual graph unipotent inclusion followed by an ambient projection
contains the corresponding full simple root group. -/
theorem root_le_range_comp {A : GroupScheme (Spec (CommRingCat.of k))}
    {a : A ⟶ D.envelope.group} (ha : IsClosedSubgroup a)
    {L : GroupScheme (Spec (CommRingCat.of k))} (r : L ⟶ D.envelope.group)
    (hr : SubgroupFunctor.range r ≤ SubgroupFunctor.range a)
    {G : GroupScheme (Spec (CommRingCat.of k))} (p : D.envelope.group ⟶ G)
    {F : SubgroupFunctor G} (hF : F.IsRepresentedBy (r ≫ p)) :
    F ≤ SubgroupFunctor.range (a ≫ p) := by
  let : IsClosedImmersion a.hom.hom.left := ha
  have har : (SubgroupFunctor.range a).IsRepresentedBy a := ⟨Over.mono_of_mono_left _, rfl⟩
  let q := har.factorHom r hr
  have hq : q ≫ a = r := har.factorHom_comp r hr
  rw [← hF.2, ← hq, Category.assoc]
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ q.hom.hom, by
    simp only [Grp.comp_hom_hom, Category.assoc]⟩

end GraphDynamicFactors
end SimpleComparisonGraph

local instance affine_of_affineHom {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

section ProjectionData

variable {H G A : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual restricted map into the canonical ambient unipotent factor,
with its inclusion square and faithfully flat geometry. -/
structure UnipotentProjectionData (p : H ⟶ G) (a : A ⟶ H)
    (ν : cocharacterLattice T) (i : T.toGrp ⟶ G) where
  hom : A ⟶ Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ν ≫ i)
  comp : hom ≫ Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ i) = a ≫ p
  geometry : Flat hom.hom.hom.left ∧ Surjective hom.hom.hom.left ∧
    LocallyOfFinitePresentation hom.hom.hom.left ∧ QuasiCompact hom.hom.hom.left

variable [IsAlgClosed k] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    [Smooth A.X.hom] [IsAffineHom A.X.hom] [ConnectedSpace A.X.left]

/-- Construct the actual unipotent restriction and its quotient geometry
from actual simple-root containment in the composite range. -/
def unipotentProjectionData (p : H ⟶ G) (a : A ⟶ H)
    (t : T.toGrp ⟶ H) (i : T.toGrp ⟶ G) (ht : t ≫ p = i)
    (ν : cocharacterLattice T)
    (ha : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t)).IsRepresentedBy a)
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    {J : Type v} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (hν : IsGenericCocharacter i ν)
    (hZ : Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = SubgroupFunctor.range i)
    (hpos : ∀ b ∈ simpleRelativeRoots i ν,
      RelativeRoot.subgroup i b ≤ SubgroupFunctor.range (a ≫ p)) :
    UnipotentProjectionData p a ν i := by
  let b := Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ i)
  have hb := Dynamic.Affine.isRepresentedBy_unipotentHom (CommGroupScheme.groupHom ν ≫ i)
  have hb' : (Dynamic.unipotent ((CommGroupScheme.groupHom ν ≫ t) ≫ p)).IsRepresentedBy b := by
    rw [Category.assoc, ht]
    exact hb
  let q := unipotentRestriction (CommGroupScheme.groupHom ν ≫ t) p a b ha hb'
  have hq : q ≫ b = a ≫ p := unipotentRestriction_comp _ _ _ _ _ _
  have hg := unipotent_projection_geometry hT hi hP hν hZ b hb
    (Dynamic.Affine.isClosedSubgroup_unipotentHom _) q
    (fun b hb => by rw [hq]; exact hpos b hb)
  exact ⟨q, hq, hg⟩

end ProjectionData

namespace SimpleComparisonGraph
namespace GraphDynamicFactors

variable {D} (E : D.GraphDynamicFactors)
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (i : T.toGrp ⟶ G) (p : D.envelope.group ⟶ G)
    (ht : D.envelope.torusLift ≫ p = i)
    (hroots : roots i₁ = roots i)
    {J : Type v} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : IsRootDatumOf i P) (hG : IsConnectedReductive G) (hmax : IsMaximalTorus i)

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
  [Smooth G.X.hom] [ConnectedSpace G.X.left] in
include hroots in
private theorem target_generic : IsGenericCocharacter i D.directions.chamber := by
  intro a ha
  apply D.directions.generic a
  change a ∈ roots i₁
  rw [hroots]
  exact ha

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
  [Smooth G.X.hom] [ConnectedSpace G.X.left] in
include hroots in
private theorem target_simple_eq : simpleRelativeRoots i₁ D.directions.chamber =
    simpleRelativeRoots i D.directions.chamber := by
  unfold simpleRelativeRoots positiveRelativeRoots
  rw [show relativeRoots i₁ = relativeRoots i from hroots]

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
  [Smooth G.X.hom] [ConnectedSpace G.X.left] in
include hroots hG hmax in
private theorem target_centralizer_eq :
    Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i) =
      SubgroupFunctor.range i := by
  have hself := maximalTorusCentralizer_of_structuralInputs dynamicCentralizerReductive
    noTorusUnipotent solvableTorusQuotient k G hG T i hmax
  exact (genericCentralizer k G hG T i (hmax.isMaximalSplitTorus D.split)
    D.directions.chamber (target_generic (D := D) i hroots)).trans hself

/-- The actual restriction of either graph projection on its full positive
factor is faithfully flat when its simple-root composites represent the target roots. -/
def positiveProjectionData [IsAlgClosed k]
    (hrep : ∀ a : D.SimpleIndex, (RelativeRoot.subgroup i (a : characterLattice T)).IsRepresentedBy
      (D.positiveHom a ≫ p)) :
    UnipotentProjectionData p E.positive.inclusion D.directions.chamber i := by
  apply unipotentProjectionData p E.positive.inclusion D.envelope.torusLift i ht
    D.directions.chamber E.positiveRep D.split hmax.2.1 hP
    (target_generic (D := D) i hroots) (target_centralizer_eq (D := D) i hroots hG hmax)
  intro a ha
  let a' : D.SimpleIndex := ⟨a, (target_simple_eq (D := D) i hroots).symm ▸ ha⟩
  exact root_le_range_comp E.positive.closed (D.positiveHom a')
    (by rw [E.positiveRep.2]; exact D.positive_le_unipotent a') p (hrep a')

/-- The corresponding actual restriction on the full opposite graph factor. -/
def negativeProjectionData [IsAlgClosed k]
    (hrep : ∀ a : D.SimpleIndex, (RelativeRoot.subgroup i (-(a : characterLattice T))).IsRepresentedBy
      (D.negativeHom a ≫ p)) :
    UnipotentProjectionData p E.negative.inclusion (-D.directions.chamber) i := by
  have haU : (Dynamic.unipotent (CommGroupScheme.groupHom (-D.directions.chamber) ≫
      D.envelope.torusLift)).IsRepresentedBy E.negative.inclusion := by
    rw [groupHom_neg_comp_eq_oppositeCocharacter]
    exact E.negativeRep
  have hν : IsGenericCocharacter i (-D.directions.chamber) := by
    intro a ha
    rw [map_neg]
    exact neg_ne_zero.mpr (target_generic (D := D) i hroots a ha)
  have hZ : Dynamic.centralizer (CommGroupScheme.groupHom (-D.directions.chamber) ≫ i) =
      SubgroupFunctor.range i := by
    rw [Dynamic.centralizer_groupHom_neg]
    exact target_centralizer_eq (D := D) i hroots hG hmax
  apply unipotentProjectionData p E.negative.inclusion D.envelope.torusLift i ht
    (-D.directions.chamber) haU D.split hmax.2.1 hP hν hZ
  intro a ha
  have hn := neg_mem_simpleRelativeRoots hP ha
  simp only [neg_neg] at hn
  let a' : D.SimpleIndex := ⟨-a, (target_simple_eq (D := D) i hroots).symm ▸ hn⟩
  have hr := hrep a'
  change (RelativeRoot.subgroup i (-(-a))).IsRepresentedBy (D.negativeHom a' ≫ p) at hr
  rw [neg_neg] at hr
  exact root_le_range_comp E.negative.closed (D.negativeHom a')
    (by
      rw [E.negativeRep.2]
      simpa only [groupHom_neg_comp_eq_oppositeCocharacter, Dynamic.oppositeCocharacter,
        Category.assoc] using D.negative_le_unipotent a') p hr

end GraphDynamicFactors

/-- All four actual unipotent factor restrictions and their quotient geometry. -/
structure GraphFactorProjections (E : D.GraphDynamicFactors) where
  positiveFirst : UnipotentProjectionData D.envelope.first E.positive.inclusion D.directions.chamber i₁
  negativeFirst : UnipotentProjectionData D.envelope.first E.negative.inclusion (-D.directions.chamber) i₁
  positiveSecond : UnipotentProjectionData D.envelope.second E.positive.inclusion D.directions.chamber i₂
  negativeSecond : UnipotentProjectionData D.envelope.second E.negative.inclusion (-D.directions.chamber) i₂

/-- Construct all four actual faithfully flat restriction maps from the full
graph factors and the reductive ambient simple-root generation theorems. -/
def graphFactorProjectionsOfReductive [IsAlgClosed k] (E : D.GraphDynamicFactors)
    {J₁ : Type v} {J₂ : Type w}
    (P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T))
    (P₂ : RootDatum J₂ (characterLattice T) (cocharacterLattice T))
    (hP₁ : IsRootDatumOf i₁ P₁) (hP₂ : IsRootDatumOf i₂ P₂)
    (hroots : roots i₁ = roots i₂)
    (hG₁ : IsConnectedReductive G₁) (hG₂ : IsConnectedReductive G₂)
    (hmax₁ : IsMaximalTorus i₁) (hmax₂ : IsMaximalTorus i₂) : D.GraphFactorProjections E := by
  let : ConnectedSpace G₁.X.left := hG₁.connectedSpace
  let : ConnectedSpace G₂.X.left := hG₂.connectedSpace
  exact ⟨
    E.positiveProjectionData i₁ D.envelope.first D.envelope.torusLift_first rfl P₁ hP₁ hG₁ hmax₁
      D.positive_first_rep,
    E.negativeProjectionData i₁ D.envelope.first D.envelope.torusLift_first rfl P₁ hP₁ hG₁ hmax₁
      D.negative_first_rep,
    E.positiveProjectionData i₂ D.envelope.second D.envelope.torusLift_second hroots P₂ hP₂ hG₂ hmax₂
      D.positive_second_rep,
    E.negativeProjectionData i₂ D.envelope.second D.envelope.torusLift_second hroots P₂ hP₂ hG₂ hmax₂
      D.negative_second_rep⟩

end SimpleComparisonGraph

end Langlands.GroupScheme.LeviGluing
