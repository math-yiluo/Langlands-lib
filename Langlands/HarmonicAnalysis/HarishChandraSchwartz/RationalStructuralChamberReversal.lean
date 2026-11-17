import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTerm
import Langlands.BruhatTits.SpecialCompact.WeakIwahoriBasisReduction

/-! # Reversal of the structural data used by the actual constant-term estimate -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

section Groups

variable {H : Type*} [Group H]

/-- Inversion reverses the ordered factors of an Iwahori decomposition. -/
theorem HasIwahoriIntersectionDecomposition.reverse
    {K M N Nbar : Subgroup H} (h : HasIwahoriIntersectionDecomposition K M N Nbar) :
    HasIwahoriIntersectionDecomposition K M Nbar N := by
  let e : ↥(K ⊓ N) × ↥(K ⊓ M) × ↥(K ⊓ Nbar) ≃
      ↥(K ⊓ Nbar) × ↥(K ⊓ M) × ↥(K ⊓ N) :=
    { toFun := fun x => (x.2.2⁻¹, x.2.1⁻¹, x.1⁻¹)
      invFun := fun x => (x.2.2⁻¹, x.2.1⁻¹, x.1⁻¹)
      left_inv := by rintro ⟨x, y, z⟩; simp
      right_inv := by rintro ⟨x, y, z⟩; simp }
  have hb := (Equiv.inv K).bijective.comp (h.comp e.bijective)
  have heq : orderedIntersectionProduct K M Nbar N =
      (Equiv.inv K) ∘ orderedIntersectionProduct K M N Nbar ∘ e := by
    funext x
    apply Subtype.ext
    change (x.1 : H) * (x.2.1 : H) * (x.2.2 : H) =
      ((x.2.2 : H)⁻¹ * (x.2.1 : H)⁻¹ * (x.1 : H)⁻¹)⁻¹
    group
  change Function.Bijective (orderedIntersectionProduct K M Nbar N)
  rw [heq]
  exact hb

end Groups

section Rational

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Negating the face and reversing the chamber keeps the exact Levi subgroup. -/
theorem standardLeviPoints_reversed (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) :
    standardLeviPoints i (-ν) (Neg.neg '' J) = standardLeviPoints i ν J := by
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG S i hi ν hν J hJ).1
  exact congrArg (fun H : SubgroupFunctor G => H.carrier (Over.mk (𝟙 _)))
    (standardSubgroups_reversedChamber i ν standardCocharacter hG hi hν
      (relativeRootNegation F G hG S i hi) hζ).2.1

omit [LocallyOfFiniteType G.X.hom] in
/-- Inverting a split-torus chamber point negates its character inequalities. -/
theorem inv_mem_CAplus_neg_image {A : CommGroupScheme (Spec (CommRingCat.of F))}
    {R : Set (characterLattice A)} {a : rationalPoints A.toGrp}
    (ha : a ∈ CocharacterUniformizer.CAplus F A R) :
    a⁻¹ ∈ CocharacterUniformizer.CAplus F A (Neg.neg '' R) := by
  refine ⟨(CocharacterUniformizer.CA F A).inv_mem ha.1, ?_⟩
  rintro _ ⟨α, hα, rfl⟩
  rw [componentCharacterNorm_neg_inv]
  exact ha.2 α hα

omit [LocallyOfFiniteType G.X.hom] in
/-- Inversion reverses the weak chamber of a compatible split component. -/
theorem inv_mem_standardComponentCAplus_reversed
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {m : rationalPoints G} (hm : m ∈ standardComponentCAplus i ν J q) :
    m⁻¹ ∈ standardComponentCAplus i (-ν) (Neg.neg '' J) q := by
  obtain ⟨a, ha, rfl⟩ := hm
  refine ⟨a⁻¹, ?_, map_inv (rationalPoints.map (q ≫ i)) a⟩
  rw [standardParabolicComponentCharacters_reversed i ν hneg]
  exact inv_mem_CAplus_neg_image ha

omit [LocallyOfFiniteType G.X.hom] in
/-- Reversal preserves the complete simultaneous basis at the same compact subgroup. -/
theorem simultaneousStandardBasisAt_reversed (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0) :
    SimultaneousStandardBasisAt i (-ν) K0 := by
  have hneg := relativeRootNegation F G hG S i hi
  obtain ⟨B, hB, hBJ⟩ := hbasis
  refine ⟨B, hB, fun J' hJ' => ?_⟩
  let J := Neg.neg '' J'
  have hJJ : Neg.neg '' J = J' := by
    simp only [J, Set.image_image, neg_neg, Set.image_id']
  have hJ : J ⊆ simpleRelativeRoots i ν := by
    rintro _ ⟨α, hα, rfl⟩
    simpa only [neg_neg] using neg_mem_simpleRelativeRoots i (-ν) hneg (hJ' hα)
  obtain ⟨hInherited, A, q, hA, hmem⟩ := hBJ J hJ
  have hMrev : standardLeviPoints i (-ν) J' = standardLeviPoints i ν J := by
    rw [← hJJ]
    exact standardLeviPoints_reversed hG hi hν hJ
  have hArev : IsCompatibleStandardSplitComponent i (-ν) J' A q := by
    simpa only [hJJ] using hA.reversed i ν hG hi hν hJ
  refine ⟨?_, A, q, hArev, fun H hH => ?_⟩
  · rw [hMrev]
    exact hInherited
  · have hUrev : standardUnipotentPoints i (-ν) J' =
        standardOppositeUnipotentPoints i ν J := by rw [← hJJ]
    have hOrev : standardOppositeUnipotentPoints i (-ν) J' =
        standardUnipotentPoints i ν J := by
      simp only [standardOppositeUnipotentPoints, neg_neg, J]
    have hweak : WeakChamberContraction H (standardUnipotentPoints i (-ν) J')
        (standardOppositeUnipotentPoints i (-ν) J') (standardComponentCAplus i (-ν) J' q) := by
      intro m hm
      have hm' : m⁻¹ ∈ standardComponentCAplus i ν J q := by
        simpa only [neg_neg, J] using
          inv_mem_standardComponentCAplus_reversed (ν := -ν) hneg hm
      have hw := (hmem H hH).2.2.1 m⁻¹ hm'
      rw [hUrev, hOrev]
      simpa only [inv_inv] using And.intro hw.2 hw.1
    refine ⟨?_, hArev.contractionAndCofinality_of_weak i (-ν) hG hi (hν.neg i ν)
      hJ' H (hB.1 H hH).2.2.1 (hB.1 H hH).2.2.2 hweak⟩
    rw [hMrev, hUrev, hOrev]
    exact HasIwahoriIntersectionDecomposition.reverse (hmem H hH).1

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The simple roots in the reversed chamber are the negatives of the original ones. -/
theorem simpleRelativeRoots_reversed (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) :
    simpleRelativeRoots i (-ν) = Neg.neg '' simpleRelativeRoots i ν := by
  have hneg := relativeRootNegation F G hG S i hi
  ext α
  constructor
  · intro hα
    refine ⟨-α, ?_, neg_neg α⟩
    simpa only [neg_neg] using neg_mem_simpleRelativeRoots i (-ν) hneg hα
  · rintro ⟨α, hα, rfl⟩
    exact neg_mem_simpleRelativeRoots i ν hneg hα

omit [LocallyOfFiniteType G.X.hom] in
/-- Inversion reverses a finite Cartan covering without changing its compact subgroup. -/
theorem finiteCartanCovering_reversed (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) {K0 : Subgroup (rationalPoints G)}
    (hcover : Aubert.General.RationalPointFamily.FiniteCartanCovering F i ν K0) :
    Aubert.General.RationalPointFamily.FiniteCartanCovering F i (-ν) K0 := by
  classical
  obtain ⟨F0, hF0⟩ := hcover
  refine ⟨F0.image Inv.inv, fun g => ?_⟩
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hg⟩ := hF0 g⁻¹
  refine ⟨k₂⁻¹, k₁⁻¹, f⁻¹, a⁻¹, K0.inv_mem hk₂, K0.inv_mem hk₁,
    Finset.mem_image_of_mem _ hf, ?_, ?_⟩
  · rw [simpleRelativeRoots_reversed hG hi]
    exact inv_mem_CAplus_neg_image ha
  · have hcomm := congrArg Inv.inv
      ((centralizerPoints_le_pointCentralizer i f.2 _
        ((mem_torusPoints i _).mpr ⟨a, rfl⟩)).symm)
    simp only [mul_inv_rev] at hcomm
    change (rationalPoints.map i a)⁻¹ * (f : rationalPoints G)⁻¹ =
      (f : rationalPoints G)⁻¹ * (rationalPoints.map i a)⁻¹ at hcomm
    calc g = k₂⁻¹ * ((rationalPoints.map i a)⁻¹ * (f : rationalPoints G)⁻¹) * k₁⁻¹ := by
          rw [← inv_inv g, hg]
          group
      _ = _ := by rw [hcomm, map_inv]; simp only [Subgroup.coe_inv, mul_assoc]

omit [LocallyOfFiniteType G.X.hom] in
/-- The same inversion argument reverses the covering inside a standard Levi. -/
theorem standardLeviCartanCovering_reversed (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν) {K0 : Subgroup (rationalPoints G)}
    (hcover : StandardLeviCartanCovering F i ν J K0) :
    StandardLeviCartanCovering F i (-ν) (Neg.neg '' J) K0 := by
  classical
  obtain ⟨F0, hF0⟩ := hcover
  have hMrev := standardLeviPoints_reversed hG hi hν hJ
  refine ⟨F0.image Inv.inv, fun m hm => ?_⟩
  rw [hMrev] at hm
  obtain ⟨k₁, k₂, f, a, hk₁, hk₂, hf, ha, hg⟩ :=
    hF0 m⁻¹ ((standardLeviPoints i ν J).inv_mem hm)
  refine ⟨k₂⁻¹, k₁⁻¹, f⁻¹, a⁻¹, ?_, ?_, Finset.mem_image_of_mem _ hf,
    inv_mem_CAplus_neg_image ha, ?_⟩
  · rw [hMrev]
    exact (K0 ⊓ standardLeviPoints i ν J).inv_mem hk₂
  · rw [hMrev]
    exact (K0 ⊓ standardLeviPoints i ν J).inv_mem hk₁
  · have hcomm := congrArg Inv.inv
      ((centralizerPoints_le_pointCentralizer i f.2 _
        ((mem_torusPoints i _).mpr ⟨a, rfl⟩)).symm)
    simp only [mul_inv_rev] at hcomm
    change (rationalPoints.map i a)⁻¹ * (f : rationalPoints G)⁻¹ =
      (f : rationalPoints G)⁻¹ * (rationalPoints.map i a)⁻¹ at hcomm
    calc m = k₂⁻¹ * ((rationalPoints.map i a)⁻¹ * (f : rationalPoints G)⁻¹) * k₁⁻¹ := by
          rw [← inv_inv m, hg]
          group
      _ = _ := by rw [hcomm, map_inv]; simp only [Subgroup.coe_inv, mul_assoc]

end Rational

/-- Reversal preserves the three supplied structural properties of the same subgroup. -/
def RationalStructuralChamberReversalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ K0 : Subgroup (rationalPoints G),
      (SimultaneousStandardBasisAt i ν K0 → SimultaneousStandardBasisAt i (-ν) K0) ∧
      (FiniteCartanCovering F i ν K0 → FiniteCartanCovering F i (-ν) K0) ∧
      ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
        StandardLeviCartanCovering F i ν J K0 →
          StandardLeviCartanCovering F i (-ν) (Neg.neg '' J) K0

/-- Structural chamber reversal on actual points, at arbitrary field universe. -/
theorem rationalStructuralChamberReversal : RationalStructuralChamberReversalStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K0
  exact ⟨simultaneousStandardBasisAt_reversed hG hi hν,
    finiteCartanCovering_reversed hG hi,
    fun J hJ => standardLeviCartanCovering_reversed hG hi hν hJ⟩

end Langlands.HarishChandraSchwartz
