import Langlands.GroupScheme.Rational.RootInversionCover
import Langlands.GroupScheme.Rational.RootFactorPairSymmetry
import Langlands.GroupScheme.Rational.RootFactorPairConsequences
import Langlands.GroupScheme.Rational.CyclicWeightFiltrationProof
import Langlands.GroupScheme.Rational.CyclicRootFunctorComparisonProof
import Langlands.GroupScheme.Rational.RepresentedLieUniqueness

/-! # Nonmultipliable opposite-factor consequences from absent higher roots -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- None of the second or later positive multiples of this character
is an actual relative root. -/
def HasNoHigherRoots (i : T.toGrp ⟶ G) (a : characterLattice T) : Prop :=
  ∀ n : ℕ, 2 ≤ n → n • a ∉ relativeRoots i

/-- A root-free semigroup generates only the identity subgroup. This uses
the actual tangent decomposition of each generator, with no realization
premise for the generated functor. -/
theorem semigroupSubgroup_eq_bot_of_ambientWeights_vanish
    [LocallyOfFiniteType G.X.hom] (b : AutomorphicAction T.toGrp G)
    (hT : IsSplitTorus T.toGrp) (A : AddSubsemigroup (characterLattice T))
    (hA : HasNoAmbientWeights b A) : semigroupSubgroup b A = ⊥ := by
  apply le_antisymm ?_ (fun _ => bot_le)
  apply (semigroupSubgroup_le_iff b A ⊥).mpr
  intro F hF
  have hspan : semigroupWeightSpan b A = ⊥ :=
    semigroupWeightSpan_eq_bot_of_noAmbientWeights b A hA
  have htan : tangentSubmodule F = ⊥ := by
    apply eq_bot_iff.mpr
    rw [← hspan]
    exact (hF.1.actionWeightSupport_subset_iff_tangentSubmodule_le b hT hF.2.1 A).mp
      hF.2.2
  have hLie : HasLieImage F ⊥ :=
    (hasLieImage_iff_tangentSubmodule_eq F ⊥).mpr htan
  have heq : (⊥ : SubgroupFunctor G) = F :=
    bot_isSmoothConnectedClosed.eq_of_le_of_hasLieImage hF.1 (fun _ => bot_le)
      bot_hasLieImage hLie
  exact le_of_eq heq.symm

/-- Root-free positive multiples make the second cyclic tail trivial
without the general semigroup realization statement. -/
theorem weightFiltration_two_eq_bot_of_noHigherRoots
    (hG : Smooth G.X.hom) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0)
    (hhigh : HasNoHigherRoots i a) :
    weightFiltration (AutomorphicAction.conjugation i) a 2 = ⊥ := by
  let : Smooth G.X.hom := hG
  apply semigroupSubgroup_eq_bot_of_ambientWeights_vanish _ hT
  rintro χ ⟨n, hn, hn0, rfl⟩ hχ
  exact hhigh n hn ((mem_actionWeightSupport_conjugation_iff i
    (hT.nsmul_ne_zero ha (by omega))).mp hχ)

/-- Published cyclic comparison, smooth root representability and cyclic
filtration give inversion for a root with no higher positive multiple. -/
theorem isInversionPoint_of_noHigherRoots
    (hG : Smooth G.X.hom) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0)
    (hhigh : HasNoHigherRoots i a)
    {U : Over (Spec (CommRingCat.of k))} (s : U ⟶ T.X)
    (hs : (Gm.pointsEquiv _ U (s ≫ (CommGroupScheme.groupHom a).hom.hom) :
      Γ(U.left, ⊤)) = -1) : IsInversionPoint i a s := by
  let : Smooth G.X.hom := hG
  let b := AutomorphicAction.conjugation i
  have hfirst : weightFiltration b a 1 = subgroup i a :=
    cyclicRootFunctorComparison k G hG inferInstance T hT i a ha
  have htwo : weightFiltration b a 2 = ⊥ :=
    weightFiltration_two_eq_bot_of_noHigherRoots hG hT i ha hhigh
  obtain ⟨H, j, hj, _⟩ := subgroup_isSmoothConnectedClosed_of_ne_zero hT i a ha
  have hrep : (weightFiltration b a 1).IsRepresentedBy j := hfirst.symm ▸ hj
  obtain ⟨V, q, c, d, hq, hc, hjd, hqd⟩ :=
    (cyclicWeightFiltration k G hG inferInstance T hT b a ha 1 (by omega)).2 H j hrep
  let : Mono j.hom.hom := hj.1
  have hq0 : IsFppfQuotient ⊥ q := by
    simpa only [show 1 + 1 = (2 : ℕ) from rfl, htwo,
      SubgroupFunctor.comap_bot_of_mono] using hq
  have hc' : HasUniqueWeightVectorStructure c a := by simpa only [one_nsmul] using hc
  intro g hg
  apply conj_eq_inv_of_equivariantVectorQuotient i a j q c d hq0 hc' hjd hqd s hs
  rwa [hj.2]

/-- No higher roots on either side give a common fpqc inversion point,
with all cyclic structure inputs discharged by published theorems. -/
theorem hasFpqcInversionPoint_of_noHigherRoots_actual
    (hG : Smooth G.X.hom) (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    {a : characterLattice T} (ha : a ≠ 0)
    (hpos : HasNoHigherRoots i a)
    (hneg : HasNoHigherRoots i (-a)) :
    HasFpqcInversionPoint i a := by
  obtain ⟨U, q, hqc, hf, hsurj, s, hs⟩ := exists_fpqc_character_neg_one hT ha
  refine ⟨U, q, hqc, hf, hsurj, s, ?_, ?_⟩
  · exact isInversionPoint_of_noHigherRoots hG hT i ha hpos s hs
  · exact isInversionPoint_of_noHigherRoots hG hT i (neg_ne_zero.mpr ha) hneg s
      (character_neg_eq_neg_one s hs)

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- A common fpqc inversion point forces equal opposite factors, since
uniqueness at the rational inverse point is automatic for a supplied pair. -/
theorem HasFpqcInversionPoint.hasEqualOppositeFactors
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    (hinv : HasFpqcInversionPoint i a) : HasEqualOppositeFactors i a := by
  obtain ⟨U, q, hqc, hf, hsurj, s, hpos, hneg⟩ := hinv
  let : QuasiCompact q.left := hqc
  let : Flat q.left := hf
  let : Surjective q.left := hsurj
  intro x hx hx1 p hp
  have hxinv : x⁻¹ ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) :=
    Subgroup.inv_mem _ hx
  have hxinv1 : x⁻¹ ≠ 1 := inv_ne_one.mpr hx1
  have hunique : ∃! r, IsOppositeFactorPair i a x⁻¹ r := by
    refine ⟨(p.2⁻¹, p.1⁻¹), hp.inv i, ?_⟩
    intro r hr
    exact hr.eq i hT ha hxinv hxinv1 (hp.inv i)
  exact hp.fst_eq_snd_of_local_inversion i hunique q s
    (hpos ((subgroup i a).comp_mem q hx))
    (hneg ((subgroup i (-a)).comp_mem q hp.1))
    (hneg ((subgroup i (-a)).comp_mem q hp.2.1))

/-- Common local inversion gives all three additional conclusions for
a supplied opposite pair: equality, conjugation and the actual torus square. -/
theorem IsOppositeFactorPair.nonmultipliable_consequences_of_fpqcInversion
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    (hinv : HasFpqcInversionPoint i a)
    {x : rationalPoints G}
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p) :
    p.1 = p.2 ∧
      p.1 = (p.1 * x * p.2)⁻¹ * x * (p.1 * x * p.2) ∧
      (p.1 * x * p.2) * (p.1 * x * p.2) ∈ (rationalPoints.map i).range := by
  have hsym := hinv.hasEqualOppositeFactors i hT ha
  have heq := hsym x hx hx1 p hp
  refine ⟨heq, hp.fst_eq_conj_of_equal_factors i hsym hx
    (hp.factors_ne_one i hT ha hx hx1).1
    (hp.weylAction_eq_neg i hT ha hx hx1) heq, ?_⟩
  obtain ⟨U, q, hqc, hf, hsurj, s, hpos, hneg⟩ := hinv
  let : QuasiCompact q.left := hqc
  let : Flat q.left := hf
  let : Surjective q.left := hsurj
  apply square_mem_torus_of_local_inversion i ⟨p.1 * x * p.2, hp.2.2⟩ q s
  have hxq := hpos ((subgroup i a).comp_mem q hx)
  have hp₁q := hneg ((subgroup i (-a)).comp_mem q hp.1)
  have hp₂q := hneg ((subgroup i (-a)).comp_mem q hp.2.1)
  simp only [MonObj.comp_mul]
  calc
    _ = ((s ≫ i.hom.hom) * (q ≫ p.1) * (s ≫ i.hom.hom)⁻¹) *
        ((s ≫ i.hom.hom) * (q ≫ x) * (s ≫ i.hom.hom)⁻¹) *
        ((s ≫ i.hom.hom) * (q ≫ p.2) * (s ≫ i.hom.hom)⁻¹) := by group
    _ = (q ≫ p.1)⁻¹ * (q ≫ x)⁻¹ * (q ≫ p.2)⁻¹ := by rw [hp₁q, hxq, hp₂q]
    _ = _ := by rw [← heq]; simp only [mul_inv_rev, mul_assoc]

/-- With higher roots absent on both sides, published cyclic geometry gives
the three additional factor and square identities for every supplied pair. -/
theorem IsOppositeFactorPair.nonmultipliable_consequences_of_noHigherRoots
    (hG : Smooth G.X.hom) (hT : IsSplitTorus T.toGrp)
    {a : characterLattice T} (ha : a ≠ 0)
    (hpos : HasNoHigherRoots i a)
    (hneg : HasNoHigherRoots i (-a))
    {x : rationalPoints G}
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1)
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p) :
    p.1 = p.2 ∧
      p.1 = (p.1 * x * p.2)⁻¹ * x * (p.1 * x * p.2) ∧
      (p.1 * x * p.2) * (p.1 * x * p.2) ∈ (rationalPoints.map i).range :=
  hp.nonmultipliable_consequences_of_fpqcInversion i hT ha
    (hasFpqcInversionPoint_of_noHigherRoots_actual hG hT i ha hpos hneg) hx hx1

end Langlands.GroupScheme.RelativeRoot
