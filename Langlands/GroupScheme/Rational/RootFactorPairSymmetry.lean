import Langlands.GroupScheme.Rational.RootSubgroupInversion
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Rational.CharacterFpqcProof
import Langlands.GroupScheme.SubgroupFunctor.FpqcMembership

/-! # Equal opposite factors and torus squares from local inversion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G)

/-- Every normalizing opposite pair for a nonidentity point of the actual
root subgroup has equal factors. Existence is not part of this predicate. -/
def HasEqualOppositeFactors (a : characterLattice T) : Prop :=
  ∀ (x : rationalPoints G),
    x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) → x ≠ 1 →
    ∀ (p : rationalPoints G × rationalPoints G),
      IsOppositeFactorPair i a x p → p.1 = p.2

/-- Inversion reverses the order of an opposite factor pair. -/
theorem IsOppositeFactorPair.inv {a : characterLattice T}
    {x : rationalPoints G} {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p) :
    IsOppositeFactorPair i a x⁻¹ (p.2⁻¹, p.1⁻¹) := by
  refine ⟨Subgroup.inv_mem _ hp.2.1, Subgroup.inv_mem _ hp.1, ?_⟩
  simpa only [mul_inv_rev, mul_assoc] using
    (normalizerPoints i).inv_mem hp.2.2

variable [Mono i.hom.hom.left]

/-- Local inversion of the three factors produces a second rational
opposite pair for the inverse point, by fpqc descent of normalization. -/
theorem IsOppositeFactorPair.inv_same_order_of_local_inversion
    {a : characterLattice T} {x : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p)
    {U : Over (Spec (CommRingCat.of k))}
    (q : U ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))))
    [QuasiCompact q.left] [Flat q.left] [Surjective q.left]
    (s : U ⟶ T.X)
    (hx : (s ≫ i.hom.hom) * (q ≫ x) * (s ≫ i.hom.hom)⁻¹ = (q ≫ x)⁻¹)
    (hp₁ : (s ≫ i.hom.hom) * (q ≫ p.1) * (s ≫ i.hom.hom)⁻¹ = (q ≫ p.1)⁻¹)
    (hp₂ : (s ≫ i.hom.hom) * (q ≫ p.2) * (s ≫ i.hom.hom)⁻¹ = (q ≫ p.2)⁻¹) :
    IsOppositeFactorPair i a x⁻¹ (p.1⁻¹, p.2⁻¹) := by
  refine ⟨Subgroup.inv_mem _ hp.1, Subgroup.inv_mem _ hp.2.1, ?_⟩
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  apply torusNormalizer_le_normalizerPoints i
  apply SubgroupFunctor.mem_torusNormalizer_of_comp_mem i q
  have ht : s ≫ i.hom.hom ∈ (torusNormalizer i).carrier U :=
    SubgroupFunctor.le_normalizer _ U (SubgroupFunctor.mem_range.mpr ⟨s, rfl⟩)
  have hm : q ≫ (p.1 * x * p.2) ∈ (torusNormalizer i).carrier U :=
    (torusNormalizer i).comp_mem q (normalizerPoints_le_torusNormalizer i hp.2.2)
  have heq : q ≫ (p.1⁻¹ * x⁻¹ * p.2⁻¹) =
      (s ≫ i.hom.hom) * (q ≫ (p.1 * x * p.2)) * (s ≫ i.hom.hom)⁻¹ := by
    simp only [MonObj.comp_mul, GrpObj.comp_inv]
    calc
      _ = ((s ≫ i.hom.hom) * (q ≫ p.1) * (s ≫ i.hom.hom)⁻¹) *
          ((s ≫ i.hom.hom) * (q ≫ x) * (s ≫ i.hom.hom)⁻¹) *
          ((s ≫ i.hom.hom) * (q ≫ p.2) * (s ≫ i.hom.hom)⁻¹) := by
            rw [hp₁, hx, hp₂]
      _ = _ := by group
  rw [heq]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hm) (Subgroup.inv_mem _ ht)

/-- Rational uniqueness at the inverse point and a local inversion point
force equality of the original two factors. -/
theorem IsOppositeFactorPair.fst_eq_snd_of_local_inversion
    {a : characterLattice T} {x : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p)
    (hunique : ∃! r, IsOppositeFactorPair i a x⁻¹ r)
    {U : Over (Spec (CommRingCat.of k))}
    (q : U ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))))
    [QuasiCompact q.left] [Flat q.left] [Surjective q.left]
    (s : U ⟶ T.X)
    (hx : (s ≫ i.hom.hom) * (q ≫ x) * (s ≫ i.hom.hom)⁻¹ = (q ≫ x)⁻¹)
    (hp₁ : (s ≫ i.hom.hom) * (q ≫ p.1) * (s ≫ i.hom.hom)⁻¹ = (q ≫ p.1)⁻¹)
    (hp₂ : (s ≫ i.hom.hom) * (q ≫ p.2) * (s ≫ i.hom.hom)⁻¹ = (q ≫ p.2)⁻¹) :
    p.1 = p.2 := by
  have heq := hunique.unique
    (hp.inv_same_order_of_local_inversion i q s hx hp₁ hp₂) (hp.inv i)
  exact inv_injective (congrArg Prod.fst heq)

/-- A normalizer inverted by a local torus point has square in the actual
rational torus image. The image membership, rather than a lift of an
arbitrary quotient point, is descended. -/
theorem square_mem_torus_of_local_inversion
    (m : normalizerPoints i) {U : Over (Spec (CommRingCat.of k))}
    (q : U ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))))
    [QuasiCompact q.left] [Flat q.left] [Surjective q.left]
    (s : U ⟶ T.X)
    (hm : (s ≫ i.hom.hom) * (q ≫ m.val) * (s ≫ i.hom.hom)⁻¹ = (q ≫ m.val)⁻¹) :
    m.val * m.val ∈ (rationalPoints.map i).range := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  change m.val * m.val ∈ (SubgroupFunctor.range i).carrier (Over.mk (𝟙 _))
  apply SubgroupFunctor.mem_range_of_comp_mem_range i q
  have ht : s ≫ i.hom.hom ∈ (SubgroupFunctor.range i).carrier U :=
    SubgroupFunctor.mem_range.mpr ⟨s, rfl⟩
  have hn : q ≫ m.val ∈ (torusNormalizer i).carrier U :=
    (torusNormalizer i).comp_mem q (normalizerPoints_le_torusNormalizer i m.2)
  have hconj := SubgroupFunctor.conj_mem_of_mem_normalizer hn ht
  have hinv : (s ≫ i.hom.hom) * (q ≫ m.val)⁻¹ * (s ≫ i.hom.hom)⁻¹ =
      q ≫ m.val := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using congrArg Inv.inv hm
  have heq : q ≫ (m.val * m.val) =
      (q ≫ m.val) * (s ≫ i.hom.hom) * (q ≫ m.val)⁻¹ * (s ≫ i.hom.hom)⁻¹ := by
    rw [MonObj.comp_mul]
    calc
      _ = (q ≫ m.val) *
          ((s ≫ i.hom.hom) * (q ≫ m.val)⁻¹ * (s ≫ i.hom.hom)⁻¹) := by rw [hinv]
      _ = _ := by group
  rw [heq]
  exact Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ ht)

/-- Equal-factor symmetry for all points of a root subgroup gives the
conjugation formula for a pair whose product negates that character. -/
theorem IsOppositeFactorPair.fst_eq_conj_of_equal_factors
    {a : characterLattice T} (hsym : HasEqualOppositeFactors i a)
    {x : rationalPoints G} (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p) (hp₁ : p.1 ≠ 1)
    (hn : weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) a = -a)
    (heq : p.1 = p.2) :
    p.1 = (p.1 * x * p.2)⁻¹ * x * (p.1 * x * p.2) := by
  let m : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have hma : weylAction i m⁻¹ (-a) = a := by
    rw [← hn, map_inv]
    exact (weylAction i m).symm_apply_apply a
  have hmneg : weylAction i m⁻¹ a = -a := by
    have h := congrArg (fun z => -z) hma
    simpa only [map_neg, neg_neg] using h
  have hv : m.val⁻¹ * p.1 * m.val ∈ (subgroup i a).carrier (Over.mk (𝟙 _)) := by
    have h := normalizer_conj_mem i (-a) m⁻¹ hp.1
    simpa only [G.constantPoint_self, Subgroup.coe_inv, inv_inv, hma] using h
  have hu : m.val⁻¹ * x * m.val ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) := by
    have h := normalizer_conj_mem i a m⁻¹ hx
    simpa only [G.constantPoint_self, Subgroup.coe_inv, inv_inv, hmneg] using h
  have hv1 : m.val⁻¹ * p.1 * m.val ≠ 1 := by
    intro h
    apply hp₁
    have h' := congrArg (fun z => m.val * z * m.val⁻¹) h
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one,
      inv_mul_cancel_left, mul_one, mul_one, mul_inv_cancel] using h'
  have hprod : p.1 * (m.val⁻¹ * p.1 * m.val) *
      (m.val⁻¹ * x * m.val) = m.val := by
    dsimp [m]
    rw [← heq]
    group
  exact hsym _ hv hv1 (p.1, m.val⁻¹ * x * m.val)
    ⟨hp.1, hu, by
      change p.1 * (m.val⁻¹ * p.1 * m.val) *
        (m.val⁻¹ * x * m.val) ∈ normalizerPoints i
      rw [hprod]
      exact m.2⟩

end Langlands.GroupScheme.RelativeRoot
