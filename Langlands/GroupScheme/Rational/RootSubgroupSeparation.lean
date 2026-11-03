import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement
import Langlands.GroupScheme.Rational.BruhatPointReduction
import Langlands.GroupScheme.Rational.BruhatOppositeCellReduction

/-! # Separation of actual opposite root subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom]

/-- Opposite root subgroups of a split torus have trivial intersection on every
scheme, for an arbitrary affine ambient group. -/
theorem eq_one_of_mem_subgroup_of_mem_opposite
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier U)
    (hg' : g ∈ (subgroup i (-a)).carrier U) : g = 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, hD, ν, hν⟩ := hT.exists_pairing_eq_pos ha
  have hpos : 0 < latticePairing T a ν := by omega
  have hneg : 0 < latticePairing T (-a) (-ν) := by simpa using hpos
  have hminus := subgroup_le_dynamicUnipotent i (-ν) hneg U hg'
  rw [groupHom_neg_comp_eq_oppositeCocharacter i ν] at hminus
  exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
    (CommGroupScheme.groupHom ν ≫ i) hminus
    (Dynamic.unipotent_le_parabolic _ U (subgroup_le_dynamicUnipotent i ν hpos U hg))

/-- The all-test subgroup functors for a nonzero character and its negative
are disjoint. -/
theorem subgroup_inf_opposite_eq_bot
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0) :
    subgroup i a ⊓ subgroup i (-a) = ⊥ := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  change (g ∈ (subgroup i a).carrier U ∧ g ∈ (subgroup i (-a)).carrier U) ↔ g = 1
  constructor
  · exact fun hg => eq_one_of_mem_subgroup_of_mem_opposite i hT ha hg.1 hg.2
  · rintro rfl
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

/-- Multiplication of points in opposite root subgroups is injective on
every test scheme. -/
theorem oppositeMultiplication_injective
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    (U : Over (Spec (CommRingCat.of k))) :
    Function.Injective (fun p : (subgroup i a).carrier U ×
        (subgroup i (-a)).carrier U => (p.1 : U ⟶ G.X) * p.2) := by
  intro p q hpq
  change (p.1 : U ⟶ G.X) * (p.2 : U ⟶ G.X) =
    (q.1 : U ⟶ G.X) * (q.2 : U ⟶ G.X) at hpq
  have hrel : (q.1 : U ⟶ G.X)⁻¹ * p.1 =
      (q.2 : U ⟶ G.X) * (p.2 : U ⟶ G.X)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).mpr
    rw [mul_assoc, hpq, inv_mul_cancel_left]
  have hpos : (q.1 : U ⟶ G.X)⁻¹ * p.1 ∈ (subgroup i a).carrier U :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ q.1.property) p.1.property
  have hneg : (q.1 : U ⟶ G.X)⁻¹ * p.1 ∈ (subgroup i (-a)).carrier U := by
    rw [hrel]
    exact Subgroup.mul_mem _ q.2.property (Subgroup.inv_mem _ p.2.property)
  have h1 : (p.1 : U ⟶ G.X) = q.1 :=
    (inv_mul_eq_one.mp (eq_one_of_mem_subgroup_of_mem_opposite i hT ha hpos hneg)).symm
  have h2 : (p.2 : U ⟶ G.X) = q.2 := by
    rw [h1] at hpq
    exact mul_left_cancel hpq
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

/-- The actual multiplication embedding for opposite root points on a test
scheme; no represented root subgroup is chosen. -/
def oppositeMultiplicationEmbedding
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    (U : Over (Spec (CommRingCat.of k))) :
    ((subgroup i a).carrier U × (subgroup i (-a)).carrier U) ↪ (U ⟶ G.X) where
  toFun p := (p.1 : U ⟶ G.X) * p.2
  inj' := oppositeMultiplication_injective i hT ha U

/-- A root point cannot also admit a limit along a cocharacter pairing
negatively with its character. -/
theorem eq_one_of_mem_subgroup_of_mem_negative_parabolic
    {a : characterLattice T} (ν : cocharacterLattice T)
    (hpos : 0 < latticePairing T a ν)
    {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X}
    (hg : g ∈ (subgroup i a).carrier U)
    (hgP : g ∈ (Dynamic.parabolic
      (CommGroupScheme.groupHom (-ν) ≫ i)).carrier U) : g = 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  apply Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic
    (CommGroupScheme.groupHom (-ν) ≫ i) _ hgP
  rw [← groupHom_neg_comp_eq_oppositeCocharacter i (-ν), neg_neg]
  exact subgroup_le_dynamicUnipotent i ν hpos U hg

/-- A normalizer which is a product of two opposite root points is the
identity, without any Weyl-action assumption. -/
theorem normalizer_eq_one_of_mul_opposite
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    (n : normalizerPoints i) {x y : rationalPoints G}
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hy : y ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)))
    (hn : n.val = x * y) : n = 1 := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨D, hD, ν, hν⟩ := hT.exists_pairing_eq_pos ha
  have hpos : 0 < latticePairing T a ν := by omega
  have hneg : 0 < latticePairing T (-a) (-ν) := by simpa using hpos
  apply normalizer_eq_one_of_unipotent_product i (-ν) n
    ⟨x, ?_⟩ ⟨y, subgroup_le_dynamicUnipotent i (-ν) hneg _ hy⟩ hn
  change x ∈ (Dynamic.unipotent
    (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom (-ν) ≫ i))).carrier _
  rw [← groupHom_neg_comp_eq_oppositeCocharacter i (-ν), neg_neg]
  exact subgroup_le_dynamicUnipotent i ν hpos _ hx

/-- Both factors of a normalizing opposite pair for a nonidentity root
point are nonidentity, without a reflection premise. -/
theorem IsOppositeFactorPair.factors_ne_one
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    {x : rationalPoints G} (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hx1 : x ≠ 1) {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p) : p.1 ≠ 1 ∧ p.2 ≠ 1 := by
  let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  constructor
  · intro hp1
    have hn1 := normalizer_eq_one_of_mul_opposite i hT ha n hx hp.2.1
      (by simp [n, hp1])
    have heq : x * p.2 = 1 := by
      simpa [n, hp1] using congrArg Subtype.val hn1
    have hxopp : x ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) := by
      rw [mul_eq_one_iff_eq_inv.mp heq]
      exact Subgroup.inv_mem _ hp.2.1
    exact hx1 (eq_one_of_mem_subgroup_of_mem_opposite i hT ha hx hxopp)
  · intro hp2
    have hn1 := normalizer_eq_one_of_mul_opposite i hT (neg_ne_zero.mpr ha) n hp.1
      (by simpa only [neg_neg] using hx) (by simp [n, hp2])
    have heq : p.1 * x = 1 := by
      simpa [n, hp2] using congrArg Subtype.val hn1
    have hxopp : x ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) := by
      have h : x = p.1⁻¹ := by
        simpa only [← mul_assoc, inv_mul_cancel, one_mul, mul_one] using
          congrArg (fun z => p.1⁻¹ * z) heq
      rw [h]
      exact Subgroup.inv_mem _ hp.1
    exact hx1 (eq_one_of_mem_subgroup_of_mem_opposite i hT ha hx hxopp)

variable [Mono i.hom.hom.left]

/-- A root-flipping normalizer cannot itself lie in that root subgroup. -/
theorem normalizer_not_mem_subgroup_of_flip
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    (n : normalizerPoints i) (hn : weylAction i n a = -a) :
    n.val ∉ (subgroup i a).carrier (Over.mk (𝟙 _)) := by
  intro hna
  have hnminus := normalizer_conj_mem i a n hna
  simp only [G.constantPoint_self, mul_inv_cancel_right, hn] at hnminus
  have hone : n = 1 := Subtype.ext
    (eq_one_of_mem_subgroup_of_mem_opposite i hT ha hna hnminus)
  rw [hone, map_one] at hn
  change a = -a at hn
  obtain ⟨D, hD, ν, hν⟩ := hT.exists_pairing_eq_pos ha
  have h := congrArg (fun b => latticePairing T b ν) hn
  simp only [map_neg, LinearMap.neg_apply, hν] at h
  omega

/-- A root-flipping normalizer cannot be a product of one positive and one
negative root point. -/
theorem normalizer_ne_mul_opposite_of_flip
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    (n : normalizerPoints i) (hn : weylAction i n a = -a)
    {x y : rationalPoints G}
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    (hy : y ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _))) :
    n.val ≠ x * y := by
  intro hxy
  have hnminus : weylAction i n (-a) = a := by rw [map_neg, hn, neg_neg]
  have hc := normalizer_conj_mem i (-a) n
    ((subgroup i (-a)).carrier _ |>.inv_mem hy)
  simp only [G.constantPoint_self, hnminus] at hc
  apply normalizer_not_mem_subgroup_of_flip i hT ha n hn
  have hm := ((subgroup i a).carrier _).mul_mem
    (((subgroup i a).carrier _).inv_mem hc) hx
  simpa [hxy, mul_assoc] using hm

/-- Both factors of a normalizing opposite pair are nonidentity whenever
its normalizer negates the character. -/
theorem IsOppositeFactorPair.factors_ne_one_of_flip
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    {x : rationalPoints G} (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _)))
    {p : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p)
    (hn : weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) a = -a) :
    p.1 ≠ 1 ∧ p.2 ≠ 1 := by
  let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have hnminus : weylAction i n (-a) = a := by rw [map_neg, hn, neg_neg]
  constructor
  · intro hp1
    apply normalizer_ne_mul_opposite_of_flip i hT ha n hn hx hp.2.1
    simp [n, hp1]
  · intro hp2
    apply normalizer_ne_mul_opposite_of_flip i hT (neg_ne_zero.mpr ha) n
      (by simpa only [neg_neg] using hnminus) hp.1
      (by simpa only [neg_neg] using hx)
    simp [n, hp2]

/-- Two opposite factor pairs are equal if the first normalizer negates
the character; no comparison of their Weyl classes is required. -/
theorem IsOppositeFactorPair.eq_of_flip
    (hT : IsSplitTorus T.toGrp) {a : characterLattice T} (ha : a ≠ 0)
    {x : rationalPoints G} {p q : rationalPoints G × rationalPoints G}
    (hp : IsOppositeFactorPair i a x p) (hq : IsOppositeFactorPair i a x q)
    (hn : weylAction i (⟨p.1 * x * p.2, hp.2.2⟩ : normalizerPoints i) a = -a) :
    p = q := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let n : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  let m : normalizerPoints i := ⟨q.1 * x * q.2, hq.2.2⟩
  let v := q.1 * p.1⁻¹
  let w := p.2⁻¹ * q.2
  have hv : v ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) :=
    ((subgroup i (-a)).carrier _).mul_mem hq.1
      (((subgroup i (-a)).carrier _).inv_mem hp.1)
  have hw : w ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)) :=
    ((subgroup i (-a)).carrier _).mul_mem
      (((subgroup i (-a)).carrier _).inv_mem hp.2.1) hq.2.1
  have hna : weylAction i n⁻¹ (-a) = a := by
    rw [← hn, map_inv]
    exact (weylAction i n).symm_apply_apply a
  have hc := normalizer_conj_mem i (-a) n⁻¹ hv
  simp only [G.constantPoint_self, Subgroup.coe_inv, inv_inv, hna] at hc
  have hz1 := normalizer_eq_one_of_mul_opposite i hT ha (n⁻¹ * m) hc hw
    (by simp [n, m, v, w, mul_assoc])
  have hrel : n.val⁻¹ * v * n.val * w = 1 := by
    have hz := congrArg Subtype.val hz1
    simpa [n, m, v, w, mul_assoc] using hz
  have hc1 : n.val⁻¹ * v * n.val = 1 :=
    eq_one_of_mem_subgroup_of_mem_opposite i hT ha hc
      (by
        rw [mul_eq_one_iff_eq_inv.mp hrel]
        exact Subgroup.inv_mem _ hw)
  have hv1 : v = 1 := by
    have h := congrArg (fun t => n.val * t * n.val⁻¹) hc1
    simpa [mul_assoc] using h
  have hpq1 : p.1 = q.1 := by
    have h := congrArg (fun t => t * p.1) hv1
    simpa [v, mul_assoc] using h.symm
  have hw1 : w = 1 := by simpa only [hc1, one_mul] using hrel
  have hpq2 : p.2 = q.2 := by
    have h := congrArg (fun t => p.2 * t) hw1
    simpa [w, mul_assoc] using h.symm
  exact Prod.ext hpq1 hpq2

end Langlands.GroupScheme.RelativeRoot
