import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RelativeReflectionProperties
import Langlands.GroupScheme.Rational.UnipotentQuotientNormalizerLift

/-! # A fixed reflection normalizer and its translated root cell -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section Cell

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]

/-- Every nonidentity root point lies in the opposite-root cell of any fixed
normalizer representing the reflection in that root. -/
theorem rootPoint_translatedCell_of_reflection
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (hfac : HasRankOneFactorization i)
    {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (n : normalizerPoints i)
    (hn : IsRelativeReflection i a (QuotientGroup.mk n))
    (x : rationalPoints G)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1) :
    ∃ y ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)),
      ∃ z ∈ centralizerPoints i,
        ∃ w ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)),
          x = y * z * n.val * w := by
  obtain ⟨p, hp, _⟩ := (hfac a ha x hx hx1).1
  let n' : normalizerPoints i := ⟨p.1 * x * p.2, hp.2.2⟩
  have heq : (QuotientGroup.mk n' : relativeWeylGroup i) = QuotientGroup.mk n :=
    hroot.eq_of_isRelativeReflection (hp.isRelativeReflection i hT ha hx hx1) hn
  have hz : n' * n⁻¹ ∈ (centralizerPoints i).subgroupOf (normalizerPoints i) := by
    apply (QuotientGroup.eq_one_iff _).1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, heq, mul_inv_cancel]
  refine ⟨p.1⁻¹, Subgroup.inv_mem _ hp.1, n'.val * n.val⁻¹, hz,
    p.2⁻¹, Subgroup.inv_mem _ hp.2.1, ?_⟩
  dsimp only [n']
  group

/-- Multiplication by the inverse of the same fixed normalizer puts the
root point in the ordinary opposite-centralizer-positive cell. -/
theorem rootPoint_mul_inv_mem_cell_of_reflection
    (hT : IsSplitTorus T.toGrp) (hroot : HasRelativeRootSystem i)
    (hfac : HasRankOneFactorization i)
    {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (n : normalizerPoints i)
    (hn : IsRelativeReflection i a (QuotientGroup.mk n))
    (x : rationalPoints G)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1) :
    ∃ y ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)),
      ∃ z ∈ centralizerPoints i,
        ∃ w ∈ (subgroup i a).carrier (Over.mk (𝟙 _)),
          x * n.val⁻¹ = y * z * w := by
  obtain ⟨y, hy, z, hz, w, hw, he⟩ :=
    rootPoint_translatedCell_of_reflection i hT hroot hfac ha n hn x hx hx1
  have hw' := normalizer_conj_mem i (-a) n hw
  simp only [GroupScheme.constantPoint_self, map_neg,
    hn.weylAction_apply_self i hT n, neg_neg] at hw'
  exact ⟨y, hy, z, hz, n.val * w * n.val⁻¹, hw', by rw [he]; group⟩

end Cell

section Reductive

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    [IsAffineHom G.X.hom] [Mono i.hom.hom.left]

include hG hi in
/-- Choose a rational representative of the reflection in an actual root.
This choice is independent of the root point later put in its cell. -/
theorem exists_reflectionNormalizer
    {a : characterLattice T} (ha : a ∈ relativeRoots i) :
    ∃ n : normalizerPoints i, IsRelativeReflection i a (QuotientGroup.mk n) := by
  obtain ⟨w, hw⟩ := (relativeRootSystem k G hG T i hi).exists_isRelativeReflection ha
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact ⟨n, hw⟩

/-- A fixed actual rational reflection normalizer for an actual relative root. -/
def reflectionNormalizer {a : characterLattice T} (ha : a ∈ relativeRoots i) :
    {n : normalizerPoints i // IsRelativeReflection i a (QuotientGroup.mk n)} :=
  ⟨Classical.choose (exists_reflectionNormalizer hG i hi ha),
    Classical.choose_spec (exists_reflectionNormalizer hG i hi ha)⟩

include hG hi in
/-- The single chosen reflection normalizer works for every nonidentity point
in this actual root group. -/
theorem reflectionNormalizer_translatedCell
    {a : characterLattice T} (ha : a ∈ relativeRoots i)
    (x : rationalPoints G)
    (hx : x ∈ (subgroup i a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1) :
    ∃ y ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)),
      ∃ z ∈ centralizerPoints i,
        ∃ w ∈ (subgroup i (-a)).carrier (Over.mk (𝟙 _)),
          x = y * z * (reflectionNormalizer hG i hi ha).val.val * w :=
  rootPoint_translatedCell_of_reflection i hi.isSplitSubtorus.1
    (relativeRootSystem k G hG T i hi) (rootRankOneFactorization k G hG T i hi)
    ha (reflectionNormalizer hG i hi ha).val (reflectionNormalizer hG i hi ha).property
    x hx hx1

end Reductive

section Lift

variable {k : Type u} [Field k] [PerfectField k]
    {N G Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth N.X.hom] [ConnectedSpace N.X.left]
    (r : N ⟶ G) (hr : IsClosedSubgroup r) (hN : IsUnipotent N)
    (q : G ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range r) q)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp)
    (hQ : IsConnectedReductive Q) (hi : IsMaximalSplitTorus (i ≫ q))
    [IsAffineHom Q.X.hom] [Mono (i ≫ q).hom.hom.left]

/-- Lift the fixed quotient reflection normalizer with its exact quotient
image and its exact torus automorphism. The automorphism negates the root. -/
def reflectionNormalizerLift
    {a : characterLattice T} (ha : a ∈ relativeRoots (i ≫ q)) :
    {m : rationalPoints G × (T ≅ T) //
      rationalPoints.map q m.1 = (reflectionNormalizer hQ (i ≫ q) hi ha).val.val ∧
        IsNormalizingPoint i m.1 m.2 ∧ characterAut m.2 a = -a} := by
  let n := (reflectionNormalizer hQ (i ≫ q) hi ha).val
  let σ := normalizingAut (i ≫ q) n
  let m :=
    UnipotentQuotientNormalizerLift.perfectFieldNormalizerLift
      r hr hN q hq i hT n.val σ (isNormalizingPoint_normalizingAut (i ≫ q) n)
  refine ⟨(m.val, σ), m.property.1, m.property.2, ?_⟩
  exact (reflectionNormalizer hQ (i ≫ q) hi ha).property.weylAction_apply_self
    (i ≫ q) hi.isSplitSubtorus.1 n

include hr hN hq hT hQ hi in
/-- Every nonidentity quotient-root point lies in the cell translated by the
image of this one fixed actual source normalizer. -/
theorem reflectionNormalizerLift_translatedCell
    {a : characterLattice T} (ha : a ∈ relativeRoots (i ≫ q))
    (x : rationalPoints Q)
    (hx : x ∈ (subgroup (i ≫ q) a).carrier (Over.mk (𝟙 _))) (hx1 : x ≠ 1) :
    ∃ y ∈ (subgroup (i ≫ q) (-a)).carrier (Over.mk (𝟙 _)),
      ∃ z ∈ centralizerPoints (i ≫ q),
        ∃ w ∈ (subgroup (i ≫ q) (-a)).carrier (Over.mk (𝟙 _)),
          x = y * z *
            rationalPoints.map q (reflectionNormalizerLift r hr hN q hq i hT hQ hi ha).val.1 *
              w := by
  rw [(reflectionNormalizerLift r hr hN q hq i hT hQ hi ha).property.1]
  exact reflectionNormalizer_translatedCell hQ (i ≫ q) hi ha x hx hx1

end Lift

end Langlands.GroupScheme.RelativeRoot
