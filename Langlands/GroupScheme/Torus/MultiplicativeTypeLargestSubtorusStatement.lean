import Langlands.GroupScheme.Torus.MultiplicativeType
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Statement: the largest subtorus of a group of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The largest subtorus of a group of multiplicative type** (Milne, *Algebraic Groups*
(2017), Notation 12.29). Over a field `K`, a homomorphism `t : T ⟶ G` is a *largest subtorus*
of `G` when `T` is a torus, `t` is a closed subgroup, and every closed subgroup
`t' : T' ⟶ G` with `T'` a torus factors through `t`. Let `H` be a group of multiplicative
type over a field `k`.
1. `H` has a largest subtorus.
2. A subtorus `t : T ⟶ H` such that the quotient `H/T` (an fppf quotient by the image of `t`)
   is finite is a largest subtorus of `H`.
3. If `t` is a largest subtorus of `H`, then for every field extension `K` of `k` its base
   change `t_K` is a largest subtorus of `H_K`.
4. If `H` is a closed normal subgroup of a smooth algebraic group `G` and `t` is a largest
   subtorus of `H`, then the image of `T` in `G` is normal in `G`. -/
def MultiplicativeTypeLargestSubtorusStatement : Prop :=
  let IsLargestSubtorus :
      ∀ {K : Type u} [Field K] {G T : GroupScheme (Spec (CommRingCat.of K))}, (T ⟶ G) → Prop :=
    fun {K} _ {G T} t => IsTorus T ∧ IsClosedSubgroup t ∧
      ∀ (T' : GroupScheme (Spec (CommRingCat.of K))) (t' : T' ⟶ G),
        IsTorus T' → IsClosedSubgroup t' → ∃ f : T' ⟶ T, f ≫ t = t'
  ∀ (k : Type u) [Field k] (H : GroupScheme (Spec (CommRingCat.of k))),
    IsMultiplicativeType H →
      (∃ (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H), IsLargestSubtorus t) ∧
      (∀ (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H),
        IsTorus T → IsClosedSubgroup t →
        (∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : H ⟶ Q),
          IsFinite Q.X.hom ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range t) q) →
        IsLargestSubtorus t) ∧
      (∀ (K : Type u) [Field K] [Algebra k K]
        (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H),
        IsLargestSubtorus t →
        IsLargestSubtorus
          ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map t)) ∧
      (∀ (G : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        Smooth G.X.hom → QuasiCompact G.X.hom →
        IsClosedSubgroup h → (SubgroupFunctor.range h).IsNormal →
        ∀ (T : GroupScheme (Spec (CommRingCat.of k))) (t : T ⟶ H),
          IsLargestSubtorus t → (SubgroupFunctor.range (t ≫ h)).IsNormal)

end Langlands.GroupScheme
