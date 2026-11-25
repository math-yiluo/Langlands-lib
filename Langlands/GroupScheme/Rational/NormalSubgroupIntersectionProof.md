# Normal subgroups meet maximal tori, parabolic and Borel subgroups well: proof

`Langlands.GroupScheme.normalSubgroupIntersection : NormalSubgroupIntersectionStatement.{u}`
proves the published statement
[`Rational.NormalSubgroupIntersectionStatement`](NormalSubgroupIntersectionStatement.md),
Conrad, *Reductive group schemes*, Exercise 5.5.1, for every universe `u` and every field. The
module adds no statements, definitions or axioms. It assembles three results:

- Clause (i), maximal tori. `NormalSubgroupIntersection.torusIntersection` from
  [`Rational.NormalSubgroupTorusIntersection`](NormalSubgroupTorusIntersection.md).
  For a maximal torus `t : T ⟶ G` and a smooth connected closed subgroup
  `n : N ⟶ G` whose range `t` normalizes, it gives a maximal torus `c : C ⟶ N` with
  `range (c ≫ n) = range n ⊓ range t`. This is exactly clause (i) for the given data. The
  proof passes the clause-(i) hypotheses of the statement through unchanged.
- Clauses (ii) and (iii), parabolic and geometric Borel subgroups.
  `NormalSubgroupParabolicIntersection.normalSubgroupIntersection_of_torusClause_of_borelSelfNormalizer`
  from [`Rational.NormalSubgroupParabolicIntersection`](NormalSubgroupParabolicIntersection.md).
  Given `BorelContainingSubgroupSelfNormalizerStatement` and a proof of clause (i),
  it returns the full statement. Over an algebraic closure, `Z = (H ∩ P)_red` contains a Borel
  subgroup of `H` and is normalized by every point of `H ∩ P`. Self-normalization of `Z` in `H`
  then gives `H ∩ P = Z`, which is smooth and connected. Smoothness, connectedness and the
  geometric Borel property then descend to the base field.
- The normalizer theorem. `borelContainingSubgroupSelfNormalizer :
  BorelContainingSubgroupSelfNormalizerStatement.{u}` from
  [`Absolute.BorelContainingSubgroupSelfNormalizerProof`](../Absolute/BorelContainingSubgroupSelfNormalizerProof.md)
  (Milne, *Algebraic Groups*, Theorem 17.48 and Corollary 17.49).

The theorem is the single term

```lean
normalSubgroupIntersection_of_torusClause_of_borelSelfNormalizer
  borelContainingSubgroupSelfNormalizer
  (fun _ _ G _ _ _ T t ht N n hn hNs hNc hnorm =>
    NormalSubgroupIntersection.torusIntersection G T t ht N n hn hNs hNc hnorm)
```

The two supporting modules document their proofs and their relation to Conrad's hints.
