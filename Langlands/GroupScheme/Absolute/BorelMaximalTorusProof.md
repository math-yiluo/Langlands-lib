# Every Borel subgroup contains a maximal torus of the ambient group

Worker 1418.

`Langlands.GroupScheme.borelMaximalTorus.{u}` proves exactly the unchanged
`BorelMaximalTorusStatement.{u}`. Let `k : Type u` be an algebraically closed
field of any characteristic. Let `G` be a group scheme over `Spec k` with
smooth affine structural map and connected underlying space. Then every actual
Borel subgroup `i : B ⟶ G` belongs to a Borel pair `IsBorelPair i j` for some
commutative group scheme `T` and morphism `j : T.toGrp ⟶ G`. By the published
definition, this means that `i` is a Borel subgroup, `j` is a maximal torus of
`G`, and `j = f ≫ i` for some `f : T.toGrp ⟶ B`. The proof adds no
reductivity, splitness or characteristic hypothesis.

## Implemented proof

The theorem is the published conditional result
`borelMaximalTorusStatement_of_borelConjugacy`, from
`Langlands.GroupScheme.Absolute.BorelMaximalTorusReduction`. It is applied to
the published proof `borelConjugacy : BorelConjugacyStatement.{u}`, from
`Langlands.GroupScheme.Absolute.BorelConjugacyProof`.

For a fixed `G`, the conditional result proceeds as follows.

1. `exists_isBorelPair G` produces one Borel pair `(i₀ : B₀ ⟶ G, j : T ⟶ G)`.
   It first chooses a maximal torus `j` of `G` by `exists_isMaximalTorus` from
   `Torus.HeightExistence`, which takes a closed torus whose coordinate kernel
   has minimal height. A closed torus is smooth, connected and commutative, hence
   solvable, so it is an admissible subgroup
   (`BorelExistence.isAdmissible_of_isTorus`). The published
   `BorelExistence.exists_isBorelSubgroup_containing` gives a Borel subgroup
   `i₀` through which `j` factors (`maximalToriLieInBorels`).
2. The conjugacy component of `BorelConjugacyStatement` applied to `i₀` and the
   given Borel subgroup `i` gives a rational point `g` of `G` and an
   isomorphism `φ : B₀ ≅ B` with `i₀ ≫ (G.innerIso g).hom = φ.hom ≫ i`.
3. `IsBorelPair.of_subgroupConjugate` moves the pair along this conjugation.
   The composite `j ≫ (G.innerIso g).hom` is again a maximal torus of `G`, by
   `IsMaximalTorus.comp_iso`. It factors through `i` via the factor of `j`
   through `i₀` followed by `φ`, so `(i, j ≫ (G.innerIso g).hom)` is a Borel
   pair.

The witnesses for the existential conclusion are `T` and
`j ≫ (G.innerIso g).hom`.

## Sources and provenance

The original source is J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`. The relevant passage is the paragraph after
Definition 17.12, on printed p.355 (one-based PDF p.371). There Milne argues
that every maximal torus lies in a Borel subgroup, and that Borel subgroups are
conjugate (Theorem 17.9), so every Borel subgroup contains a maximal torus. The
Lean proof follows this route. Its maximal torus existence step uses
minimal coordinate-kernel height in place of a dimension argument.

The reduction module and `Torus.HeightExistence` were written by Worker 1418.
`BorelConjugacyProof` is the published proof by Worker 1293, with Worker 135.
`BorelContaining` was published by Worker 1358. This module only composes these
published results. It imports them by Lean name and changes no statement pair.
