# Reduction of the split semisimplicity criterion to its root form

Worker 1391. This module is a derived, conditional step toward the published
`SplitSemisimpleRootDatumStatement` (module
`Langlands.GroupScheme.Reductive.SplitClassificationStatement`). That
statement has two conjuncts: a root finite-index form and a coroot
finite-index form. This module proves that the coroot form follows from the
root form. It does not prove the root form, which is Milne Proposition 21.48
itself, and so it does not prove `SplitSemisimpleRootDatumStatement`.

## The lattice lemma

`RootPairing.finite_quotient_rootSpan_iff_corootSpan` is pure linear algebra
over `ℤ`. Let `P : RootDatum ι X Y` be a Mathlib root datum, with `ι` finite
and `X` finitely generated. Then `X ⧸ P.rootSpan ℤ` is finite exactly when
`Y ⧸ P.corootSpan ℤ` is finite.

The Lean proof:

1. The pairing of `P` is perfect, so `X` is reflexive
   (`Module.IsReflexive.of_isPerfPair`), hence torsion-free. A finitely
   generated torsion-free `ℤ`-module is free
   (`Module.free_of_finite_type_torsion_free'`).
2. The flipped perfect pairing gives a linear equivalence `Y ≃ Dual ℤ X`, so
   `Y` is also finitely generated and free.
3. For a submodule `N` of a finite free `ℤ`-module `M`, `M ⧸ N` is finite
   exactly when `finrank N = finrank M` (`Submodule.finiteQuotient_iff`).
   This turns both sides into rank equations.
4. The coroot span and the root span have equal rank
   (`RootPairing.finrank_corootSpan_eq'`; Milne Lemma C.41). The Mathlib
   lemma needs the root pairing to be anisotropic. That holds for every root
   pairing over the ordered ring `ℤ`
   (`RootPairing.instIsAnisotropicOfLinearOrderedCommRing`).
5. `X` and `Y` have equal rank, because they are perfectly paired
   (`Module.finrank_of_isPerfPair`).

After these rewrites the two rank equations are the same.

## The root-form statement

`SplitSemisimpleRootSpanStatement.{u}` has exactly the quantifiers and
hypotheses of `SplitSemisimpleRootDatumStatement.{u}`: a field `k : Type u`, a
connected reductive group `G` over `Spec k`, a split torus `T` with a maximal
torus `i : T ⟶ G`, and a root datum
`P : RootDatum J (characterLattice T) (cocharacterLattice T)` with
`IsRootDatumOf i P`. Its conclusion is only the first conjunct:

```text
IsSemisimple G ↔ Finite (characterLattice T ⧸ P.rootSpan ℤ)
```

This is Milne Proposition 21.48 together with Definition C.34 ("a root datum
(X, Φ, Φ^∨) is semisimple if ZΦ is of finite index in X"). The definition is
an internal packaging step. It adds no hypothesis that the published statement
lacks.

## Finitely many roots

The published statement does not assume that `J` is finite.
`IsRootDatumOf.finite_index` derives it. The second clause of
`IsRootDatumOf i P` says that `Set.range P.root` is `roots i`. Each root has a
nonzero weight space, so `roots i` lies in the weight support of the Lie
algebra. That support is finite for a split torus in a group of finite type
(`IsSplitTorus.finite_weightSupport`). `P.root` is injective, so `J` is finite
(`Set.finite_range_iff`). The lemma assumes `IsAffineHom` and
`LocallyOfFiniteType` for `G.X.hom`. In the theorem below these come from
`hG.isAffineHom` and `hG.smooth`.

## The reduction theorem

`splitSemisimpleRootDatum_of_rootSpan` states that
`SplitSemisimpleRootSpanStatement.{u}` implies
`SplitSemisimpleRootDatumStatement.{u}`. The proof proceeds as follows:

1. Apply the root-form statement to the given data. This gives the first
   conjunct.
2. For the second conjunct, compose that equivalence with the lattice lemma.
3. The lattice lemma needs `Finite J`, which comes from
   `IsRootDatumOf.finite_index`. It also needs `Module.Finite ℤ` for the
   character lattice of the split torus `T`, which comes from
   `IsSplitTorus.finite_characterLattice`.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The universe `u` is arbitrary. Nothing in it restricts the
field: imperfect fields and positive characteristic are allowed. All group
schemes, centres and kernels keep the Library's actual-scheme conventions,
because the conclusion is the published proposition itself.

## Provenance

Milne, *Algebraic Groups* (2017), source `milne-2017-algebraic-groups`,
SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`:

- Proposition 21.48 (printed p.439, PDF p.455): "A split reductive group is
  semisimple if and only if its root datum is semisimple." This is the root
  form, recalled there through C.34.
- The proof of Proposition 21.49(a) on the same page uses the dual form: "By
  duality the α^∨ generate a subgroup of X_*(T) of finite index".
- Lemma C.41 (printed p.617, PDF p.633): "The map p: X → X^∨ defines an
  isomorphism 1⊗p: V → V^∨. In particular, dim V = dim V^∨." Its proof shows
  that the rational spans of the roots and of the coroots have equal
  dimension.

The Lean proof follows that duality step. It uses the Mathlib rank equality
for root pairings over a domain in place of Milne's map `p`. Both arguments
come down to the same rank comparison. The errata snapshot of 2026-11-02
(`milne-2017-algebraic-groups-errata-2026-11-02`) has no entry for
Proposition 21.48, Proposition 21.49 or Lemma C.41.
