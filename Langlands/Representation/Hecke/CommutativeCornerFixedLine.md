# Fixed lines over commutative compact-open Hecke corners

This module derives a one-dimensional fixed space from commutativity of the
compact-open Hecke corner, for an irreducible smooth complex representation whose
fixed space is nonzero and finite-dimensional. It is a helper for the spherical
fixed-line proof in `Langlands.Representation.Unramified.SphericalFixedLineProof`.

Provenance: the fixed-line fact is a source fact. Borel (1979), *Automorphic
L-functions*, §7.2 (printed page 39, PDF page 48), states that the fixed space of a
hyperspecial maximal compact subgroup in an irreducible admissible representation of
class 1 is one-dimensional. Gross (1998), *On the Satake isomorphism*, §6 (PDF
page 11), states that it has dimension at most one for irreducible smooth
representations. The simplicity input is Bernstein–Zelevinsky (1976), 2.10, already
published in the Library as `Langlands.CompactCoefficientClass.isSimpleModule_fixedVectors`.
The linear-algebra lemma and this general corner formulation are internal
derivations.

## A transitive commuting family on a finite-dimensional space

`Langlands.Hecke.finrank_eq_one_of_commute_of_transitive` concerns a nonzero
finite-dimensional complex vector space `W` and a set `S` of pairwise commuting
endomorphisms. It assumes `S` is transitive: for every nonzero `w` and every `v`,
some `T ∈ S` has `T w = v`. Then `finrank ℂ W = 1`.

Proof.

1. Each `T ∈ S` is a scalar. Because `ℂ` is algebraically closed and `W` is
   finite-dimensional and nontrivial, `Module.End.exists_eigenvalue` gives an
   eigenvalue `c` with eigenvector `u ≠ 0`. For any `v`, transitivity gives
   `T' ∈ S` with `T' u = v`. Commutativity then yields
   `T v = T (T' u) = T' (T u) = T' (c • u) = c • v`.
2. Fix a nonzero `w`. Every `v` is `T w` for some `T ∈ S`, and `T w` is a scalar
   multiple of `w` by step 1. `finrank_eq_one_iff_of_nonzero'` concludes.

## Application to the corner action

`Langlands.Hecke.finrank_fixedVectors_eq_one_of_corner_comm` has the following
setting:

- `G` is a topological group with Borel σ-algebra and left Haar measure `μ`;
- `N` is an open subgroup with compact underlying set;
- `ρ` is a smooth complex representation of `G` on an arbitrary, possibly
  infinite-dimensional, space `V`.

It assumes:

- all elements of the corner `HeckeAlgebra.Corner μ N hN` commute;
- `ρ` is irreducible;
- the `N`-fixed space is a finite `ℂ`-module;
- the `N`-fixed space is nonzero.

Then the `N`-fixed space has `finrank` one.

Proof. `isSimpleModule_fixedVectors` makes the fixed space a simple module over the
corner, through the published `cornerModule` structure given by `cornerAction`.
`isSimpleModule_iff_toSpanSingleton_surjective` turns simplicity into transitivity:
any nonzero fixed vector is sent to any fixed vector by some corner element. Apply
the previous lemma with `S` the range of the algebra homomorphism `cornerAction`.
The range is pairwise commuting because `cornerAction` is multiplicative and the
corner is commutative by hypothesis.
