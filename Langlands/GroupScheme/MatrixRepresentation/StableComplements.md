# Stable-subspace lattices and semisimple representations

This derived infrastructure concerns a matrix representation of any group scheme
over a field, with an arbitrary finite coordinate index. Stability always means
`MatrixRepresentation.IsStableSubspace`, quantified over every commutative test
algebra and every ground-field linear functional. No smoothness, reducedness,
finite-type or characteristic hypothesis is imposed on the group.

`affineCoefficientEndomorphism` applies a linear functional to the entries of an
affine-test matrix and uses the resulting ground-field matrix as a linear
endomorphism. Its application theorem identifies this with applying that
functional to the translate of a vector. Consequently arbitrary sums and
intersections of stable subspaces are stable.

`stableSubspaceLattice` is the resulting complete sublattice of the submodule
lattice. It is modular because the submodule lattice is modular. Finite dimension
makes its ascending chains stationary; Mathlib then supplies compact generation.
The atoms are exactly the nonzero stable subspaces with no proper nonzero stable
subspace, and coercion preserves their supremum.

`IsSemisimple` abbreviates exactly the sum-of-simple-stable-subspaces condition
used in `NagataLinearlyReductiveStatement`. It holds also for the zero
representation. `isSemisimple_iff_exists_stable_complement` proves that this
condition is equivalent to every stable subspace having a stable vector-space
complement. The proof passes to the stable-subspace lattice and applies Mathlib's
compactly generated modular lattice results: a lattice whose atoms span the top
is complemented, and a complemented lattice of this kind is atomistic.

## Provenance

The representation-theoretic content is Milne, *Algebraic Groups* (2022 corrected
reprint), Definition 4.15 and Proposition 4.17, printed p. 90, and the converse
immediately following that proof. The source is registered as
`milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The official errata snapshot, registered as
`milne-2022-algebraic-groups-errata-2026-11-04`, has no correction for these
statements; its nearby p. 89 correction concerns the matrix indices in the proof
of 4.14. The source passages and the full errata snapshot were read locally.

The complete-sublattice and coefficient-endomorphism constructions are internal
derived infrastructure. They translate Milne's subrepresentations into the
Library's existing all-test coefficient formulation. The implemented proof uses
Mathlib's abstract lattice theorem rather than reproducing Milne's direct
maximal-independent-family proof. This file proves no structural assertion about
identity components and does not prove Nagata's theorem.
