# Universal property of the relative differential sheaf

The theorem `Langlands.Scheme.relativeDifferentialsUniversal` proves
`RelativeDifferentialsUniversalStatement f` for every scheme morphism
`f : X ⟶ S` over arbitrary universe `u`.

`relativeDifferentialsHomEquiv f M` is constructed by applying the
sheafification transfer to the concrete presheaf derivation
`Langlands.PresheafDifferentials.derivation f.c` and its proved
`derivationUniversal f.c`. No universal property is supplied as an unproved input.
The transfer composes the module-sheafification adjunction with the
factorization and uniqueness equivalence for the presheaf derivation.
Its forward map is postcomposition of `relativeDifferentialsDerivation f`.
The required bijectivity follows from the inverse laws of this equivalence.

`relativeDifferentialsHomEquiv_naturality` states compatibility with
postcomposition by any morphism of module sheaves, and
`relativeDifferentialsCorepresentable` packages this naturality into
Mathlib's `CorepresentableBy` structure for `relativeDerivationFunctor f`.
`relativeDifferentialsDesc` is the inverse equivalence, with factorization
lemma `relativeDifferentialsDesc_fac`. Equality of morphisms out of the
differential sheaf follows from equality after postcomposition of the
universal derivation (`relativeDifferentials_hom_ext`).
`relativeDifferentialsDesc_postcomp` follows from this uniqueness and
associativity of postcomposition.

The proof implements the universal property in Stacks Project
Lemma 29.33.2 (tag 01UM), using the presheaf construction and sheafification
route of Section 17.28, Lemmas 17.28.2 and 17.28.4 and Definition 17.28.10.
Registered source `stacks-relative-differentials-internal-hom-2026-10-21`,
content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
files `01UM.html` and `08RL.html`.
