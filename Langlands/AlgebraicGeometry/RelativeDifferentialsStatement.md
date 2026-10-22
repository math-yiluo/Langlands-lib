# Universality of the relative differential sheaf

`Langlands.Scheme.RelativeDifferentialsUniversalStatement f` says that for
every actual module sheaf `M` on `X`, postcomposition of the distinguished
derivation `relativeDifferentialsDerivation f` is a bijection from
`relativeDifferentials f ⟶ M` to `RelativeDerivation f M`.

Both the source sheaf and its distinguished derivation are the explicit
constructions of `RelativeDifferentials.lean`. There is no assumption of
universality or existence in this proposition. Bijectivity states both
factorization of every relative derivation and uniqueness of the factor.
The corresponding naturality is implemented with the hom equivalence in
the proof module; it is the composition law for postcomposition of derivations.

This is Stacks Project Lemma 29.33.2 (tag 01UM), with the chosen sheaf and
derivation defined as in Section 17.28, Lemmas 17.28.2 and 17.28.4 and
Definition 17.28.10. Registered original
`stacks-relative-differentials-internal-hom-2026-10-21`,
content SHA256
`9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`,
files `01UM.html` and `08RL.html`.
