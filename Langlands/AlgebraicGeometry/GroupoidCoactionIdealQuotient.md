# Coactions modulo invariant ideals

This internal module supplies the ideal-reduction step in the planned
Noetherian faithfulness argument. Let `B` and `C` be commutative rings in
an arbitrary universe `u`, with source algebra map `s : B →+* C`,
target map `t : B →+* C`, and a published `GroupoidCoaction t M` on a
`B`-module `M : Type v`.

First, a coaction descends to `M/P` if its composite with
`C ⊗[B] M → C ⊗[B] (M/P)` vanishes on `P`. The semilinear map
`quotientSemilinearMap` is the quotient lift of that composite.
`quotient` uses the previously implemented surjective transport to prove
the full published coaction identities. Its quotient map is equivariant.

For an ideal `I : Ideal B`, assume
`I.map t ≤ I.map s`. The source extension `I.map s` annihilates
`C ⊗[B] (M/IM)`: for a tensor `c ⊗ m`, source scalars move across the
tensor to the second factor, where `I` acts by zero. The ideal map
universal property extends this to every source-extended scalar.
Semilinearity then shows that the coaction of each `a • m` with `a ∈ I`
vanishes after the tensor quotient map, and induction on the ideal
multiple proves the vanishing on all of `IM`.
`idealQuotient` is the resulting actual coaction on
`M ⧸ (I • ⊤ : Submodule B M)`, and `idealQuotient_mkQ_isHom` proves
equivariance of its canonical quotient map.

Assuming `RingEtaleEquivalenceRelation t` and acyclicity of every
coaction on a module in `Type v`, the previously implemented invariant
surjectivity theorem applies to this quotient map.
`idealQuotient_invariantsMap_surjective` states that every quotient
invariant lifts. `exists_nonzero_invariant_of_idealQuotient` observes
that a lift of a nonzero element is itself nonzero.

Finally, for a finite `B`-module, Mathlib's support identity
`Supp(M/IM) = Supp(M) ∩ V(I)` proves that `M/IM` is nonzero whenever
some `p ∈ Supp(M)` contains `I`. This last assertion does not require
a coaction.

The module is derived from the unchanged published coaction definitions,
the internal transport and invariant-surjectivity helpers, and Mathlib's
ideal, tensor, quotient, and support APIs. It translates no new
literature theorem. It does not construct a finite orbit, prove that its
radical ideal has equal source and target extensions, construct a
restricted relation over `B/I`, or supply a nonzero invariant on the
quotient by descent. Those are explicit remaining inputs to the full
Noetherian faithfulness proof.
