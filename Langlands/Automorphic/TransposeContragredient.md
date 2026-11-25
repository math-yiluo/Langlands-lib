# The full-operator transpose contragredient pairing condition

This is internal infrastructure for the proof of
`CuspidalTransposeInverseContragredientStatement`. It reformulates the
contragredient bridge using the Library's actual operators and its
definition of a contragredient functional. It does not prove Gelfand--Kazhdan or
assert existence of a transpose-twisted realization.

Let `S` and `T` be actual operator realizations over an arbitrary-universe number
field, at any natural matrix size. `S.IsTransposeIntertwining T e` says that a
complex-linear equivalence `e : S.Space ≃ₗ[ℂ] T.Space` intertwines the operators of
`T` with the following operators on `S`:

- finite adelic translation by the transpose inverse of the argument;
- the action of `compactTranspose k` for the actual standard infinite compact;
- the real Lie action of `realLieIota X`, namely negative ordinary transpose.

The finite group automorphism, compact automorphism, and Lie automorphism are
the concrete Library constructions. The Lie condition uses the real Lie action
through the genuine complexified enveloping algebra. It does not replace the
archimedean differential condition by finite-place information.

`S.IsTransposeInvariantPairing B` says that a complex-bilinear form on
`S.Space × S.Space` is invariant with the second variable acted on by this
transpose twist. Its Lie identity is
`B (D_X y) x + B y (D_{-Xᵗ} x) = 0`.
`S.IsTransposeContragredientPairing B` additionally requires that its partial map
`x ↦ B (·) x` have values in, and be a bijection onto, the algebraic functionals
that are smooth for the finite adelic group and finite for the standard infinite
compact. Injectivity and surjectivity are explicit; nondegeneracy alone is not
used as a substitute for this bijection.
`S.HasTransposeContragredientPairing` asserts existence of such a form.

For a supplied `e` satisfying `IsTransposeIntertwining`, the theorem
`IsTransposeIntertwining.isContragredientOf` transports such a form to
`B' y x = B y (e.symm x)` on `S.Space × T.Space`. The covariance equations give
all three invariance identities. Precomposing the partial map with a bijection
preserves its image, injectivity, and surjectivity.
The converse theorem `hasTransposeContragredientPairing` pulls back an actual
contragredient pairing by `e`, giving `B y x = B' y (e x)`.
The resulting `isContragredientOf_iff` identifies the two conditions exactly.

All these definitions and transports follow directly from the existing
`IsContragredientPairing` definition and linear equivalence identities; this is
their internal provenance. For the cuspidal realizations the pairing-existence
condition is stated as `CuspidalTransposePairingStatement`
(`Global/RankinSelberg/CuspidalTransposeInverseContragredientReduction`); no
theorem of the Library proves it. Neither the equivalence theorem nor
transpose-covariance alone proves `CuspidalTransposeInverseContragredientStatement`;
the statement is proved as `cuspidalTransposeInverseContragredient` in
`Global/RankinSelberg/CuspidalTransposeInverseContragredientProof`.
