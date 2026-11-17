# Affine fppf quotients by diagonalizable normal subgroups

This module completes the direct affine model used toward SGA 3, Exposé VIII,
Theorem 5.1 and the quotient construction cited in Conrad, *Reductive group
schemes* (2014), proof of Lemma 3.3.2, p.98. Its provenance is derived: it combines
the actual strong-grading invariant spectrum and the previously implemented
normal fpqc quotient group construction. It works in every universe, over every
commutative ring, without smoothness or reducedness of the subgroup.

For a finitely generated abelian group `M`,
`Diagonalizable.locallyOfFinitePresentation R M` proves that `D_R(M)` is locally
finitely presented over `Spec R`. The proof first uses finite type of the actual
group algebra over the universe-lifted integers. The integer spectrum is
Noetherian, so finite type implies local finite presentation there. Stability
under base change and the actual diagonalizable base-change isomorphism then
transport the property to the original ring `R`. This argument allows torsion
in `M` and does not assume `R` Noetherian.

`quotientScheme_isAffine` records that the spectrum of the actual invariant ring
is affine. For a closed inclusion `i : D_R(M) → G` into an affine group scheme,
`translationProjection_locallyOfFinitePresentation` proves local finite
presentation of the actual invariant projection when `M` is finitely generated.
The translation relation is a pullback of this projection along itself. Its
first map to `G` is the product projection `D_R(M) × G → G`, which is locally
finitely presented by base change. The invariant projection is flat and
surjective by strong grading and quasi-compact since both schemes are affine.
Fpqc descent of local finite presentation therefore applies to that pullback.

For a closed diagonalizable inclusion with normal range, `quotientGroup i hi hn`
is the actual invariant spectrum equipped with the group structure supplied by
`NormalQuotient.groupScheme`. `quotientHom` is the original projection equipped
with its group-homomorphism structure. The all-test fiber criterion from
`TranslationQuotient` is the input to the descended multiplication and inverse.
`quotientGroup_isAffineHom` proves that this group scheme is affine over the
original base. These constructions do not need finite generation of `M`.

Finally, for finitely generated `M`, `quotientHom_isFppfQuotient` proves the exact
Library predicate: flatness, surjectivity, local finite presentation, and
agreement between the range of the actual kernel inclusion and the range of
`i` on every relative scheme test. No quotient scheme or action is assumed as
input. The global case over arbitrary bases is handled by the separate
multiplicative-type reduction and gluing construction.
