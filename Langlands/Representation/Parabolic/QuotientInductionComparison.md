# Actual quotient-Levi induction and composite comparison

This internal adapter constructs normalized smooth induction from the actual
upper block parabolic quotient and compares it with the existing product-Levi
induction. Together with `QuotientJacquetComparison`, it reexpresses each
induction-after-Jacquet composite, and hence the unchanged actual GL alternating
operator, through quotient-Levi functors. It defines no new Aubert operator or
general reductive datum.

## Covariance on actual parabolic elements

For an existing `BlockShape B` over a commutative topological ring `F`,
`quotientToProductLevi` is smooth pullback along the inverse of the actual
continuous quotient-to-product Levi equivalence. It preserves the original
vector space and linear maps. For a supplied smooth complex character `χ` of
the product Levi and an actual quotient-Levi representation `ρ`,
`quotientInducingRepresentation` inflates `ρ` along the genuine quotient
projection `QuotientGroup.mk'` and twists by the existing inflated `χ`.
Its action on `g` in the actual parabolic and a vector `v` is

`χ(leviProjection g) • ρ([g]) v`.

`quotientInducingRepresentation_eq` is equality of parabolic representations on
the same vector space. It identifies this direct quotient-inflation action with
the existing `inducingRepresentation` of the product-Levi action obtained by
inverse group transport. The proof uses the inverse law for
`parabolicQuotientLevi` applied to `[g]`; it does not identify arbitrary labels.

`normalizedQuotientInductionFunctorOf` is inverse smooth Levi transport followed
by the existing `normalizedInductionFunctorOf`. The direct quotient covariance
model is compared to that functor's actual object by `quotientInducingEquiv` and
`quotientInducedEquiv`. The former is the identity on original vectors, and the
latter induces it by postcomposition. `quotientInducedEquiv_eval` says that every
underlying induced function is retained pointwise. The covariance is therefore
the actual displayed quotient formula, and the group acts by the existing right
translation on full smooth covariant functions. On morphisms,
`normalizedQuotientInductionFunctorOf_map_eval` states that the original
intertwiner postcomposes every induced function. No finite-length restriction
is imposed on these smooth-functor constructions.

The generic construction permits arbitrary commutative topological `F`, complex
representation coefficients, independent field and carrier universes, and all
natural ranks. The induced carrier universe is `max uF uV`, as for the existing
smooth function construction. No Hausdorff or local-compactness assumption is
added here.

## Existing p-adic normalization and exact K0

For a prime `p`, every `F : PadicField.{uF} p` and every supplied
`T : F.TopologicalData`, `Parabolic.normalizedQuotientInductionFunctor` uses
`T.leviHalfCharacter B`. This is the existing positive square root of the full
explicit block character; the quotient Jacquet map retains its inverse half.
Identifying that explicit character with a Haar conjugation modulus remains a
separate theorem obligation.

At the existing saturated carrier universe `Type (max uF uV)`, finite length
follows from generic group-equivalence pullback and the unchanged normalized
induction finite-length theorem. Short-exact preservation follows from the
unchanged maps in group pullback and the existing normalized induction exactness
theorem. The generic exact-K0 functor construction gives
`normalizedQuotientInductionK0`, a map of the full existing exact groups of actual
finite-length smooth representations, with all actual short-exact relations.
`normalizedQuotientInductionK0_hasFiniteLength` supplies the actual output witness.
`normalizedQuotientInductionK0_finiteLengthClass` sends every actual input class
to the class of its actual quotient-Levi induction for any output-length proof.

`normalizedQuotientInductionK0_eq` is equality of whole integer-linear maps:
the quotient induction map is the unchanged `normalizedInductionK0` after the
inverse of `quotientLeviK0Equiv`. The proof is generic functor-map composition.
Combining with `normalizedQuotientJacquetK0_eq` and cancelling that actual
linear equivalence proves `normalizedQuotientInductionJacquetK0_eq` on every
exact class.

Finally, `Aubert.alternatingOperator_eq_quotientLevi_sum` reexpresses the existing
operator as the signed sum of these actual quotient-Levi composites. Its sign
remains `(-1)^(n-B.length)`, and the finite sum includes all positive ordered
block shapes, including the empty shape at rank zero. This is a theorem about
the existing integer-linear operator. It is not yet a comparison with a
specialization of the pending shared general operator.

## Internal provenance and boundaries

The construction reuses the actual quotient and continuous Levi equivalence,
`Induction.Parabolic`, `Induction.Equivalences`, the generic smooth pullback and
exact-K0 APIs, and the existing named p-adic induction and Jacquet maps.
The internal group inverse law, induced-equivalence construction, functor
composition law and cancellation of a linear equivalence account for all new
comparison proofs. No extra representation-theoretic hypothesis is introduced
in the p-adic specialization.

The generic change-of-group length proof invokes
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` and
`length_comp_surjective` in `Classification.FiniteLengthProof`; their proof is
algebraic module-length invariance through the actual subrepresentation order
isomorphism. The reused p-adic normalized induction/Jacquet finite-length proofs
have larger transitive classification dependencies, retained unchanged. This
module makes no classification-independence or external Chapter V closure claim.
The host dependency note lists the actual declaration-body closure separately.

The shared general reductive datum, scheme-point/matrix topology and subgroup
bridges, shared general normalized functors, Haar modulus identification, and
comparison of their general operator specialization remain separate obligations.
The current `PadicField` scope is explicit; arbitrary local-field comparison is
not supplied here.
