# Actual quotient-Levi Jacquet comparison

This internal adapter identifies the actual normalized Jacquet action of an
upper block parabolic quotient with the existing product-Levi Jacquet functor.
It retains the existing radical coinvariant space, descended linear maps and
exact finite-length Grothendieck groups. It introduces no general reductive
structure or general Aubert operator.

## Actual algebraic actions and maps

For an existing `BlockShape B` over any commutative ring `F`, the acting quotient
is literally `B.parabolic F ⧸ B.unipotentRadical F`. The radical is the kernel
of the actual diagonal-block projection. Given a positive unit-valued character
`δ` of `B.Levi F`, `quotientModulus` is its pullback through the existing
`parabolicQuotientLevi` group equivalence.

`normalizedQuotientJacquetOf` applies Mathlib's
`Representation.quotientToCoinvariants` to the restriction of the original
`GL_n` action to the actual parabolic and twists by the inverse positive half
of `quotientModulus δ`. Its carrier is the existing `B.JacquetModule ρ`.
On a quotient group element represented by `g` and a quotient vector represented
by `v`, its action is

`inverseHalfCharacter δ (leviProjection g) • jacquetMk ρ (ρ g v)`.

`normalizedQuotientJacquetOf_eq` is equality of representations on this same
vector space: this quotient action equals the existing `normalizedJacquetOf δ ρ`
pulled back along `parabolicQuotientLevi`. The proof reduces both quotients to
representatives and uses the existing `Parabolic.mk_action_eq_levi` decomposition
identity. Thus the comparison concerns actual actions, not only virtual classes.
`normalizedQuotientJacquetOfMap` retains exactly the existing descended linear
map and sends `[v]` to `[f(v)]` for every original ambient intertwiner.

## Smooth functors and exact K0

For a commutative topological ring and an open-kernel supplied character,
`isSmooth_normalizedQuotientJacquetOf` pulls smoothness back along the already
constructed continuous quotient-to-product Levi equivalence.
`normalizedQuotientJacquetFunctorOf` bundles these actual objects and maps.
`normalizedQuotientJacquetIsoOf` identifies it naturally with the existing
product-Levi Jacquet functor followed by `Parabolic.productToQuotientLevi`.
Every component is the identity linear map of the original coinvariant space;
`normalizedQuotientJacquetIsoOf_hom_apply` records this literally.

The generic finite-length and short-exact preservation lemmas transfer the
corresponding hypotheses on the existing product-Levi functor. Finite length
uses invariance under the surjective change of acting group and the proved
equality of representations, transporting the whole representation-dependent
module predicate. Exactness uses the unchanged linear maps. The resulting
`normalizedQuotientJacquetK0Of` acts on the existing exact K0: actual finite-length
smooth isomorphism classes modulo all actual short-exact relations.
`normalizedQuotientJacquetK0Of_eq` is equality of integer-linear maps on this
whole group. It is `quotientLeviK0Equiv` after the existing product-Levi Jacquet
map, proved using the natural isomorphism and generic functor composition.

These generic declarations do not prove finite length or exactness for an
arbitrary ring and arbitrary character: those two premises remain explicit.
Field and representation-carrier universes are independent, complex coefficients
are fixed, and every natural rank including zero is permitted.

## P-adic specialization and normalization

The declarations in `Langlands.Parabolic` specialize to every
`F : PadicField.{uF} p` with `p` prime and every supplied `T : F.TopologicalData`.
`normalizedQuotientJacquetFunctor` uses the existing full explicit block character
`T.leviModulus B` and its proved open kernel. Its natural comparison with
`T.normalizedJacquetFunctor B` is `normalizedQuotientJacquetIso`. The scalar above
is the inverse of `T.leviHalfModulus B (leviProjection g)`, by the existing
positive-half-character and explicit-block-half formulas. This is the existing
inverse-Jacquet normalization paired with positive-half normalized induction.
No identification of the explicit block character with a Haar conjugation
modulus is added by this adapter.

At the existing saturated carrier universe `Type (max uF uV)`, the published
finite-length and exactness theorems supply the generic premises.
`normalizedQuotientJacquetK0_hasFiniteLength` gives the output length proof;
`normalizedQuotientJacquetK0` is the resulting actual map. The theorem
`normalizedQuotientJacquetK0_eq` identifies it with
`quotientLeviK0Equiv` after the unchanged `Parabolic.normalizedJacquetK0`.
`normalizedQuotientJacquetK0_finiteLengthClass` sends every finite-length
representation class to the class of its actual quotient Jacquet module,
independently of the chosen output-length proof. Rank zero is included throughout.
The existing p-adic scope is retained; arbitrary nonarchimedean-local-field
specialization is a separate comparison obligation.

## Provenance and remaining boundaries

This is an internal construction from the existing actual GL groups,
`Parabolic.LeviBridges`, `Jacquet.Parabolic`, smooth pullback and exact-K0 APIs.
The new quotient action is Mathlib's genuine quotient-to-coinvariant action,
not a representation defined merely to make a comparison tautological.

The generic change-of-group finite-length helper is imported through
`Smooth.FiniteLengthGrothendieckTransport` from
`Classification.FiniteLengthProof`. Its invoked
`FiniteLengthAssembly.finiteLength_comp_surjective_iff` follows from invariance of
module length via the explicit subrepresentation order isomorphism.
The p-adic specialization also reuses the published normalized-parabolic
finite-length and exactness proofs through `Aubert.AlternatingOperator`.
Their transitive representation-theoretic and classification dependencies remain
those of the existing proofs; this module makes no classification-independence
claim and supplies no new external structural assumption. The host task's
source/dependency note records the declaration-body closure separately.

This focused unit compares actual GL quotient and product Levi Jacquet models.
The shared general reductive datum, its induction model, the general-to-GL
operator comparison, Haar modulus bridge and full graded Zelevinsky comparison
remain separate host or sibling obligations.
