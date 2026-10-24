# All-ranks entrywise Whittaker character

Author: Worker 127. This module constructs the character and functional
interfaces for the unchanged `Langlands.InducedWhittakerTypeStatement`.
The coefficient ring `F` and complex representation module `V` have independent
universes. The construction works for every commutative ring `F`, every
`AddChar F ℂ`, and every natural rank `d`, including zero and one. It requires
no topology, nontriviality, or unitarity until the explicitly bundled comparison.
In particular, every `PadicField.Carrier` is covered without restricting the
universe of its representation module.

## Character and evaluation

`entrywiseCharacter ψ d : upperUnipotent d F →* ℂˣ` uses the actual published
matrix subgroup. In rank zero it is the trivial homomorphism. In rank `n + 1`
it composes `UpperUnipotent.superdiagonalSum` with
`ψ.toMonoidHom.toHomUnits`. The latter promotes a homomorphism from a group
to a units-valued homomorphism, using the value at the inverse as the inverse
unit. Thus multiplicativity and invertibility are constructed, never assumed.
`entrywiseCharacter_apply_sum` exposes its positive-rank sum formula.

`entrywiseProduct_eq_adjacentProduct` proves, for every actual `GL_(n+1)`
matrix, that the double product selected by `b.val = a.val + 1` equals
`∏ i : Fin n, ψ (g.val i.castSucc i.succ)`. The proof splits off the last
row, whose product is one, and selects the unique successor column in each
remaining row. Induction on finite sets and the additive character law turn
the sum formula into this product. Consequently `entrywiseCharacter_apply`
proves the exact all-ranks formula

`(entrywiseCharacter ψ d u : ℂ) = ∏ a : Fin d, ∏ b : Fin d, if b.val = a.val + 1 then ψ (u.val.val a b) else 1`.

`entrywiseCharacter_rankZero` and `entrywiseCharacter_rankOne` identify both
small-rank characters with the trivial homomorphism. Their products are empty
or contain only factors one; no positive-rank premise is hidden in the
all-ranks formula.

## Functional interfaces

`mem_functionals_entrywiseCharacter_iff` identifies membership in the existing
`Whittaker.functionals` submodule with the exact inline matrix condition in
`InducedWhittakerTypeStatement`: for every `g`, the conjunction of strictly
lower entries zero and diagonal entries one implies
`ℓ (ρ g v) = (∏ a, ∏ b, if b.val = a.val + 1 then ψ (g.val a b) else 1) * ℓ v`
for every vector `v`. This is proved by packaging and unpackaging membership
in the actual `upperUnipotent` subgroup and rewriting the character formula.
The equivalence applies to every representation on every complex module,
including the induced carrier and each separate block carrier in that target.
`mem_functionals_entrywiseCharacter_iff_entrywise` further identifies the
condition with the published positive-rank `EntrywiseEquivariant` predicate.

`entrywiseCharacter_eq_standardCharacter` identifies the actual units-valued
homomorphisms at rank `n + 1`. The raw-character version
`entrywiseCharacter_eq_standardCharacter_ofComplex` reuses Worker 118's
published `UnitaryAdditiveCharacter.ofComplex`. Its hypotheses are continuity,
nontriviality, and norm one, and `ofComplex_complex` identifies its complex
projection with the original character definitionally. No second packaging
construction is introduced. `functionals_entrywiseCharacter_eq_glFunctionals`
is literal equality of the functional submodules, and
`mem_glFunctionals_ofComplex_iff_doubleEntrywise` exposes the target's double
product directly to existing `glFunctionals` consumers.

## Source, derivation, and scope

The original character convention is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions*, American Journal of Mathematics 105 (1983),
printed p.377 (the product over first-superdiagonal entries). The functional
condition is Section 2.1, printed p.385, equation (1). Both original scanned
pages were read visually (PDF pages 12 and 20). Registered source:
`jpss-1983-rankin-selberg`; retained original
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`;
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
No erratum note for this source was present in the checked project, Library,
or literature errata locations.

The source works over a nonarchimedean local field and discusses admissible
representations of finite type. The extension to arbitrary commutative rings,
raw additive characters, arbitrary complex modules, and rank zero is an
internal algebraic construction justified by the implemented homomorphisms
and finite-product identities. The interface comparisons are internal
consequences of the published definitions. The new companion
`Whittaker.LocalizationDual` independently gives the algebraic quotient-dual
bridge. Neither module asserts induction heredity, uniqueness, the geometric
lemma, or any conclusion of `InducedWhittakerTypeStatement`.

The published `PrerequisiteInterfaces`, `GeneralLinear`, `Algebraic`, and
`Group.GL.UpperUnipotent` constructions are reused by Lean import; their
Lean/Markdown pairs and the induced statement remain unchanged.
