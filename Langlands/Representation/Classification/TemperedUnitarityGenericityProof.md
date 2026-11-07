# Invariant positive forms and genericity for tempered GL representations

Author: Worker 62.

`Langlands.Classification.temperedUnitarityAndGenericity` proves exactly
`Langlands.Classification.TemperedUnitarityAndGenericity.{uF,uV} F T`
from [TemperedBlockStatement](TemperedBlockStatement.md). Its parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The field and representation universes remain independent. For every
irreducible analytically tempered smooth representation of rank `n + 1`,
including rank one, the conclusion supplies an invariant positive definite
Hermitian form and full standard genericity for every bundled continuous
nontrivial unitary additive character.

## Implemented proof

Install the supplied topology `T.topology` and introduce the original
representation `π`, its irreducibility and its analytic temperedness.
Apply the published `temperedBlockExhaustion.{uF,uV} F T` at positive rank
`n + 1`. It supplies an actual ordered block shape `B`, smooth block
representations `σ`, their irreducibility, analytic square-integrability
and invariant positive forms, and a category isomorphism
`i : π ≅ (T.normalizedProductInductionFunctor B).obj σ`.
`SmoothRep.equivOfIso i` gives an equivariant linear equivalence `e`
from the original representation to this actual normalized product.

Apply the published `squareIntegrableBlockInduction.{uF,uV} F T`
to the supplied blocks. Its second conclusion is `IsUnitarizable` of
their product. The reverse implication of
`isUnitarizable_iff_of_equiv e` pulls this conclusion back to `π`.
That transport pulls an actual `InvariantPositiveForm` back along `e`:
its value on `v,w` is the product form evaluated on `e v,e w`.
Equivariance gives invariance and injectivity gives positive definiteness.

For an arbitrary character `ψ` introduced by the target, the published
`squareIntegrableBlockGenericity.{uF,uV} F T` gives
`Whittaker.IsGeneric ψ n` for the same normalized product.
The reverse implication of `Whittaker.isGeneric_iff_of_equiv ψ n e`
transports all three clauses to `π`: irreducibility, admissibility and
existence of an actual nonzero standard Whittaker functional.
The functional transport is precomposition with `e`, preserving the
same upper-unipotent subgroup and character. Surjectivity of `e` ensures
that a nonzero functional has nonzero pullback.

Every carrier remains in `Type (max uF uV)` and every compatible `T`
is allowed. The hypothesis is the unchanged Library `T.IsTempered`,
with smooth-dual coefficients on the full central quotient, all Borel
Haar measures and every real exponent `2 + ε` for `ε > 0`.
The product uses the standard upper parabolic, positive half-modulus
covariance and right translation. The statement pair and its imports
are unchanged, and the theorem has no additional hypotheses.

## Provenance

This is a derived composition of published closed proofs, together with
published equivalence transports. The mathematical inputs and their
implemented arguments are documented in the following pairs:

| Published proof pair | Role |
| --- | --- |
| [TemperedBlockExhaustionProof](TemperedBlockExhaustionProof.md) | Constructs the actual analytic square-integrable blocks and the category isomorphism. |
| [SquareIntegrableBlockInductionProof](SquareIntegrableBlockInductionProof.md) | Supplies an invariant positive form on their normalized product. |
| [SquareIntegrableBlockGenericityProof](SquareIntegrableBlockGenericityProof.md) | Supplies full standard genericity for every allowed character. |
| [Unitary.Basic](../Unitary/Basic.md) | Pulls the invariant form through the actual equivalence. |
| [Whittaker.Transport](../Whittaker/Transport.md) | Pulls back the nonzero functional and transports full genericity. |

Kudla, *The local Langlands correspondence: the non-archimedean case*
(1994), Proposition 2.2.1, printed p.373, gives the tempered block
description following the analytic definition on p.372; §2.3, p.374,
states tempered genericity and independence of the additive character.
Jacquet–Shalika, *The Whittaker models of induced representations* (1983),
§1.2, pp.108–109, gives the smooth upper-parabolic functional formulation.
Casselman, *Introduction to the theory of admissible representations of
p-adic reductive groups*, draft 1 May 1995, Proposition 2.5.4, p.29,
provides the invariant-form construction used upstream for square-integrable
blocks. These retained originals are registered as
`kudla-1994-local-langlands-nonarchimedean`,
`jacquet-shalika-1983-whittaker` and
`casselman-1995-admissible-representations`; their precise editions and
fingerprints are recorded in the unchanged statement Markdown.

The local argument uses the proved Library inputs above. Their paired
accounts retain the analytic comparisons, support, segment and induction
proof routes. The source boundaries in
[the classification source note](../../../notes/henniart/gln-classification-sources.md)
remain applicable: Jacquet 1977 supplies no tempered exhaustion theorem.
