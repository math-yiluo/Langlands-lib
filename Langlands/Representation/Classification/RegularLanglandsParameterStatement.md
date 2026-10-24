# Regular Langlands block-rank and real-parameter uniqueness

Author: Worker 346.

`Langlands.GLRegularLanglandsParameterUniquenessStatement` is a closed
proposition definition isolating the standard-parabolic and real-parameter
conclusions of Silberger's Proposition 6.1 for the Library's actual tempered
Langlands data for `GL_n`. It is a statement, with no proof supplied.

## Exact quantifiers and conclusion

For every prime `p`, `F : PadicField.{uF} p`, compatible topological realization
`T`, and positive rank `n`, take two values
`d e : T.TemperedLanglandsDatum.{max uF uV, uF} n` and two actual smooth
complex representations
`π τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)`.
Assume precisely

```
d.IsLanglandsQuotient π
e.IsLanglandsQuotient τ
Nonempty (π ≅ τ).
```

The conclusion is the existence of an order isomorphism
`a : Fin d.shape.length ≃o Fin e.shape.length` such that, for every `i`,

```
d.shape.size i = e.shape.size (a i)
d.exponent i = e.exponent (a i).
```

The two equalities occur as a conjunction under the same universal quantifier.
The order isomorphism identifies the ordered positions, not just the multiset
of block ranks. Thus the conclusion identifies the standard upper block
parabolic and its real determinant parameters. It makes no assertion about
isomorphisms between the inducing tempered representations, quotient maps,
or a chosen canonical matching.

The field universe `uF` and carrier parameter universe `uV` are independent.
The carriers are saturated to `max uF uV`, exactly as in
`GLRegularLanglandsDataUniquenessStatement` in
[RegularLanglandsStatement](RegularLanglandsStatement.md). This accommodates
the actual induced function spaces and imposes no finite-dimensionality
condition. There are no free representation or field parameters outside the
proposition definition.

## Existing objects and normalization

The only import is
`Langlands.Representation.Classification.LanglandsData`.
Its `TemperedLanglandsDatum` contains an ordered positive block shape summing
to `n`, actual smooth irreducible tempered block representations, real
exponents, and `StrictAnti` for those exponents. Temperedness is the existing
analytic predicate, including admissibility and unitary scalar central
character, with matrix-coefficient norms in `L^(2+ε)` modulo the center.
No continuation, exponent comparison, matching, or quotient witness is a
field of this datum.

The existing `standardModule` is normalized induction from the actual upper
block parabolic of the external tensor of `|det|^(t_i) σ_i`. Its covariant
functions carry right translation and the positive upper half modulus.
`IsLanglandsQuotient` asks for irreducibility and an actual surjective
intertwiner from that standard module. It does not assert the unique-head
property. Neither this relation nor any existing definition is changed here.

Silberger, p.96, uses `I(P, σ) = Ind_P^G(δ_P^(1/2) σ)` and
`χ_ν(m) = q^(i⟨ν,H(m)⟩)`. His parameter `ν = -iλ` therefore gives
`q^(⟨λ,H(m)⟩)`. Under the Library's residue-normalized absolute value
`|ϖ| = q^(-1)` and determinant-coordinate convention this is
`∏_i |det m_i|^(t_i)`. On block scalars `m_i = a_i I_(n_i)` it is
`∏_i |a_i|^(n_i t_i)`. In particular, the statement compares determinant
exponents `t_i`, rather than confusing them with scalar-coordinate weights
`n_i t_i`. This is the convention translation recorded in the existing
[Silberger reading note](../../../notes/henniart/silberger.md) and
[regular quotient statement](RegularLanglandsStatement.md).

For the usual Weyl-invariant inner product on the full diagonal torus, the
pairing of the block-constant parameter with the projected adjacent root
is `t_i - t_(i+1)`. Positive regularity is therefore strict descent, as in
the existing datum. No individual exponent must be positive, and no weighted
sum must vanish. All common real central twists are retained. A one-block
datum has vacuous strict descent and allows every real determinant exponent.

## Original source and scope correspondence

The source is A. J. Silberger, *The Langlands quotient theorem for p-adic
groups*, Math. Ann. 236 (1978), 95–104, registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
with SHA-256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The retained file is
`literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`.
For this contribution, printed pp.96–97, 99 and 102–103 were read as text
and checked in page images; one-based PDF pages are printed pages minus 94.
No source-specific author erratum was found in the supplied errata locations.

Theorem 4.1(1), p.99, defines the distinguished quotient `J(σ, λ)` using
uniqueness of the irreducible quotient. Theorem 4.1(2), p.99, and
Proposition 6.1, pp.102–103, assert equality of standard parabolics, real
parameters, and tempered classes when the distinguished quotients are
isomorphic. This pair extracts only the first two conclusions, specialized
from general reductive groups to the actual upper block parabolics of
`GL_n` over finite extensions of `Q_p`.

The specialization also expresses the tempered Levi representation as the
actual external tensor of the tempered blocks. Its irreducibility and
analytic temperedness comparison need separate proofs; they are not new
assumptions here. Passing from the source's distinguished quotients to our
arbitrary irreducible quotient witnesses will use the separately published
`GLRegularLanglandsHeadExistenceStatement` and its future proof: equality
of kernels identifies every irreducible quotient with the head. This
explains the reformulation without adding head hypotheses to this target.

## Remaining proof dependencies and excluded downstream recovery

The parameter argument in Proposition 6.1, pp.102–103, first uses associated
cuspidal support to obtain a Weyl comparison. It then uses analytic
continuation of actual class exponents, tempered cone inequalities,
orthogonality and a Weyl-invariant inner product, followed by rigidity in
the standard chamber. These are unproved dependencies of this statement,
not facts supplied by declaring it.

In particular, the existing `Exponents.DualJacquetStatement` states finite
dual spectrum, its comparison with actual opposite Jacquet constituents,
and tempered support. It does not supply analytic continuation in the real
parameter. Silberger's class exponents on p.97 use the normalized opposite
Jacquet module `δ_P^(1/2) π(P̄)`. A future continuation statement must concern
those actual constituents and their parameter variation; finite character
sets at a fixed parameter are insufficient.

The elementary numerical part has the separate target
`Langlands.Exponents.OrthogonalParameterComparisonStatement`.
Even a proof of that target would not supply the representation-theoretic
cone bounds or the Weyl comparison. The existing order constructions
`RegularLanglandsOrder.orderIsoOfExponentEquiv` and `orderedBlockMatching`
likewise require matching input. They do not derive matching from an
isomorphism of quotients.

The published [Lemma 5.3 scope audit](../../../notes/jacquet/silberger-lemma53-scope.md)
was independently approved by Reviewer 1486. It identifies a `GL₂`
obstruction to the printed unrestricted multiplicity equality and the
inner-constituent restriction supported by its proof. It is a source audit,
not a Lean theorem or an author erratum. Its caution also applies to use
of Corollary 5.4. Lemma 5.6 has an inner-quotient hypothesis, but the
continuation argument still needs its own justification. This pair neither
imports nor assumes the suspect unrestricted equality.

After identifying the standard parabolic and parameter, the source uses
Propositions 5.8 and 5.7 to recover the tempered class. That final step is
deliberately outside this statement. This target is a prerequisite for
`GLRegularLanglandsDataUniquenessStatement`; invoking that stronger target,
or downstream square-integrable block classification which depends on it,
would be circular in the intended proof development.

The future proof task must separate substantial missing constructions,
statements and proofs in that dependency order, in particular the actual
class-exponent continuation/comparison. It must preserve the weak quotient
hypotheses, all real central twists, the one-block case, and both universe
parameters throughout.
