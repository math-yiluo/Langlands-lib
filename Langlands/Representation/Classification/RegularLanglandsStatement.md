# The regular-chamber Langlands quotient theorem for GL_n

Author: Worker 19.

`Langlands.GLRegularLanglandsQuotientStatement` is the conjunction of three
proposition definitions for actual complex representations of `GL_n(F)` over
every finite extension of `Q_p`. It states the regular-positive tempered form
of Silberger's Langlands quotient theorem. It proves none of its clauses.

## Exact clauses

For every prime `p`, finite extension `F : PadicField p`, topological realization
`T`, and positive integer `n`, the components are as follows.

1. `GLRegularLanglandsHeadExistenceStatement`: every
   `d : T.TemperedLanglandsDatum n` has a smooth representation `π` satisfying
   `d.IsLanglandsHead π`.
2. `GLRegularLanglandsDataUniquenessStatement`: if `π` and `τ` are irreducible
   quotients of the standard modules of `d` and `e`, and `π ≅ τ`, there is an
   order isomorphism between their finite block-index sets which matches
   every block size, every real exponent, and every tempered block up to an
   actual smooth-representation isomorphism after transport by the equality
   of ranks.
3. `GLRegularLanglandsExhaustionStatement`: every irreducible admissible
   smooth representation `π` is itself the irreducible head of the standard
   module of some `d : T.TemperedLanglandsDatum n`.

An order isomorphism of the finite index sets preserves the positions of the
blocks. Thus the second clause recovers the ordered block shape, and hence
the standard parabolic, rather than merely an unordered partition. The equality
`h i` transports a representation of `GL_(d.shape.size i)` to one of
`GL_(e.shape.size (a i))` before the isomorphism is requested. It does not
identify different ranks without evidence. All isomorphisms occur under
`Nonempty`; there is no choice of canonical representatives.

The second clause uses the weaker quotient premises deliberately. Part (1)
identifies every such quotient with the unique head, so part (2) of the source
applies to arbitrary quotient witnesses. Conversely, the exhaustion clause
puts the given representation itself in the head relation: a source
isomorphism from it to the distinguished quotient transports the surjection
without changing its kernel. These are documented reformulations, not
additional assumptions.

## Actual data and quotient objects

The sole project import is the published
`Langlands.Representation.Classification.LanglandsData`.
`TemperedLanglandsDatum` contains an ordered positive block shape, actual
smooth irreducible analytically tempered representations `σ_i` of its factors,
and real numbers `t_i` with `StrictAnti t`. It contains no quotient, head,
classification witness, or Jacquet criterion.

Its standard module is the actual normalized upper parabolic induction of
the external tensor product of `|det|^(t_i) σ_i`. The action on covariant
functions is right translation and the covariance contains the positive
square root of the upper parabolic modulus. Both the finite tensor
representation and function-space induction are published constructions.

`d.IsLanglandsHead π` unfolds to algebraic irreducibility of `π`, an actual
surjective intertwiner from the standard module to `π`, and equality of the
linear kernels of this map and every other surjective intertwiner to an
irreducible representation. This is uniqueness as a quotient object. It is
stronger than merely asserting one isomorphism class among the quotients.
Silberger's Lemma 5.5 and the proof of Lemma 5.6 rule out two distinct
irreducible quotient objects by considering a quotient onto their direct sum;
the head formulation preserves that conclusion. It does not assert that the
quotient map itself is unique.

The exhaustion hypothesis retains admissibility explicitly. Smoothness comes
from `SmoothRep`; irreducibility is Mathlib's actual irreducibility predicate
and excludes the zero representation. The tempered datum already includes
admissibility of each block through `T.IsTempered`. That analytic predicate
requires a smooth unitary scalar central character and all smooth
matrix-coefficient norms in `L^(2+ε)` modulo the center for every `ε > 0`
and every Borel Haar measure. It is independent of the conclusions here.

## Original sources and normalization

The retained Silberger article was read in full; its theorem and
formula-bearing pages were checked as page images. Kudla's printed
pp.367–368 and 372–374 were also read directly for the explicit block and
analytic conventions. No errata file for either source was present in the
current Library when this pair was prepared.

| Source | Exact locations | Correspondence |
| --- | --- | --- |
| A. J. Silberger, *The Langlands quotient theorem for p-adic groups* (1978), registered as `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`, SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5` | §1, pp.95–97; Theorem 4.1(1)–(3), p.99; Proposition 5.1 and Lemmas 5.2–5.6, pp.99–101; Proposition 6.1, pp.102–103; Proposition 7.2, pp.103–104 | Normalized induction and regular chamber; respectively head existence, inducing-data uniqueness, and exhaustion. The one-based PDF page is the printed page minus 94. |
| S. S. Kudla, *The local Langlands correspondence: the non-archimedean case* (1994), registered as `kudla-1994-local-langlands-nonarchimedean`, SHA256 `0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b` | §0, p.367; §1.1, pp.367–368; §2.2, pp.372–374, especially the paragraph after (2.2.3) and Theorem 2.2.2(a)–(b) | Actual upper block induction, determinant twists, analytic temperedness, unique quotient, exhaustion, and ordered block uniqueness. The retained file is the complete *Motives*, Part II volume; its one-based PDF page is the printed page plus 10. |

Silberger's theorem applies to arbitrary connected reductive groups over
nonarchimedean local fields. This pair restricts it to `GL_n` over finite
extensions of `Q_p`, with its standard upper block parabolics. In block form,
the irreducible tempered representation of the product Levi is expressed
as the external tensor of irreducible tempered block representations.
Factorization of irreducible admissible product representations and the
correspondence of temperedness with temperedness of the factors are part of
the mathematical specialization, not fields assumed for an arbitrary
Levi representation. Kudla's explicit block version confirms precisely the
existence and uniqueness conclusions used here. Its statement is not a
replacement for the original Silberger proof route.

The Library uses the residue-normalized absolute value `|ϖ| = q^(-1)`.
Silberger's character on p.96 is `χ_ν(m) = q^(i⟨ν,H(m)⟩)`, so his parameter
`ν = -iλ` in Theorem 4.1 yields the positive real character
`q^(⟨λ,H(m)⟩)`. For the product Levi, this is
`∏_i |det m_i|^(t_i)`. On its split center
`diag(a_i I_(n_i))`, its exponent in block-scalar coordinates is
`r_i = n_i t_i`, where `n_i` is the block size.

Using the Weyl-invariant inner product on the full diagonal torus and
projecting to the block-constant subspace, the pairing of `λ` with the
projected root between adjacent blocks is `t_i - t_(i+1)`. Thus the positive
regular chamber is precisely strict descent of the determinant exponents.
The code uses `StrictAnti` on the finite ordered set, equivalent to adjacent
strict descent. There is no condition `t_i > 0` on each individual exponent,
nor a zero-sum condition: the central direction is unrestricted. In
particular, the one-block case allows every real determinant twist of an
irreducible tempered representation; its regularity condition is vacuous.

The analytic bridge between Silberger's weak coefficient definition of
temperedness and the Library's `L^(2+ε)` convention is documented in the
published `TemperedExponentStatement.md` and
`TemperedInductionStatement.md`. Its future formal proof remains necessary
when implementing Silberger's route. Kudla p.372 uses the same analytic
convention as this pair.

## Universes, grouping, and remaining obligations

The field universe `uF` and representation parameter universe `uV` are
independent. The smooth blocks, standard modules, and quotient carriers in
these statements all lie in `Type (max uF uV)`. This universe is closed under
the actual induction construction, whose functions involve the field-sized
group, and matches the existing `IsLanglandsHead` interface. It is not an
equality of carriers or a finite-dimensionality restriction. Representations
initially in a smaller universe can be transported to lifted carriers;
exhaustion requires no lowering of a carrier universe. The finite product
factors can be realized in the universe of the original representation,
as in the published product-factorization statement.

These assertions concern strictly ordered tempered data only. To pass from
weakly ordered essentially square-integrable data, the separately published
`Langlands.Classification.SquareIntegrableEqualExponentGrouping` in
`Classification/TemperedBlockStatement` first groups maximal consecutive
equal-exponent runs and identifies the actual induced modules. This
GL-specific step is a separate theorem target; it is not an assumption or
a proof supplied by this pair. No irreducibility of arbitrary reductive
tempered induction is asserted here.

This pair supplies the three top-level conclusions of Theorem 4.1 and the
conclusions of Propositions 5.1, 6.1, and 7.2. It does not separately encode
the finer cuspidal Jacquet multiplicity comparisons of Lemmas 5.3 and 5.6,
the relative recovery and cosocle multiplicity assertions of Propositions
5.7–5.9, the semistandard conjugacy formulation of Corollary 6.2, or the
maximal-cone construction inside the proof of Proposition 7.2. Those remain
statement obligations in the broader task. The general root/weight cone
lemma, exponent criteria, fixed-central-character splitting and tempered
prerequisite families already have separate targets; their proofs, product
specialization, chamber conversion and the present three implications all
remain open. No proposition from those families is imported as a proved fact.
