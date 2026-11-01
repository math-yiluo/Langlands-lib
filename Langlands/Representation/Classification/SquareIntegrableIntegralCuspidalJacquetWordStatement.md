# Integral cuspidal Jacquet words for analytic discrete series

`Langlands.Classification.SquareIntegrableIntegralCuspidalJacquetWordExistence F T`
is a proposition definition. For every positive rank `n` and actual smooth
complex representation `π` of `GL_n(F)`, irreducibility and the analytic
hypothesis `T.IsSquareIntegrable π.representation` imply the existence of:

- a rank `m > 0`;
- an actual supercuspidal representation `A` of `GL_m(F)`;
- a nonempty ordered integer list `w` satisfying
  `IntegralCuspidalJacquetWord F T m n A π w`.

The prime and finite p-adic field are arbitrary, and `T` is the supplied
compatible topological data. The field and carrier universes `uF,uV` are
independent. Both `π` and `A` have carriers in `Type (max uF uV)`. No canonical
topology, fixed prime, finite-dimensional carrier or relation between the
universe parameters is imposed.

## Actual occurrence and analytic hypothesis

The imported `IntegralCuspidalJacquetWord` retains a block shape `B` of total
rank `n`, actual supercuspidal objects `C i`, and integer exponents `e i` in
block order, with `w = List.ofFn e`. For every block, equality in the dependent
sum over ranks identifies the class of `C i` with the class of `A` twisted by
`|det|^(e i)`, and includes equality of its rank with `m`. The actual external
smooth tensor of the `C i` is a `SmoothRep.IsSubquotient` of the actual
normalized upper Jacquet module of `π` for `B`. The supplied `T` determines the
residue-normalized determinant twists and the inverse half-modulus Jacquet
normalization. A support-set equality or equality in an exact Grothendieck
group does not replace this actual subquotient condition.

`T.IsSquareIntegrable` is the existing analytic predicate on absolute
smooth-dual matrix coefficients, with square integrability on the actual
central quotient for every Borel Haar measure. Its definition already
includes admissibility and a unitary scalar central character. This module
adds neither an admissibility premise nor an exponent-based replacement for
the analytic predicate. It also adds no premise asserting finite length,
finite cuspidal support, factorwise unitarizability or Jacquet occurrence.
There is no unitarity requirement on `A`.

## Original assertion and derivation boundary

The source is Chris Jantzen, *On Square-Integrable Representations of Classical
p-adic Groups*, Canadian Journal of Mathematics 52 (2000), 539–581,
[DOI 10.4153/CJM-2000-025-7](https://doi.org/10.4153/CJM-2000-025-7).
The first claim in the converse proof of Theorem 2.3.1, printed p.549
(one-based PDF p.11), asserts that the cuspidal support of an irreducible
square-integrable `π` lies in `{ν^α ρ : α ∈ α₀ + ℤ}` for one unitary
supercuspidal `ρ` and a real `α₀`, where `ν = |det|`. The present proposition
isolates an actual realization consequence of that support assertion; it does
not state the full segment classification in that theorem.

To pass from support to the present conclusion, a proof must first obtain a
nonzero normalized Jacquet module with an actual finite tensor of
supercuspidal factors, identify those factors with the cuspidal support, and
retain the actual occurrence while identifying their genuine classes. General
irreducible product-Levi objects cannot simply be treated as external tensors.
If the line is expressed using a unitary base `ρ` and exponents `α₀ + e i`,
choose an actual representative of `ν^α₀ ρ` as `A`. Actual twist composition
and isomorphism transport then give the required integer class equalities.
No existence or choice of a unitary base is an additional hypothesis of the
Lean proposition. Positive total rank and positive block sizes must give a
nonempty word and positive base rank.

The source recalls the rank-weighted Casselman inequalities on printed p.548
(PDF p.10), and its local shuffling statement is Lemma 2.1.2 on printed
pp.543–544 (PDF pp.5–6). In the proposed route, if two or more integral lines
occur, choose one and move all its factors to the front in one actual
Jacquet constituent, and all factors of its complement to the front in a
second. Every factor in the complement must be retained even when it occupies
several distinct lines. Strict positivity of the two proper-prefix weighted
sums contradicts the zero full central sum. The weights are the individual
factor ranks times their real exponents. The printed two-line example alone
does not supply this arbitrary finite grouping argument.

This route still requires proofs, or independently audited existing proofs,
of the actual finite cuspidal realization, product-Levi tensor identification,
necessary admissibility and finite-length facts, real unitarizations,
cross-line binary irreducibility and commutation, actual Jacquet transfer
through repeated local shuffles, and the strict Casselman and central-sum
comparisons in the present conventions. Admissibility of `π` itself can be
extracted from the analytic hypothesis. Neither this module nor a pointer to
another statement establishes any of the other inputs. In particular,
`CuspidalSupport.MinimalRefinedJacquetProof` gives quasicuspidal descent, and
`glSingleBlockDiscreteSeriesSupport` gives product-Levi inducing data; neither
by itself supplies this actual supercuspidal tensor on one integral line.

The intended exact proof and all its transitive proof inputs must remain
independent of the parent analytic segment classification and the other
excluded downstream conclusions. In particular, neither Jantzen §2.1.3 nor
Jantzen 1997 Corollary 5.6's global disjoint-support irreducibility, general
ordered quotient coverage, full multisegment classification, or this one-line
support conclusion under another name is an admitted input. A citation's
position before a classification theorem is no independence certificate.
The actual-word definition is a reusable lower construction, not an existence
theorem. Local pair interchange still requires its binary irreducibility and
commutation hypotheses to be proved independently.

## Source record and scope

The retained source is
`literature/Jantzen (2000), On Square-Integrable Representations of Classical p-adic Groups.pdf`,
literature ID `jantzen-2000-square-integrable-classical-i`, SHA256
`539eee93dd339c42bf6d065bbb1969ab0e2c6c54699c5b4447a2166a3ddf9428`.
The support/normalization setup on PDF pp.4–6 and the theorem/criterion on
PDF pp.10–12 were read; the formulas on PDF pp.6,10,11 were also checked
against page images. A bounded search of project and current Library errata
notes and a title-specific web search found no source-specific correction;
this is not a claim that none exists.

This file states an existence target and supplies no proof. The exact proof
successor must prove the named Library proposition for arbitrary `p,F,T` and
independent `uF,uV`, without extra theorem-valued premises, while preserving the
same direct and transitive independence boundary. Statement publication and
proof-task arrangement do not establish word existence, local closure,
lexicographic minimality, segment extraction or a strong segment-head theorem.
