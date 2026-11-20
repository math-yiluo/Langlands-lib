# Induced support of a cuspidal isobaric sum

`Langlands.Global.cuspidalIsobaricSupport` proves
`Langlands.Global.CuspidalIsobaricSupportStatement.{u, uQ}`. It keeps the
cuspidal presentations, the automorphic quotient, and the archimedean
parameters supplied by the hypothesis. The block product in the conclusion
uses the original index order of the presentations.

## Finite places

`cuspidalIsobaricSum_finiteSupport` uses the local isobaric-sum witnesses and
their embeddings into the quotient. The local occurrence lemma inducts on
the block list. It applies the binary Langlands-head occurrence theorem to
the head of the first block and a head of the sum of the tail labels, then
uses exactness and induction in stages to compare with the full ordered
product. The exceptional set is the union of the exceptional sets of the
cuspidal presentations. Outside it, the multisegment labels of the spherical
blocks are multisets of unramified singleton segments. Their sum is the
singleton label of the pooled spectrum, so the chosen isobaric sum is
spherical by the spherical quotient construction and uniqueness of the
Langlands head.

## Archimedean places

At a real or complex place, the Langlands-ordered standard module has an
equivariant map into the given operator subquotient. Its range carries the
restricted compact action and the Lie operators along real matrix directions.
The range hypotheses make this a nonzero simple target for the joint
operators. A subspace stable for the restricted operators maps under
inclusion to a stable subspace inside the original range. This identifies
the simplicity hypotheses of the place predicate and the specialization
theorem.

The real and complex permutation lemmas move this constituent across
adjacent swaps. They shift one exponent in both orders, keeping the compact
actions fixed and the Lie operators affine. The shifted pair is unlinked
when its two exponents have different imaginary parts. An infinite set of
such parameters gives intertwining equivalences. A finite sum of compact
isotypic projections detects the constituent. The specialization proof uses
polynomial identities for the determinants of compressed operators and
transfers occurrence at zero, the original parameter. Induction on the list
permutation reaches the blocks in index order.

The resulting stable subspace of the compact-finite standard module maps
injectively into the ambient space of functions. Transport along this
inclusion gives the required subspace of functions. The surjection to the
original range, followed by its inclusion into the operator subquotient,
gives an equivariant map with the same nonzero irreducible image.

## Sources

- Getz and Hahn (2024), `getz-hahn-2024-automorphic-representations`, Theorem
  10.7.5 and (10.35), printed p. 288 (PDF p. 300), give the induced-constituent
  assertion. Theorems 10.6.3 and 10.6.4, printed pp. 285–286 (PDF pp. 297–298),
  give the local sphericity and occurrence steps.
- Tadić (1986), `tadic-1986-unitary`, Proposition A.4(ii), printed p. 372
  (PDF p. 39), supplies the binary occurrence theorem. Zelevinsky (1980),
  `zelevinsky-1980-induced-ii`, §1.7 and Theorem 1.9, printed pp. 172–174
  (PDF pp. 9–11), gives the induction-in-stages and constituent comparison
  underlying the ordered block product. The Lean proof uses the actual
  induction-in-stages isomorphism.
- Badulescu and Renard (2010), `badulescu-renard-2010-unitary-dual`,
  Definition 2.2 and Remark 2.3, printed p. 1123 (PDF p. 10), and Proposition
  2.4, printed p. 1124 (PDF p. 11), give the archimedean reordered-product
  constituent comparison. The Lean proof derives the required occurrence
  transfer by specialization. The unlinked inputs use Mœglin (1997),
  `bailey-knapp-1997-pspm61`, §8 and §10, Theorem 10b and its proof, printed
  pp. 163–165 (PDF pp. 172–174), for the real case, and Tadić (2009),
  `tadic-2009-gl-n-c-gl-n-r-unitary-duals`, §1, (1-1) and the sentence after
  (1-2), author's PDF pp. 5–6, and §3, author's PDF p. 11, for the complex
  case.
