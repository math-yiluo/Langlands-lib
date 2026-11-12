# Multisegment special-head exhaustion

Author: Worker 748. The kernel and degree argument develops the conditional
assembly supplied by Worker 195 of the previous instance.

`Langlands.Classification.multisegmentHeadExhaustion` proves exactly the
published proposition
`Langlands.Classification.MultisegmentHeadExhaustion.{uF,uV} F T` in
[MultisegmentClassificationStatement](MultisegmentClassificationStatement.md).
Its only outer parameters are
`{p : Nat} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
For every natural rank `n` and irreducible smooth complex input `π` on
`GL_n(F)`, it gives a multisegment of degree `n` and an actual ordered
segment-product datum whose induced representation has the original `π`
as its strong irreducible head. No admissibility premise is required.
The independent universes `uF` and `uV` are preserved, with input carriers,
segment bases, blocks and induced carriers in `Type (max uF uV)`.

The proof composes two published unconditional theorems:

- [`orderedMultisegmentQuotientExhaustion`](OrderedMultisegmentQuotientExhaustionProof.md)
  supplies an actual datum `d`, its nonprecedence ordering, its strong
  individual special-segment heads, and a surjective intertwiner
  `q : d.induced.representation.IntertwiningMap π.representation`.
- [`orderedMultisegmentHeadExistence`](OrderedMultisegmentHeadExistenceProof.md)
  applies to this same `d`, ordering and block family. It supplies a strong
  head `π₀`, a surjective head map `q₀`, and equality of the kernel of every
  irreducible surjective quotient map with `ker q₀`.

Apply the latter equality to both an arbitrary irreducible quotient map `q'`
and the original coverage map `q`. Transitivity with the symmetric second
equality yields `ker q' = ker q`. Retain `q`, its surjectivity, the
irreducibility of the original input, and the datum's ordering and individual
heads. These are exactly `d.IsLanglandsHead π`, including kernel uniqueness
for every actual surjective quotient map, even when its target is isomorphic
to another quotient target. The construction therefore gives a strong head
relation for the given input itself.

The multisegment witness is `d.multisegment`, the multiset of the finite list
`List.ofFn d.segments`. Its degree is the sum of the segment degrees.
`Multiset.map_coe`, `Multiset.sum_coe`, `List.map_ofFn` and `List.sum_ofFn`
convert this to the finite sum in `d.degree_sum`, proving degree `n`.
The same datum `d` witnesses the multisegment head relation by reflexivity
of its multisegment equality. The original quotient map is unchanged.

The proof is uniform in `n`, including zero. Both imported theorems include
the actual empty-product case; no positivity premise is introduced here.
The upper block parabolic, normalized induction and right-translation
conventions remain those of the published datum.

This is an internal algebraic composition of the two published results.
The source assertion is Rodier (1982), section 4.3, Theorem 3(c), printed
p.212 (PDF p.13), registered as `rodier-1982-gln`, PDF SHA-256
`389a9155f59022f5f5403bf568216f66b407b6d47e98221d115dcd85e076c8fc`.
The source and dependency audit in the target's companion Markdown records
the printed argument's Bernstein converse, tempered exhaustion and Langlands
quotient inputs. The implemented proof uses the published Lean theorems above,
whose proof pairs document their implementations and provenance. A source
reference or proposition definition is not used as a substitute for a proof.
No downstream square-integrable or regular exhaustion proof is imported.
The target pair and all its imported published pairs are unchanged.
