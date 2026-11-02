# Both repeated-factor cuspidal triple Jacquet transfers

The theorem `Langlands.Classification.repeatedCuspidalTripleJacquetTransfer`
proves exactly the Library proposition
`Langlands.Classification.RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T`.
It proves both implications, with every original actual factor and every
unrestricted outside factor retained. It adds no premise. The prime, field
and topological data are supplied, the field and representation universes
are independent, and the ambient and factor carriers lie in `max uF uV`.
The published statement and its imported definitions are unchanged.

## Implemented local proof

`CuspidalSupport.LocalTripleSeeds` proves the local uniform conjunction.
An actual irreducible cuspidal tensor occurring as a Jacquet subquotient
becomes an actual Jacquet quotient by the lower cuspidal constituent
theorem. First adjunction gives an actual injection of the irreducible
ambient object into the ordered three-factor induction. This is derived
from the stated subquotient hypothesis.

For \([A]=\nu[B]\), put \(P=A\times B\). Case split on irreducibility of
this actual product. If it is irreducible, lower two-factor commutativity
gives an actual isomorphism with \(B\times A\); induction with the last
factor gives the required move.

Otherwise the lower rank-two adjacent structure produces its actual
nonzero proper subrepresentation \(L\), irreducible quotient \(Q\), and
the ordered Jacquet modules of both. The substantive local rank-three
input proves both \(L\times A\) and \(L\times B\) irreducible.
For \(L\times A\), an actual comparison identifies \(L\) with a quotient
of the increasing product \(B\times A\), and applies the independently
proved increasing-quotient upper-factor theorem. For \(L\times B\),
actual smooth duality identifies \(L^\vee\) with a quotient of the
increasing product \(A^\vee\times B^\vee\). The relation
\([B^\vee]=\nu[A^\vee]\) permits the same upper-factor theorem.
Same-order product duality and admissible biduality then reflect
irreducibility to \(L\times B\).

The increasing-quotient upper-factor theorem is proved by actual positive
Leibniz filtrations and partial derivatives of the adjacent quotient.
Its proper common-rank derivatives have finite length and every simple
actual constituent has a support containing the upper endpoint. Choose
a highest nonzero derivative of a simple constituent of the product.
If it were proper, common-rank vanishing forces order \(d\) or \(2d\).
The individual highest-derivative support shift would place the next
twist of that upper endpoint in the displayed source support
\(\{B,A,A\}\), contrary to integral twist freeness. Thus the top derivative
is nonzero on every simple actual subquotient. Its value on the product
has dimension one, so actual derivative exactness and finite length imply
product irreducibility. An actual surjection from the literal \(B,A,A\)
induction supplies the required source support presentation. No
classification or product-presentation premise remains.

For the final local move, take the actual short exact sequence
\[
 L\times C\longrightarrow P\times C\longrightarrow Q\times C
\]
with \(C=B\) or \(C=A\). The simple-source exact alternative either
injects the ambient object into \(Q\times C\), or identifies it with
\(L\times C\). In the quotient case the actual Jacquet formula and first
adjunction embed \(Q\) into \(B\times A\), giving output \(B,A,C\).
In the other case, actual irreducible product commutativity moves \(C\)
past \(L\); the actual inclusion \(L\hookrightarrow A\times B\) then
gives output \(C,A,B\). Explicit induction-in-stages equivalences and
entry-preserving rank reindexings retain the three literal factors.
First adjunction recovers the actual Jacquet occurrences.

For \(C=B\), both alternatives give \(B,A,B\). For \(C=A\), they give
\(B,A,A\) or \(A,A,B\). Actual isomorphisms from equality of
supercuspidal classes replace the repeated representative. This proves
the uniform local input without a remaining local theorem premise.

## Ambient extraction and refinement

`CuspidalSupport.repeatedCuspidalTripleJacquetTransfer_of_uniform`
applies that proved local result to the exact published ambient statement.
It merges only the three selected consecutive blocks, leaving every
outside block a singleton. Actual finite image filtrations and exact
Jacquet functors extract one family of actual irreducible admissible
finite-length coarse factors. The tensor occurrence in their refined
Jacquet module yields every original inner occurrence, including the
selected three-factor occurrence.

The two rank-indexed class equalities force equality of the three
selected ranks. Equality elimination identifies their actual shape with
the positive uniform three-block shape. The local theorem applies to
that actual coarse factor. Explicit refinement and tensor comparisons
then combine its new selected occurrence with all original outside
occurrences. The result is the actual external tensor of the original
permuted family at the literal adjacent permutation and `B.permute`.
The disjunction is chosen after a common extraction, so both branches
refer to the same ambient object and unchanged outside data. Outside
repetitions, linkage and cuspidal lines are never restricted.

## Source scope and independence

The motivating source is Jantzen, *On Square-Integrable Representations
of Classical p-adic Groups* (2000), Lemma 2.2.2, printed pp.545–547
(PDF pp.7–9); normalizations are Section 1.2, printed pp.541–542.
The registered source is `jantzen-2000-square-integrable-classical-i`,
SHA256 `539eee93dd339c42bf6d065bbb1969ab0e2c6c54699c5b4447a2166a3ddf9428`.
The printed argument uses one integral twist line of a unitary
supercuspidal and a lexicographically minimal constituent. It motivates
the two patterns but does not by itself establish this broader target.
The implemented proof directly uses arbitrary supplied supercuspidals,
actual local product structure and extraction/refinement; it needs no
unitary, lexicographic, common-line or square-integrability reduction.
It retains the supplied upper parabolic normalization, positive
half-modulus covariance, right translation and \(\nu=|\det|\).
The context's reversed printed lexicographic inequality is not used.

The new proof imports and used lower bodies follow these routes:

- Actual image and quotient filtrations, tensor flatness, compact
  averaging and exact coinvariants supply extraction and product
  exactness. Refinement comparisons are explicit quotient transitivity,
  tensor equivalences and half-modulus calculations.
- Coarse irreducible factorization uses Schur and density arguments,
  multiplicity evaluation and actual admissible subquotient extraction.
- The local derivative argument uses actual localization and minus
  functor identities, individual highest-derivative pairing/support
  shift, central-character twist freeness, Whittaker multiplicity one
  and the elementary exact-functor length criterion.
- Lower finite length of a product of irreducibles comes from separately
  embedding each factor into cuspidal induction, inducing the tensor
  injection and regrouping. Cuspidal induction length is bounded using
  a finite detecting family of minimal nonzero Jacquet modules, the
  associated geometric filtration and nonassociation vanishing.
- Actual product commutativity uses inverse transpose, smooth induction
  duality and Gelfand–Kazhdan on simple factors. Smooth supercuspidal
  duality uses the actual upper/opposite canonical pairing and block
  conjugacy. These supply individual maps and factors.

None of these routes invokes the parent analytic strong-head
classification, ordered strong-head existence, general ordered quotient
coverage, multisegment exhaustion, tempered block uniqueness,
square-integrable Langlands classification or exhaustion, or regular
exhaustion, including their conclusions under another name. No global
decomposition by cuspidal lines is used. The final import closure,
unchanged target dependency hashes and declaration inspection are
recorded with the submission audit. Broad proposition definitions in
some lower imports are not used as proved classification conclusions.

The reproduced final closure contains 1,082 project modules and 278
external import names. Every project module has nonempty paired Markdown.
The target and all 68 project modules in its recursive dependency closure
have both files byte-identical to Library base
`e058cb4d3adbd71764731d87c4cbfcb5805696e8`. The 27 new pairs needed over
that base, including this proof pair, are explicitly included in the
submission. Declaration inspection preserves exactly `uF,uV` and reports
only `propext`, `Classical.choice` and `Quot.sound`.

Worker 168 supplied the increasing-quotient derivative/irreducibility
proof and the literal unequal-rank swap adapter. Worker 1216 supplied
the reused generic ordered tensor occurrence adapter. Worker 19 supplied
the actual ambient calculus, local exact-sequence and dual transports,
the two seed moves and final assembly.
