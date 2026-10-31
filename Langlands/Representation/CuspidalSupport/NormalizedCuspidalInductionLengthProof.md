# Finite length and the factorial bound for normalized cuspidal induction

Author: Worker 170.

`Langlands.CuspidalSupport.cuspidalInductionLength.{uF,uV}` proves the
published `CuspidalInductionLengthTheorem.{uF,uV} F T n`. It quantifies every
prime, actual finite p-adic extension, supplied compatible topology, and natural
rank, including zero. The field and inducing carrier universes are independent.
For the exact irreducible cuspidal inducing hypotheses, it proves finite length
over the actual complex group algebra and supplies an actual composition series
with at most `Nat.factorial B.length` irreducible factors.

The induction is the published normalized smooth induction: inflation through
the upper-parabolic Levi projection, the canonical positive half-modulus twist,
and the right-translation action on smooth covariant functions. Its functor
object is definitionally the representation in the target. Its carrier universe
is `max uF uV`, so the proof applies `jacquetDetectingFamilyLength` at universes
`uF, max uF uV`.

The private `associatedLengthBound` evaluates the published
`associatedJacquetFiltration` at the inducing representation. The actual
successive quotients are equivalent to whole-Levi transports of the inducing
representation. Surjectivity of the Levi conjugation isomorphism preserves
irreducibility under this transport, and representation equivalence transfers
irreducibility to each actual quotient. The exhaustive indexing equivalence
identifies the number of factors with the cardinality of
`MinimalConjugatingPermutations`. This gives a composition series for each
associated Jacquet module, retaining multiplicities.

The public helper `cuspidalInductionSubquotientJacquet` records the detection
step independently of the length argument. For arbitrary smooth quasicuspidal
inducing data and any nonzero smooth subquotient of their normalized induction,
it produces an associated block Levi whose actual normalized Jacquet module
of the subquotient is nonzero and quasicuspidal. Apply `minimalNonzeroJacquet`
to the subquotient. The theorem `normalizedJacquetSubquotient` makes its
Jacquet module an actual subquotient of the corresponding Jacquet module of
the induction. If the chosen Levi were nonassociated, the published
`nonassociatedJacquetSubquotients` would make that quasicuspidal object zero,
contradicting its nontriviality. This helper requires neither irreducibility
nor admissibility of the inducing data, and no finite-length premise.

For the final theorem, take the finite family of all block shapes associated
with the inducing shape. Bound each associated Jacquet module by its minimal
conjugating count using `associatedLengthBound`, and detect every nonzero
subquotient using the public helper. The published theorem
`jacquetDetectingFamilyLength` gives finite group-algebra length and an actual
composition series bounded by the sum of these counts. Its proof uses exactness
of normalized Jacquet modules to make a bounded natural-number measure strictly
increase along every strict chain of invariant subspaces; the generic length
criterion then constructs the composition series.

The private `countBound` increases the sum to the sum over all block shapes,
identifies that sum with the cardinality of the dependent sum of minimal
conjugating permutations, and applies `totalConjugatingCount`. The resulting
cardinality is `B.length!`. Transitivity of the numerical inequality changes the
bound on the same actual composition series.

This is an internal assembly of published proofs following Bernstein and
Zelevinsky, *Induced representations of reductive p-adic groups I* (1977),
Theorem 2.8, printed pp.447–448/PDF8–9, and its proof in section 2.14,
printed p.449/PDF10. The detection helper preserves the Levi-association
conclusion of section 2.14(1); the finite detecting-family argument implements
section 2.14(2), using Corollary 2.13(b),(c). Registered source:
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The original section 2.14 was read directly. The concrete filtration,
finite-family and cardinality bookkeeping are internal deductions from the
named published results.

All geometric prerequisites are applied as proved Library theorems. There is no
extra theorem-valued premise, rank positivity assumption, or dimension
assumption on the ambient representation. The proof does not use induction
association, general preservation of finite length, or finite-type induction.
The target's Lean/Markdown pair and all imported pairs are unchanged.
