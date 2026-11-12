# Semistandard Langlands conjugacy for GL_n

Author: Worker 1155.

`Langlands.glSemistandardLanglandsConjugacy` proves exactly
`Langlands.GLSemistandardLanglandsConjugacyStatement.{uF,uV,uW,uJ,uK}`.
The field, two inducing carriers, and two quotient carriers have five
independent universes. The proof reuses the closed whole-Levi recovery theorem
and its tensor-recovery dependency by Lean name. Neither is an assumed premise.

The proof follows the standardization and standard-data comparison route
of Silberger 1978, Corollary 6.2, printed p.103. The complete ten-page
original was read; the semistandard definition on p.95, the normalization
on p.96, and Proposition 6.1 and Corollary 6.2 on pp.102–103 were checked
in the page images. The registered source is
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
The published source-scope audit of Lemma 5.3 was also read. The present
assembly does not use that lemma's unsupported unrestricted wording.

Write `c = P.conjugator`. The published
`glSemistandardStandardization` applies to the actual inclusion
`P.splitComponent ≤ A₀` and constructs a permutation `w` and a coordinate
Levi element `m` satisfying

```text
y * c = P.shape.leviEmbedding F.Carrier m,
y = GeneralLinear.permutation n F.Carrier w.
```

Its determinant and matrix-entry proof retains the original ordered shape.
The coordinate equivalence is then the actual continuous inner equivalence
`e = T.innerLeviEquiv P.shape m`. Its inverse pulls back `σ` to `σ₀`.
The published `innerPullbackEquiv` preserves irreducibility, and
`isLeviTempered_inner_iff` preserves the exact analytic tempered predicate,
including its all-Haar full-center formulation. No tensor presentation or
temperedness certificate is supplied by the premises.

`innerLeviInducedEquiv` transports the same real determinant twist through
this inner pullback and then through actual normalized induction.
`conjugateParabolicInducedEquiv` is the published left-translation
equivalence from standard induction in the original coordinates to the
actual conjugate induction. Composing these equivalences with the supplied
surjection to `J` constructs a genuine surjection from the standard twisted
induction of `σ₀`. Right translation, positive half-modulus covariance and
the residue-normalized positive real determinant twist are retained.

The closed `glWholeLeviLanglandsRecovery` compares this map with the
supplied standard quotient map to `K` and their given equivalence. It yields
literal equality of the ordered shapes, equality of the real vectors after
the specified dependent transport, and an actual equivalence from the
untwisted `σ₀` to `τ`. Eliminating those equalities leaves the original
coordinate inner equivalence with precisely the required target type.

The published `PairConjugation` standardizer lemmas give equality of the
actual parabolic, split component and embedded Levi under conjugation by
`y`. `permutation_mem_singletonSplitComponent_normalizer` puts that exact
permutation matrix in the normalizer of `A₀`. Finally,
`innerLeviEquiv_embedding_of_standardizer` gives the pointwise ambient
embedding formula, and `leviRealPowerCharacter_comp_innerLeviEquiv` gives
equality of the transported characters.

The proof constructs a pure permutation representative directly, so no
arbitrary representative is chosen in this assembly. The supporting
`NormalizerPermutationTransport` construction additionally factors every
diagonal-torus normalizer element as a diagonal matrix times a permutation.
Its `exists_permutation_transport_of_normalizer` combines that factorization
with the published `RepresentativeReplacement` construction. Removal of the
target diagonal factor preserves the actual pair, coordinate embedding,
character and untwisted representation conclusions, using its explicit
inclusion in the standard Levi and the inner representation equivalence.
The same adjusted coordinates preserve analytic temperedness and actual
normalized induction by the published inner transport lemmas. This supporting
unit is published separately from this proof.
The separately proved `leviRealPowerCharacter_blockScalar_injective` and
`leviRealPowerCharacter_injective` establish the faithfulness of the character
formulation: a uniformizer in scalar block `i` evaluates to
`q ^ (-(B.size i : ℝ) * t i)`, and `q > 1` and positivity of every block size
recover every real coordinate. These proofs retain the full central direction.

No nontrivial-rank or multiple-block condition is added. Positive total rank,
arbitrary ordered positive block shapes, strict chambers and the one-block
case remain exactly as stated. The proof uses neither final ordered
classification nor semistandard conjugacy as an input.
