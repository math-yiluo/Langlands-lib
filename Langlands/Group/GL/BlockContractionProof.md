# Uniform block-scalar contraction on actual p-adic radicals

Author: Worker 92.

The theorem `Langlands.GeneralLinear.BlockShape.blockContraction.{uF}` proves
exactly the published proposition
`Langlands.GeneralLinear.BlockShape.BlockContractionStatement.{uF}` from
`Langlands.Group.GL.BlockContractionStatement`. It has no additional premises.
The field universe remains arbitrary. The prime, primality instance, field,
supplied topological data, rank, and block shape are all universally quantified
by that proposition. All imported Library Lean/Markdown pairs remain unchanged.

The public component theorems in the same namespace are
`deepChamberNonempty`, `uniformCompactBlockContraction`, and
`strictPowersEventuallyDeep`. Their types are the respective existing
`DeepChamberNonempty B T`, `UniformCompactBlockContraction B T`, and
`StrictPowersEventuallyDeep B T` propositions. The final theorem combines them
in the published order.

## Scalar powers and nonempty chambers

The proof first establishes eventual deepness. For each ordered block pair
`i < j`, the real value of `B.blockScalarRatio T i j a` is nonnegative and
strictly less than one. Its natural powers tend to zero. The homomorphism law
for the ratio identifies these powers with the ratios of the pointwise powered
tuple. Two finite conjunctions combine all ordered pairs into one eventual
statement. The natural-number `atTop` characterization gives a threshold
valid for every subsequent exponent. Pairs with `i ≥ j` impose no condition.

For chamber nonemptiness, the proof uses the published uniformizer of `T`.
Its additive order is one, so it is nonzero. Its normalized absolute value is
`q⁻¹ < 1`, where `q = T.residueCardinality > 1`. Regard it as a unit `t` and
set `a i = t ^ (B.length - i.val)`. If `i < j`, cancellation gives
`a i * (a j)⁻¹ = t ^ (j.val - i.val)`. Since the exponent is at least one,
its normalized absolute value is at most that of `t`, hence below one.
The already-proved strict-power theorem now supplies a tuple at every given
positive depth. The construction and finite conjunctions also cover empty
and one-block shapes without a nonemptiness assumption.

## Uniformity on compact subsets

The proof of `uniformCompactBlockContraction` rewrites the supplied topology
using the published equality `T.topology_eq_canonicalNormTopology`. This is
a proved equality for this exact `T`, used internally to perform metric
estimates; the theorem's type remains the original supplied-topology
proposition. Put `d = [F : Q_p] > 0`. The published comparison identifies the
normalized absolute value of each field element with its canonical norm to
the natural power `d`.

Four private helpers implement the finite-coordinate argument:

* `norm_nhds_one` uses the embedding of matrix units into the product of their
  matrix and inverse-matrix coordinates. From an arbitrary identity
  neighborhood `U`, it obtains `δ > 0` such that both matrix distances to the
  identity being below `δ` imply membership in `U`. It extracts a metric ball
  in that product and uses its maximum metric. It requires no openness of `U`.
* `compact_matrix_bound` uses continuity of both coordinate maps to bound
  their norms on a compact set. Taking a maximum with one gives a strictly
  positive common bound, including when the compact set is empty.
* `upper_conj_norm_bound` proves a bound below `η M` for the difference from
  the identity of the forward upper conjugate, assuming every forward scalar
  ratio has norm below `η` and the original matrix has norm at most `M`.
* `lower_conj_norm_bound` proves the same estimate for inverse conjugation
  of the opposite radical. Its lower `(i,j)` entry has ratio `a_i⁻¹ a_j`,
  which equals the forward ratio `a_j a_i⁻¹` for `j < i`.

The last two helpers use the elementwise supremum norm on matrices. They
reindex every standard coordinate by `B.indexEquiv`. Radical preservation
and the published intrinsic radical descriptions make the diagonal-block
differences and the forbidden-direction blocks zero. Each remaining entry
is its original entry times the appropriate ratio. Its norm is at most the
ratio norm times `M`, which is strictly below `η M` since `M > 0`.
The supremum norm characterization combines all entry inequalities, including
rank zero.

Apply the compact bound to `Cplus ∪ Cminus`, obtaining `M > 0` for the
matrices and inverse matrices of all its elements. Set
`η = δ / M` and `ε = min 1 (η ^ d)`. Thus `0 < ε ≤ 1`. For **every**
ε-deep tuple, the normalized ratio inequalities and the positive-degree
comparison imply that all forward ratio norms are below `η`. The two
coordinate estimates put the required conjugates within `δ` of the identity.
They also apply to the inverses of the original radical elements: each radical
is a subgroup, and the compact bound already controls these inverse matrices.
The inverse of a conjugate is the corresponding conjugate of the inverse.
Consequently both unit-topology coordinates satisfy the neighborhood bound.

The same ε is chosen before the arbitrary tuple and works for both compact
sets. There is no restriction on a common central scalar, no selected
contraction sequence, and no Iwahori factorization, representation, or
Haar-scaling premise. The proof controls inverse coordinates directly; it
does not infer convergence in the unit topology from matrix entries alone.

## Open-subgroup consequence

`strictPowers_eventually_mem_iwahori` quantifies over any open subgroup `K`
for exactly `T.topology`, any strictly contracting tuple `a`, and elements
`x` and `y` of the upper and opposite radicals. It provides `r : ℕ` such that
for every `s ≥ r`, writing `aGL = B.blockScalar F.Carrier a`,

* `aGL^s * x * (aGL^s)⁻¹` belongs to
  `B.iwahoriUpper F.Carrier K.toSubgroup`;
* `(aGL^s)⁻¹ * y * aGL^s` belongs to
  `B.iwahoriLower F.Carrier K.toSubgroup`.

The proof applies uniform compact contraction to `{x}` and `{y}` and to
the identity neighborhood underlying `K`, then applies eventual deepness.
The homomorphism power law for `blockScalar` identifies the pointwise scalar
powers with the ambient group powers. Published radical-preservation lemmas
supply the second membership in each intersection. Neither compactness nor
factorization of `K` is assumed.

## Provenance and validation boundary

This is a derived concrete `GL_n` geometry proof of the published target,
not a translation of a numbered compact-uniformity theorem in the literature.
Its motivating source is Bill Casselman, *Introduction to admissible
representations of p-adic groups*, Chapter III, *Induced representations and
the Jacquet module*, revision April 29, 2019, sections 4–6, printed/PDF pages
5–8. The registered source is `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
The retained PDF is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Chapter III - Induced representations and the Jacquet module--2019.pdf`.
These pages were read for this proof; no source-specific project errata file
was found. Section 4 supplies the two conjugation orientations, III.5.4
motivates eventual strict powers, and III.6.2 motivates all sufficiently deep
chamber elements. The published matrix conjugation formulas determine the
orientations because PDF text extraction can omit opposite-radical overbars.
The scalar, compactness, and neighborhood arguments above describe the
implemented Lean proof.

The closing theorem and complete module pass Lean-service compilation with
zero errors or warnings. Inspection reports universe parameter `uF` and only
`propext`, `Classical.choice`, and `Quot.sound`. Independent semantic review,
official exact-target validation, and publication are separate submission
requirements.
