# Actual irreducible Aubert images up to sign

Authors: Worker 76, with Worker 585's actual composition-factor and
realization argument.

`Langlands.Aubert.irreducibleImage.{uF,uV} F T` proves exactly the published
`Langlands.Aubert.IrreducibleImageStatement.{uF,uV} F T`. Every actual
irreducible smooth complex representation `π` of `GL_n(F)` has an actual
irreducible smooth representation `πD` of that same group such that the
existing unadjusted Aubert operator satisfies `D[π] = [πD]` or
`D[π] = -[πD]`.

The proof is internal assembly of two published results. It applies
[`irreducibleImage_of_signedEffectivity`](IrreducibleImageFromEffectivity.md)
to [`signedEffectivity`](SignedEffectivityProof.md), with the independent
universe parameters supplied explicitly to both. The former result retains
common-sign effectivity as an explicit premise; the latter proves precisely
that premise without an irreducible-image input. The final theorem therefore
has no additional premise.

The reduction works as follows. Rank zero uses the published identity formula
for the actual unadjusted Aubert operator and takes `πD = π`. At positive
rank, `CuspidalSupport.normalizedQuasicuspidalEmbedding` embeds `π` into an
actual normalized induced representation `M = i_B σ`, with `σ` actual,
irreducible and quasicuspidal on the Levi of a block shape `B`. Irreducibility
gives finite length of `σ`, and the actual normalized induction preserves
finite length. The published quasicuspidal eigenvalue identity gives
`D[M] = s[M]`, where `s = (-1 : ℤ)^(n - B.length)`. Since `s² = 1`,
the endomorphism `s • D` fixes `[M]`. Published involutivity makes `D`,
and hence `s • D`, injective.

The signed-effectivity theorem supplies coefficientwise nonnegativity of
`factorMap (s • D[C])` for every actual irreducible subquotient `C` of `M`,
with this same `s`. In the lattice of genuine irreducible isomorphism
classes, the composition-factor vector of `M` is effective, has natural
integral multiplicities, and is fixed by the transported `s • D`. An actual
injective embedding puts the label of `π` in its support.

The adapter
`IrreducibleOperator.exists_irreducible_image_of_embedding_in_effective_fixed_class`
now applies. Its finite-length counting argument expands the fixed vector
as a positive integral combination of supported generators. Each image
column is effective and nonzero by injectivity, so its total multiplicity
is at least one. The fixed-vector equality forces the weighted sum of
these multiplicities to equal the original total multiplicity. Each column
therefore has total multiplicity one and is a single genuine irreducible
generator. The published realization theorem chooses an actual irreducible
smooth representative for the image of `π`; removing `s = ±1` gives the
required disjunction. Finite length of the input and output follows from
their irreducibility, exactly as in the target statement.

The effectivity input uses the actual corrected cut complex, as detailed in
its paired proof Markdown. Its degree `k` is the finite product of actual
normalized induction--Jacquet terms indexed by cut sets of cardinality `k`.
The transition maps are the actual `Transition.cutMap` intertwiners, with
signed insertion coefficient `(-1)^#{j in s | j < i}`. Their proved
composition laws give the square-zero differential.

For each Levi associated to `B`, the Jacquet complex is filtered by a finite
exhaustive chain of supports ordered by decreasing permutation inversion
length. At each source shape the support is the largest subset invariant
under both the left target and right source block Weyl subgroups. The
published quotient comparisons identify the actual induced maps on the
successive grades. Inactive grades vanish; proper target intersections
vanish by the Jacquet block bound from quasicuspidality. Whole target
intersections give a concrete Boolean interval with one common actual
flattened Jacquet coefficient. The orbit integral, whole-target evaluation,
flattened quotient comparison and their all-class naturality squares
identify its differential with the signed insertion differential.

The Boolean interval contraction proves injectivity and middle exactness
strictly below the surviving degree `m = B.length - 1`. Finite filtration
lifting transfers these conclusions to the actual Jacquet complex; actual
terms above `m` vanish. Associated-Levi detection of every nonzero
subquotient reflects this concentration to the original cut complex.
The finite-length Euler argument retains its actual terminal quotient:
degree `m` modulo the incoming image, or degree zero itself when `m = 0`.
Its class is `s • D[C]`; the composition-factor vector of this actual
finite-length object is effective. Neither terminal irreducibility nor
nonvanishing is needed for this input. The separate fixed-vector argument
above supplies the actual irreducible conclusion.

All groups and classes are the existing exact finite-length Grothendieck
groups, retaining all actual short exact relations, including nonsplit
ones. The actual upper-block functors, positive induction half-modulus,
inverse Jacquet half-modulus and right translation are unchanged. Arbitrary
primes, supplied p-adic fields and topologies, independent `uF,uV`, saturated
carriers `Type (max uF uV)`, and rank zero are retained.

The provenance is the imported published Lean proofs and constructions.
Workers 164 and 194 proved the corrected support and effectivity input;
the present module assembles that theorem with the published reduction.
The original assertions and corrections are documented in the unchanged
[`IrreducibleImageStatement`](IrreducibleImageStatement.md). No original
Aubert Proposition 3.2, defective Theorem 3.6 proof, erratum alone, or
exactness of a full complex ending in zero is assumed. No analytic segment
classification, multisegment exhaustion, ordered strong-head existence,
quotient coverage, tempered block uniqueness, square-integrable
classification or exhaustion, regular exhaustion, or proof depending on
those conclusions enters this route. No admissibility, central-character,
finite vector-space dimension, positivity or preservation premise is added.
The target pair and every pair it imports remain unchanged.
