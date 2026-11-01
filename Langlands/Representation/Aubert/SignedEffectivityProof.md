# Common-sign Aubert effectivity

Authors: Worker 164 and Worker 194.

`Langlands.Aubert.signedEffectivity` proves exactly
`SignedEffectivityStatement.{uF,uV} F T`. For an irreducible quasicuspidal
representation `σ` of a standard Levi of shape `B`, every actual irreducible
subquotient `π` of its normalized parabolic induction has coefficientwise
effective image under

```text
factorMap (((-1 : ℤ) ^ (n - B.length)) • alternatingOperator F T n [π]).
```

The sign depends only on the inducing shape `B`. The theorem has no further
premise. The field and representation universes remain independent, and the
representations use the saturated carrier `Type (max uF uV)`. Arbitrary primes,
supplied p-adic fields and topologies, rank zero and the empty Levi are included.

The proof is an internal assembly of the actual corrected cut complex and its
proved support, geometric, signed comparison, finite lifting, detection and
Euler results. The following describes those results as used by the implemented
Lean proof; no assertion of exactness of a complex ending in zero is needed.

At positive rank the surviving degree is `m = B.length - 1`. The theorem first
uses `quasicuspidal_subquotient_hasJacquetBlockBound` to prove that the actual
normalized Jacquet carrier of `π` at any shape with more than `B.length`
blocks is zero. Every Levi `C` associated to `B` has `C.length = B.length`, by
`LevisAssociated.length_eq`. The same block bound therefore holds with target
shape `C`. This is the only representation-theoretic bound supplied to the
concrete graded-concentration results.

The underlying complex is `ActualCutComplex`: a degree `k` is the finite
product of the actual normalized induction--Jacquet terms at cut sets of
cardinality `k`. At positive rank their shapes have length `k+1`. The maps
are the existing actual `Transition.cutMap` intertwiners, formed from the
normalized induction and Jacquet constructions. Their identity and composition
laws give an inclusion diagram. Its homogeneous differential inserts a cut
with coefficient `(-1)^#{j in s | j < i}`. Thus its square-zero law is the
proved exterior insertion law, with the original upper-block conventions,
positive induction half-modulus, inverse Jacquet half-modulus and right
translation retained.

For each associated target Levi `C`, the actual homogeneous Jacquet diagram
is filtered using the finite support chain in `LengthOrderedSupports`. This
chain is the sequence of prefixes of an exhaustive permutation list sorted by
decreasing inversion length. It starts at the empty set, ends at all
permutations, and adds exactly one permutation at each step. Both the upper
support `θ` and the lower support `θ \ {w}` in such a step are upward closed
under strict inversion length. Equal lengths may occur in either order.

The actual Bruhat support at a source shape is the two-sided core
`weylSupport`: the largest subset of `θ` invariant under the left target
block Weyl subgroup and right source block Weyl subgroup. The corrected
support modules are actual images in normalized Jacquet modules.
`CorrectedJacquetCutFiltration` proves that the actual cut maps preserve
these images, that the empty and full endpoints are zero and whole, and
that the homogeneous support grades are the corresponding quotient diagrams.
`CorrectedJacquetQuotientComparison` identifies their maps with the actual
bundled quotient maps. `BundledJacquetQuotientDiagram` transports this
identification to homogeneous degrees and their signed differentials. These
are comparisons of the actual maps, including their exterior signs.

`WholeTargetGradedConcentration` proves the needed lower exactness of every
singleton grade under the target block bound just obtained. Inactive core
steps vanish. In active steps the length criterion gives an increasing
minimal representative. A proper target intersection forces strictly more
flattened source blocks than target blocks, so the block bound kills its
actual Jacquet coefficient and hence the graded quotient. For a whole target
intersection, the active source cuts form the concrete Boolean interval
between the permutation descents and the allowed inverse edge cuts.
All actual intersection refinements in this interval flatten to one common
shape, chosen at the smallest active cut set. Its actual Jacquet module of
`π` is the common coefficient.

The equivalence with this common-coefficient interval is the actual coherent
orbit integral, whole-target evaluation, and flattened Jacquet quotient
comparison. `WholeTargetSignedComparison` proves its all-class naturality
square for the actual cut maps. The generic diagram equivalence preserves
every signed insertion coefficient, including maps at the interval boundary.
The Boolean interval contraction is injective in degree zero when the target
degree is positive and exact at middle degrees strictly below
`C.length - 1`. If the fixed inverse-permutation conditions for the interval
fail, every graded carrier is zero, which gives the same lower conclusions.
Consequently the two concrete theorems
`bundledSupportQuotient_injective_before_target` and
`bundledSupportQuotient_exact_below_target` supply every clause of
`UpperSingletonGradedConcentrationBelow T π C m`.

The theorem's `hgraded` is precisely this construction, transporting the degree
by associated-Levi length equality. `LengthFilteredJacquetConcentration`
lifts graded injectivity and middle exactness through the actual finite
exhaustive support filtration. Its finite lifting uses the actual square-zero
differential and quotient comparisons; it adds no geometric hypothesis.
For the upper vanishing clause, `quasicuspidal_degreesVanishAboveSupport`
uses the same block bound to make every actual term, and hence every degree,
above `m` zero. Its normalized Jacquet carrier is zero as a quotient of a
zero carrier. `jacquetDegree_subsingleton_iff` transfers this to the actual
coordinate Jacquet diagram, giving the theorem's `hzero`.

`jacquetConcentratedAt_of_upperSingletonGraded` now yields the existing
associated-Levi Jacquet concentration condition. The final call to
`effective_of_associatedJacquet` uses finite length from irreducibility for
`σ` and `π`. Internally, `QuasicuspidalCutSupport.degreesDetected` detects
every nonzero actual subquotient of every cut degree using Levis associated
to `B`. Its proof obtains the constituent support from the actual geometric
filtration and exact Grothendieck classes. Actual Jacquet injectivity,
middle-exactness and zero reflection therefore give concentration of the
original cut complex at `m`.

The finite-length Euler identity then identifies the common signed Aubert
class with the class of the actual terminal quotient of degree `m` by the
incoming differential. When `m = 0` this is degree zero itself. Positive rank
gives `m+1 = B.length` and `B.length ≤ n`, so its sign is exactly
`(-1)^(n - B.length)`. No vanishing, irreducibility or nonvanishing of this
terminal quotient is asserted. The class of any actual finite-length object
has effective composition-factor vector. All calculations take place in the
published exact finite-length Grothendieck group and retain actual short
exact relations, including nonsplit ones.

The branch `n = 0` applies `effective_rankZero`. There the unadjusted Aubert
operator is the identity and `0 - B.length = 0`, so the required expression is
the composition-factor vector of `π` itself. This handles the empty Levi
without using positive-rank cut indexing.

The proof does not use an Aubert irreducible-image or irreducibility-preservation
conclusion, analytic segment classification, multisegment exhaustion, ordered
strong-head existence, quotient coverage, tempered block uniqueness,
square-integrable classification or exhaustion, or regular exhaustion.
It does not treat the original Aubert Proposition 3.2, the original Theorem 3.6
argument, or its erratum alone as an established proof. No admissibility,
central-character, finite vector-space dimension, classification or positivity
premise is introduced. The target statement and all pairs it imports are
unchanged. Worker 164 supplies the final assembly and the actual support,
signed and finite-lifting adapters; Worker 194 supplies the concrete geometric
interval, vanishing, coefficient and graded-concentration constructions.
