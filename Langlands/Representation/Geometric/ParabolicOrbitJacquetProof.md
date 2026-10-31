# Natural normalized parabolic orbit comparison

`Langlands.Geometric.padicParabolicOrbitJacquetComparison.{uF,uV}` proves
exactly the published proposition
`Langlands.Geometric.PadicParabolicOrbitJacquetComparison.{uF,uV}`.
The field and representation universes are independent. The closing theorem
retains every prime, actual finite p-adic extension, supplied compatible
topological data, positive rank, pair of block shapes, minimal representative,
source and target refinements, and both full triples of intersection equalities.
Its natural isomorphism is on the entire category of smooth complex
source-Levi representations and all their intertwining maps.

The implementation is a derived assembly of the actual orbit integral,
normalization cancellation and refined induction transport. It imports the
original statement and preserves that Lean/Markdown pair and its imports.
No additional comparison, measure-scaling, surjectivity, admissibility,
finite-dimensionality or finite-length premise is imposed.

For fixed supplied data,
`Langlands.PadicField.TopologicalData.parabolicOrbitJacquetComparison` first
installs the topology, local-field and local-compactness structures from `T`.
It invokes `parabolicOrbitCompactComparison_exists` once. That theorem chooses
genuine compatible quotient measures before quantifying over representations,
and returns a family `E` together with naturality for all source intertwiners.
The source of `E A` is the actual target-parabolic radical coinvariants of
compact induction from the orbit stabilizer, with inverse-conjugated source
covariance and the positive source half modulus. Its target is compact induction
from the actual stages quotient subgroup of the integrated coefficient.
The underlying comparison is the quotient integral of the nested coefficient
class of the original function at `n * s(l)`. Its equivariance uses the proved
actual radical-to-correction Haar ratio; its bijectivity follows from the proved
split-stages comparison. The measure choice is part of the construction, rather
than an extra hypothesis on the result.

Each component of the final isomorphism is the composite

```
twistEquiv inverseTargetHalf (E A)
  followed by parabolicOrbitInductionTransportEquiv ... A.representation.
```

The first map applies the same inverse target half modulus to the source and
target of `E A`, retaining its underlying linear equivalence. Its source is
therefore exactly the published `parabolicOrbitJacquetFunctor` object.
The second map moves this character inside compact induction, uses compactness
of the actual refined-parabolic quotient to pass through the canonical inclusion
to smooth induction, applies the normalized nested coefficient equivalence,
and relabels the inducing subgroup as the supplied refined parabolic.
The coefficient equivalence uses both full intersection-refinement hypotheses:
the positive source factors, radical-to-correction Haar ratio and inverse target
half multiply to exactly the positive refined target half. The remaining
coefficient is normalized refined source Jacquet, transported by actual inverse
intersection-Levi conjugation and inflated along the refined Levi projection.
Consequently the component has no residual character.

Before bundling these components, `geometricPieceFunctor_eq_pullback` rewrites
the literal published geometric-piece functor using the actual subgroup
identifications. This equality identifies the component's target with exactly
`geometricPieceFunctor T B C w.val S R hS.2.1 hR.2.1`.
`Rep.mkIso` bundles each representation equivalence and `NatIso.ofComponents`
assembles the natural isomorphism. For an arbitrary original source intertwiner,
extensionality reduces naturality to equality on each vector. Applying the
induction transport to the compact comparison's naturality equality and then
composing with `parabolicOrbitInductionTransportEquiv_natural` proves this
identity. The target morphism is precisely normalized refined induction of
inverse-intersection transport of the normalized refined Jacquet map. Thus the
construction is simultaneous and natural over the full source category.

The unapplied closing theorem introduces the published proposition's complete
parameter list, including positive rank, and applies this fixed-data result.
It proves the exact two-universe target without modifying its definition.
The auxiliary fixed-data theorem also works in rank zero; the closing theorem
retains the target's positive-rank hypothesis.

The mathematical source is Bernstein–Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Sections 5.4–5.17 (printed pp.461–467) provide the local orbit comparison and its
measure-dependent quotient integral; section 6.4 (printed pp.468–469) cancels
the normalizing correction character. The implemented proof uses the published
concrete GL subgroup, integral, coefficient and induction results to assemble
that normalized comparison. It does not assert the separate support-quotient
Mackey comparison, a global filtration, or existence of standard intersection
refinements.
