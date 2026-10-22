# Smooth and compact induction

Worker 15's construction pair for task `16a1cb4a-52bf-40f8-b8f1-c3ca35146f4a`
implements smooth induction, compact induction, maps on intertwiners, and
normalization by an actual smooth scalar character. The namespace is
`Langlands.Induction`. The functor definitions contain proved identity,
composition and smoothness obligations; these conclusions are not input fields.

The coefficient ring is any commutative ring. The group has a topology with
continuous multiplication and inversion. The coefficient module has an
independent universe, no topology, and no dimension restriction. The subgroup
is an actual `Subgroup G`; the construction needs no openness,
normality, closedness, local compactness or Hausdorff hypothesis. These broader
hypotheses are validated by the construction fields. The input representation
need not already be smooth. The complex case is included.

The coefficient, group and module universes are independent. Functions on `G`
with values in `V` have universe `max uG uV`; accordingly, the induction functors
take `Rep.{uV} R P` to `SmoothRep.{uR, uG, max uG uV} R G`. The bundled map
constructors also allow source and target modules in different universes.

Mathlib's `Representation.ind` is algebraic tensor-coinvariant induction;
it is not used for smooth or compact induction here. The audited
`Representation.coindV`, `coind`, and `coindMap` already provide precisely
the covariant functions `f(p*g) = sigma(p)(f(g))`, right translation
`(g*f)(x) = f(x*g)`, and postcomposition by equivariant linear maps.
The source files are `Mathlib/RepresentationTheory/Induced.lean` and
`Mathlib/RepresentationTheory/Coinduced.lean`, in pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Smooth induction is the accepted smooth-part construction applied to this
coinduced representation. Each whole function has a single open subgroup
fixing it on the right; pointwise local constancy alone is not the definition.
The output functor lands in the full subcategory of `Rep` consisting of smooth
representations, with its smoothness certificate proved from the fixing subgroup.
Functor maps retain postcomposition and the identity and composition fields
are proved by extensionality.

`SmoothFunctions` is the actual submodule carrier and `smoothInduced` its
right-translation representation. `smoothFunctionOf` constructs an element
from covariance and a single uniform open right stabilizer. `eval` returns the
underlying value. `smoothInducedMap` postcomposes using Mathlib's `coindMap`
followed by the accepted `smoothMap`. `smoothInductionFunctor` supplies
the smoothness property for each constructed object.
`Langlands.Induction.SmoothRep` transparently reuses the canonical
`Langlands.SmoothRep` from
[`Representation/Category/Basic`](../Category/Basic.md).
Unfolding `smoothRepProperty` gives exactly the former full subcategory of
`Rep.{uV} R G` cut out by `IsSmooth`. Both names have independent coefficient,
group and carrier universes, explicit arguments `R G`, and precisely the
`CommRing R`, `Group G`, `TopologicalSpace G` instances. The category alias
does not require continuity of the group operations; the induction
constructions retain their existing `IsTopologicalGroup G` hypothesis.
All category instances and morphisms are inherited through the same type.

The compatibility migration retains the following public names and imports:

| Existing name or module | Canonical name or retained interface |
| --- | --- |
| `Langlands.Induction.SmoothRep.{uR,uG,uV} R G` | `Langlands.SmoothRep.{uR,uG,uV} R G`, a transparent alias |
| `Langlands.Representation.Induction.Definitions` | Retained; now imports `Langlands.Representation.Category.Basic` |
| `Langlands.Representation.Category.Basic` | Retained canonical category module |
| The four induction functors and their map constructors | Retained with their original types and formulas |

[`CategoryCompatibility`](CategoryCompatibility.md) contains direct Lean
checks of the complete alias telescope, the former type expression, inherited
instances, and the four functors with their morphism interfaces. These are
intrinsic definitional checks. Worker 15 made this consolidation using
Worker 23's canonical category; the original induction construction remains
Worker 15's work. The source references below continue to describe the same
mathematical constructions.

The support condition uses the quotient topology on `P \ G`, implemented by
`Quotient (QuotientGroup.rightRel P)`. Its equivalence relation is
`x ~ y` iff `y*x^-1` belongs to `P`. It is not a quotient group unless `P`
is normal. Compact induction requires the projected actual nonzero support
to be compact. This does not replace compact support by finite support, even
when the subgroup is closed and not open. Covariance makes nonzero support
saturated under `P`, and the uniform open stabilizer makes the function
locally constant. Thus projected support is closed in the quotient topology.
This closedness is the reason support contained in a compact set is compact;
it verifies the addition and scalar closure fields without a Hausdorff assumption.

More precisely, `preimage_quotientSupport` proves that covariance makes the
support saturated under `P`. `eval_locallyConstant` uses the neighborhoods
`x*K` from the uniform stabilizer. The open zero fiber gives closed support,
and the quotient topology transfers closedness to projected support.
For addition, the new support is a closed subset of the compact union of
the two old supports; scalar multiplication only shrinks support.

`compactFunctions` is the resulting actual submodule, and `CompactFunctions`
is its carrier. Right translation by `g` sends projected support into its
image under the continuous quotient map induced by right multiplication
by `g^-1`. The translated support is closed and that image is compact.
This proves the stability field of `compactSubrepresentation`, whose
restricted action is `compactInduced`. Smoothness follows by restricting the
fixing subgroup of the underlying smooth function.

Postcomposition cannot create a nonzero value at a zero of the original
function. The same closed-subset argument therefore defines `compactInducedMap`.
`compactInductionFunctor` includes the proved smoothness, identity and
composition fields. `compactFunctionOf` is the explicit constructor, and
`compactInclusion` is the canonical equivariant inclusion into smooth induction.
Because projected support is closed, its compactness is equivalent to its
containment in a compact subset.

The conventions follow Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), section 1.8(a), printed page 444, PDF page 5:
the covariance condition, single open right stabilizer, right translation, and
compact support modulo the inducing subgroup. That original page was read.
The arbitrary-ring and arbitrary-topological-group scope is an internal
generalization justified by the actual construction fields, rather than an
assertion of their exactness or reciprocity theorems under weaker hypotheses.
Retained source ID: `bernstein-zelevinsky-1977-induced-i`; content SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

`SmoothCharacter R H` contains an actual homomorphism `H ->* R^units` and a
proof that its kernel is open in the given topology. No topology on `R` is
required. `SmoothCharacter.toSmoothRep` uses the accepted
`characterRepresentation` and proves its smoothness with that open kernel.

`SmoothCharacter.twistFunctor` uses the accepted `Langlands.twist` and
`twistIntertwining`, with identity and composition fields proved directly.
`normalizedSmoothInduced` and `normalizedCompactInduced` apply the preceding
constructions to `twist chi sigma`, so their covariance is
`f(p*x) = (chi(p) : R) • sigma(p)(f(x))`. The normalized induction functors
are composites of this actual twist functor and the corresponding induction
functor. Their right-translation and quotient-support conventions are unchanged.
For parabolic induction the caller supplies the genuine smooth half-modulus
character from its GL geometry.

Casselman, Chapter III, revision April 29, 2019, section 1,
page 1, gives `f(pg)=delta_P(p)^(1/2)*sigma(p)f(g)` and right translation.
The original source pages 1–3 were read. No assertion of admissibility,
unitarity, reciprocity, or exactness is intended in this construction pair.
Retained source ID: `casselman-2019-jacquet-module`; content SHA-256:
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.

Project dependencies are imported by their current Lean module names:

- `Langlands.Representation.Category.Basic` supplies the canonical category.
- `Langlands.Representation.Smooth.SmoothPart.Definitions` supplies
  `smoothVectors`, `smoothPart` and `smoothMap`, using the smooth predicates
  from `Langlands.Representation.Smooth.Definitions`.
- `Langlands.Representation.Twist.Definitions` supplies `twist`,
  `twistIntertwining` and `characterRepresentation`.

The compatibility consolidation starts from Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`. It retains all constructions and
the existing induction structural and Jacquet reciprocity statement sources.
It was compiled in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
version 1, which pins the same Lean 4.34.0 and Mathlib commit as the
environment named below.

Prepared environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d`, version 1,
Lean 4.34.0. The original construction's native compilation and private
interface checks succeeded. Those checks verify covariance, the direction of right translation,
postcomposition formulas, the uniform stabilizer, actual compact projected
support, normalized scalar factor and all four returned smoothness certificates
at independent universes. Inspected construction axiom closures contain only
`propext`, `Classical.choice` and `Quot.sound`. These development checks are
distinct from independent semantic acceptance and publication.
