# Support filtrations for compact induction and closed-subgroup Mackey data

This module constructs support filtrations for compact induction from arbitrary
algebraic covariance representations, together with the geometric data and
representation functors for the closed-subgroup specialization of
Bernstein--Zelevinsky's geometric lemma. It does not assert a graded-piece
isomorphism.

Mathlib's `Rep.resFunctor` composes representation actions with a group
homomorphism and keeps the underlying intertwining linear maps. Its
equivariance and functor laws are reused.

`rawRestrictedCompactInduction P Q` takes any algebraic representation of `P`,
constructs its existing compact induction to `G`, and restricts that action to
`Q`. The inducing representation need not be smooth: the induction constructor
already selects smooth vectors of the right translation action. This permits
the support construction to apply to the covariance representation used for
closed semidirect triples without assuming smoothness of that covariance
representation or continuity of a chosen decomposition.

`restrictedCompactInduction P Q` is the smooth-input specialization, obtained by
precomposition with the existing full-subcategory inclusion. It uses
`Langlands.Induction.SmoothRep`, the existing transparent full subcategory alias,
rather than defining another smooth-representation category.
The source carrier universe is independent of the group and coefficient
universes. The induced functions have universe `max uG uV`.

Following BZ's choice of a representative `w` with `P w^-1` in the orbit,
`orbitStabilizer P Q w` is the actual subgroup of elements `q` of `Q` for
which `w^-1 q w` belongs to `P`. `stabilizerToInducing` is that conjugation
homomorphism with codomain restricted to `P`. Its group laws and value
formula are proved.

`orbitPiece P Q w` pulls the original representation back along this
homomorphism and then compactly induces from that subgroup to `Q`. Both
the carrier and maps come from the published induction construction.
Induction uses left covariance and right translation, with compact actual
nonzero support in the left quotient.

`cosetOrbit P Q w` is the range of `q -> P w^-1 q` in the actual topological
quotient `P \ G`. Its invariance under right multiplication by elements of `Q`
is proved.
`OrderedDoubleCosets` specifies representatives of a disjoint finite cover by
these actual orbits and requires every initial union to be open.
The initial unions, monotonicity, invariance and empty/full endpoint formulas
are implemented. Existence of this ordering is not a structure field or an
asserted theorem.

`rawSupportSubfunctor` is the actual subrepresentation of compactly induced
functions whose nonzero support projects into a specified invariant subset
of `P \ G`. Closure under addition and scalar multiplication follows from
support containment. Invariance under `Q` uses inverse translation of the
support. An intertwiner acts by postcomposition, which cannot enlarge
support; this proves that these are natural subfunctors. All these arguments
apply to arbitrary algebraic covariance representations. `supportSubfunctor`
restricts this construction to smooth inputs with the same underlying spaces
and maps.

`OrderedDoubleCosets.rawSupportFiltration` uses the successive initial orbit
unions. Its monotonicity is proved by containment, its zero endpoint by
pointwise vanishing, and its full endpoint by the orbit cover.
Thus the filtration itself is constructed rather than postulated.
`OrderedDoubleCosets.supportFiltration` restricts it to smooth inputs. The
existing smooth-input declaration types, support subspaces and order are
retained, and the raw and smooth versions share the same implementation.
The substantive Mackey assertion identifying its successive quotients with
`orbitPiece` remains a separate proposition definition and proof obligation.

The definitions use arbitrary commutative coefficients and topological
groups. They do not require closedness or local compactness merely to
construct these objects. The corresponding sourced theorem will explicitly
require complex coefficients, smooth inputs, closed subgroups, the locally
profinite Hausdorff hypotheses and countability at infinity.

## Source and scope

Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), sections 1.1-1.2, 1.7-1.8 and 5.1-5.3, printed pages
442-445 and 459-461; PDF pages 3-6 and 20-22.
The original text was read, and the formulas and ordering condition on
printed page 460 were visually inspected.

For the closed-subgroup Mackey data, the specialization sets both groups `U`
and `V` to the trivial
group, takes `M=P` and `N=Q`, and uses trivial localization characters.
Localization becomes restriction; both modular correction factors equal
one. The stabilizer and conjugation above are precisely the resulting
`N' = w(P) intersect Q` and inverse conjugation into `P`.
This is the ordinary closed-subgroup Mackey-filtration special case, not the
full normalized parabolic geometric lemma 2.12.

The raw support extension is a derived construction prerequisite for the
general section 5.3 construction before localization. Its broader algebraic
input domain is justified by the implemented support and pointwise-map
arguments, which do not use smoothness of the covariance representation.
It does not extend the sourced Mackey assertion to arbitrary nonsmooth inputs.
Actual normalized covariance, character localization, preservation of
intersections and sums after localization, and graded-piece identifications
remain separate constructions or theorem obligations.

Literature ID: `bernstein-zelevinsky-1977-induced-i`.
Retained original SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.

The construction imports the Library's
`Langlands.Representation.Induction.Definitions` and the natural
filtration interface `Langlands.Representation.Filtration.Definitions`.
Both are published Library imports. The filtration pair retains
its independently reviewed source bytes. Mathlib's group homomorphisms,
subgroup comaps, restriction functor and full-subcategory functors are reused.
No theorem truth is an input field.

Author: Worker 14.
