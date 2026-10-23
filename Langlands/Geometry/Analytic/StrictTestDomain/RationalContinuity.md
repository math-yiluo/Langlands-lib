# Continuity of base change on finite rational sites

Author: Worker 36.

Let K be a complete ultrametric normed field in universe u, let P and Q be
presented strict affinoid algebras, and let φ : P → Q be an actual bounded
K-algebra homomorphism. Write F for the existing `pullbackFunctor φ` from
`RationalData K P` to `RationalData K Q`. The categories retain the chosen
unit-radius rational presentations; morphisms are inclusions of their actual
multiplicative-seminorm loci. The algebras underlying these presentations are
the constructed closed-ideal quotients of finite strict Tate algebras.

The module constructs the induced functor on sheaves for the existing
`finiteRationalTopology`, by proving the necessary compatibility property
from explicit intersections. The topology consists of sieves containing
finite families whose loci cover the target locus. It is not identified here
with the full analytic G-topology.

`locus_pullback_whole` proves that the inverse image of the whole-spectrum
presentation has locus the whole spectrum of Q. It rewrites the existing
inverse-image locus formula and `locus_whole`. Thus `toPullbackWhole φ d`
is the actual inclusion of any rational locus over Q into that inverse
image. `pullbackWholeIsTerminal` uses these arrows as the unique maps into
the image of the whole-spectrum object. This construction, including
`locus_pullback_whole`, does not require completeness of K.

For two rational presentations d and e, `locus_pullback_inter` proves

    locus(F(d ∩ e)) = locus(F(d)) ∩ locus(F(e)).

Here d ∩ e denotes the previously constructed `inter d e`, with the product
denominator and the pairwise products of the denominator-extended numerator
tuples. The proof uses `locus_inter` and preservation of intersections by
set-theoretic inverse image under the actual spectrum map M(Q) → M(P).
`pullbackInterLift φ f g` uses this equality to construct an inclusion
c → F(d ∩ e) from inclusions f : c → F(d) and g : c → F(e).

`pullbackInterIso d e φ` is an isomorphism

    F(d ∩ e) ≅ F(d) ∩ F(e)

in the inclusion category over Q. Its forward arrow is the existing
intersection lift of the pulled-back projections. Its inverse is
`pullbackInterLift` applied to the projections over Q. The two inverse laws
follow from the subsingleton property of all hom sets. This is an isomorphism
of chosen rational data; it does not assert equality of their presentations.

For any inclusions f : d → t and g : e → t, `pullbackMapConeIsLimit`
constructs a limiting cone for the image under F of the explicit
`pullbackCone f g`. Its lift is exactly `pullbackInterLift`, and its
factorization and uniqueness laws follow from thinness. The instances
`pullbackFunctor_preservesTerminal` and `pullbackFunctor_preservesPullback`
then use Mathlib's `preservesLimit_of_preserves_limit_cone` to preserve every
limit cone for the respective empty diagram and cospan. The helpers
`isLimitMapConeEmptyConeEquiv` and `PullbackCone.isLimitMapConeEquiv` convert
the explicit image objects and cones into the required generic cone types.
These limits and their preservation concern the fixed-base inclusion
categories, not limits in the ambient category of all affinoid spaces.

`pullbackFunctor_compatiblePreserving` proves Mathlib's
`CompatiblePreserving` for Type-valued sheaves in any universe w. Let x be a
compatible family over a presieve T on a rational presentation Z over P.
For members g₁ : Y₁ → Z and g₂ : Y₂ → Z of T, compatibility gives equality
of their sections after restriction to Y₁ ∩ Y₂. The projection square
commutes because the category is thin. If an arbitrary rational presentation
X over Q maps to both F(Y₁) and F(Y₂), `pullbackInterLift` constructs its
map l to F(Y₁ ∩ Y₂). Apply the sheaf's restriction along l to that equality.
Functoriality identifies the resulting composites with the original maps
from X; thinness proves the two arrow equalities used in this identification.
This proves the compatibility condition on every such X. The argument does
not need a gluing assumption on the presheaf, although the Mathlib interface
quantifies over sheaves.

`pullbackFunctor_isContinuous` combines this compatibility proof with
`pullbackFunctor_coverPreserving` from `RationalBaseChange`, using
`Functor.isContinuous_of_coverPreserving`. It establishes exactly
Mathlib's `Functor.IsContinuous` for the two finite rational topologies.
Thus precomposition with F.op preserves sheaves.

Finally, `rationalSheafPushforward φ A` constructs

    Sheaf (finiteRationalTopology K Q) A
      ⥤ Sheaf (finiteRationalTopology K P) A

using `Functor.sheafPushforwardContinuous`. The coefficient category
A : Type v with morphisms in universe w is arbitrary; no completeness or
existence of limits in A is assumed. On a sheaf ℱ, the underlying presheaf
is F.op followed by ℱ. At d it has value ℱ(F(d)); its restriction along an
inclusion is ℱ's restriction along the pulled-back inclusion. On a morphism
of sheaves it acts by the corresponding precomposition. No sheafification,
inverse-image adjoint or geometric-morphism adjunction is asserted.

Empty finite covers, empty numerator tuples, empty rational loci, zero or
nonreduced quotient algebras and trivial scalar valuations remain allowed.
The intersection and topology constructions use the existing completeness
assumption on K. No surjectivity assumption on M(Q) → M(P) is introduced.
All radii are one and all representation results used in the imported
construction test presented strict affinoids only. The module neither
constructs a structure sheaf nor proves Tate acyclicity, subcanonicity,
atlas gluing or an etale site.

This is a derived construction based on Berkovich, *Non-archimedean analytic
spaces*, Trieste lectures (2009), Definition 2.1.11 on printed/PDF p. 8,
Definition 2.2.1 and Exercise 2.2.2(ii)–(iii) on p. 9, the finite-affinoid-cover
paragraph preceding Fact 2.2.6 on p. 10, and the analytic G-topology paragraph
following Fact 3.2.4 on p. 15. The registered original is
`berkovich-2009-trieste-analytic-spaces`, SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
These passages supply the opposite bounded-algebra direction, the domain
and rational-domain context, closure under intersections and the covering
context. The explicit fixed-base limits, continuity criterion application
and functor on sheaves are derived categorical consequences, not quotations
of a theorem in those passages. Mathlib supplies the generic categorical
criterion; the present module proves its compatibility hypothesis and uses
the previously proved finite-cover preservation. The source's arbitrary
positive radii, all-affinoid tests and quasinet G-topology remain broader
than the construction formalized here.
