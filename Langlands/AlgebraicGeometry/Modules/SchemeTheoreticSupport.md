# Scheme-theoretic support and proper support

This module constructs the scheme-theoretic support of a quasi-coherent module
sheaf `M` on an arbitrary scheme `X : Scheme.{u}` whose sections on every affine
open are finite modules. The hypothesis is the existing
`HasFiniteAffineSections M`; it requires no noetherian, quasi-compactness,
reducedness, or nonemptiness assumption on `X`. Local finite presentation is a
stronger finiteness condition supplied separately by the coherent-family
construction.

## Original sources and scope

The original definition is Stacks Project, Section 29.5, Lemma 29.5.4(1)
(Tag 05JU) and Definition 29.5.5 (Tag 05JV), in the retained source
`stacks-scheme-theoretic-support-056h-2026-11-01`, file
`Stacks Project- Supports of modules (Section 29.5, Tag 056H).html`.
The cited lemma characterizes the support on each affine open `Spec A` by
`Spec (A / Ann_A M)`. Its proof reduces construction to commutation of finite
module annihilators with localization. The implementation follows exactly that
affine characterization. The source also proves existence and uniqueness of a
module on the support with direct image `M`; that additional module construction
is not asserted or implemented in this file.

For the application, see Stacks Project Situation 99.5.1 and the use of
scheme-theoretic support in Lemma 99.5.4, retained source
`stacks-coherent-sheaf-stack-08ka-2026-11-01`, file `08KA.html`. This module
supplies the support condition for the scheme specialization when the ambient
morphism is proper. The coherent-family groupoid, relative flatness, finite
presentation, pullback restrictions and pseudofunctor are separate units.

## Definitions and affine characterization

All names below are in `Langlands.AlgebraicGeometry.Modules`.

* `annihilatorIdealSheaf M hM` is Mathlib's `X.IdealSheafData`, with affine
  component exactly `Module.annihilator Γ(X,U) Γ(M,U)`. This is compatible with
  restriction to basic opens, so Mathlib constructs its actual closed subscheme.
  Mathlib's ideal-sheaf interface records affine ideals and localization data;
  it is not an independently implemented subsheaf of the structure sheaf.
* `schemeTheoreticSupport M hM` is that actual closed subscheme, and
  `schemeTheoreticSupportι M hM` is its closed immersion into `X`.
* `ker_schemeTheoreticSupportι_app` identifies the kernel on every affine open
  with the actual annihilator. `schemeTheoreticSupportObjIso` identifies the ring
  of sections over the inverse image of that affine open with the quotient by
  the annihilator. `ker_schemeTheoreticSupportι` gives the ideal-sheaf equality.
* `IsSchemeTheoreticSupport M ι` expresses the source's affine characterization:
  `ι` is a closed immersion, and every affine section-ring map has kernel the
  annihilator of the corresponding module of sections.
  `isSchemeTheoreticSupport_schemeTheoreticSupportι` verifies this property for
  the constructed support. `isSchemeTheoreticSupport_iff_ker_eq` identifies it
  with equality to the annihilator ideal sheaf for a closed immersion.
* `schemeTheoreticSupportIso` gives an actual isomorphism from any such `ι` to
  the constructed support, commuting with the immersions into `X` in both
  directions. Thus this interface retains the scheme structure specified in
  Lemma 29.5.4(1), including its nilpotents.

`range_schemeTheoreticSupportι` identifies the range with the closed support of
the annihilator ideal sheaf, and `isClosed_range_schemeTheoreticSupportι` proves
closedness. This file does not additionally identify this set with a separately
defined stalk-support predicate.

`le_annihilatorIdealSheaf_iff` proves that the annihilator is the largest ideal
sheaf acting by zero on every affine section module.
`schemeTheoreticSupportLift` supplies the resulting morphism from the support to
any closed subscheme whose kernel ideal acts by zero on those modules, and its
composition with the immersion is the support immersion. Such a morphism is
unique because a closed immersion is a monomorphism.

## Properness and all test schemes

`HasProperSupport M f hM` means precisely that
`schemeTheoreticSupportι M hM ≫ f` is proper. `hasProperSupport_iff` proves its
equivalence to properness for any closed subscheme satisfying
`IsSchemeTheoreticSupport`. `hasProperSupport_iff_exists` expresses the same
condition by existence of such a proper closed subscheme. These equivalences
justify using the constructed support in the source's proper-support condition.

`hasProperSupport_of_isProper` proves the condition for every proper ambient
morphism `f`. `hasProperSupport_relativeSpace` specializes this result to
`Picard.relativeSpace f` and `Picard.relativeProjection f` for every object
`T : Over S`. The theorem uses only properness of `f`, quasi-coherence of `M`,
and `HasFiniteAffineSections M`; ambient flatness and local finite presentation
are not needed for this support argument. In particular, the test scheme may be
nonnoetherian, nonreduced, empty, or non-quasi-compact.

## Implemented proof route

The generic lemma `map_annihilator_of_isLocalizedModule` proves that finite
module annihilators commute with arbitrary localization. One inclusion uses
surjectivity up to denominators and invertibility of denominator actions. For
the reverse inclusion, choose finite generators, clear a denominator on each
generator, and multiply these denominators to obtain a single element of the
localizing monoid that kills every generator. The span criterion then shows
that the resulting scalar lies in the original annihilator.

Applying this to the published quasi-coherent basic-open restriction map gives
`annihilatorIdealSheaf`. The scheme, affine quotient isomorphisms, kernel and
closed-immersion facts use Mathlib's ideal-sheaf subscheme construction. Equality
of kernels gives the comparison isomorphism via the universal property of
closed immersions. Properness follows from the properness of a closed immersion,
composition of proper morphisms, and stability of properness under arbitrary
base change. These are intrinsic proofs supporting the definitions unit.
