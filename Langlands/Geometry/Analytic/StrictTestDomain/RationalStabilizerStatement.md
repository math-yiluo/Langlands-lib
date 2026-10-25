# Open setwise stabilizers of rational loci

Author: Worker 36.

`RationalLocusStabilizerOpenStatement` is a proposition definition about
the existing actual presented strict affinoid algebras, their bounded
spectra, and their unit-radius rational loci. This file states a target;
it does not provide its Lean proof.

Let `K` be an ultrametric normed field, `P` a
`PresentedStrictAffinoidAlgebra K`, `G` a topological group, and
`ρ : G →* Aut P` a homomorphism into the automorphism group of the
category of bounded `K`-algebra maps. Assume that for every `a : P`,
the map

```text
G → P,   g ↦ (ρ g).hom(a)
```

is continuous in the norm topology on `P`. For every `d : RationalData K P`,
the target asserts that the following subset of `G` is open:

```text
{g | ((x ↦ (ρ g) • x) '' d.locus) = d.locus}.
```

Here `d` consists of a finite tuple of numerators `f_j`, a denominator
`b`, and the condition that these elements have no common zero on the
actual spectrum. Its locus is the subset of points `x` satisfying
`x(f_j) ≤ x(b)` for every index `j`. The spectrum action is the
existing left action by inverse pullback:
`((ρ g) • x)(a) = x((ρ g).inv(a))`. Thus the displayed set is the
setwise stabilizer of the actual subset, allowing different chosen
rational presentations to describe the same subset. Equality of
presentations and fixation of individual spectrum points are not
part of the target. The published `RationalAutomorphism.locus_smul`
also identifies the image in the conclusion with `(ρ g • d).locus`.

The field and group occupy independent universes. There is no
completeness assumption on `K`, no nontrivial-valuation or nonzero-algebra
assumption, and no nonemptiness assumption on the spectrum or the locus.
Empty numerator tuples are allowed. The hypothesis supplies no common
operator bound and requires no topology on `Aut P` or local compactness
of `G`.

This is an internally derived local criterion. A proposed proof route
uses compactness of the closed rational locus. Its denominator is
nonzero at every point of the locus, by the no-common-zero condition
and the rational inequalities. For a nonempty locus, compactness gives
a positive uniform lower bound on the denominator seminorm. Continuity
of the finitely many algebra-element orbits near the identity then
makes their perturbations smaller than this bound. The normalized
spectrum bound and the nonarchimedean triangle inequality preserve
the rational inequalities. Applying the estimates to both an operator
and its inverse gives equality of loci near the identity. The group
action laws then yield openness of the whole stabilizer. The empty
locus case is immediate. This paragraph describes a route for the
separate proof task, not a proof supplied by this module.

The source for the rational inequalities and the no-common-zero
condition is Berkovich, *Non-archimedean analytic spaces*, Trieste
lectures (2009), printed/PDF p. 9, Exercise 2.2.2(ii), specialized to
unit radii and to the Library's presented algebras. The bounded
spectrum and its evaluation topology are in Definitions 1.2.3 and
1.2.5, printed/PDF p. 4; Exercise 1.2.4 gives the normalized bound,
and Fact 1.2.6 supplies the compactness context. The registered source
is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
The source's analytic setting has a complete coefficient field;
the target deliberately uses the weaker hypotheses sufficient for
this statement about the Library's actual normed algebras and spectra.

Berkovich's unfinished *Etale equivariant sheaves on p-adic analytic
spaces* (1995-1996), section 1.1, printed/PDF pp. 1-2, motivates
the target. Its topology on analytic automorphisms uses preservation
of finitely many compact analytic domains together with bounds on
analytic functions. The present target supplies only the setwise
stabilizer condition for the specified rational loci under the
explicit algebra-orbit hypothesis. It does not construct that
automorphism topology, continuity of transported local sections, a
full analytic `G`-space, or an equivariant etale site. It also does
not assert a rational-domain universal property against arbitrary
affinoid tests.

The registered source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
receipt SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
