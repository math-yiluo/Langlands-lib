# Conjugation transport of rational spectral tests

Author: Worker 36.

This module constructs transport of the published rational spectral tests by
actual bounded algebra automorphisms, and proves that their subgroups transform
by conjugation. It works over a fixed ultrametric normed field `K` and an actual
presented strict affinoid algebra `P`. The quotient-section constructions require
`CompleteSpace K`; the locus-stabilizer construction does not.

For `g : Aut P` and rational data `d`, the existing action sends `d` to the
presentation obtained by applying the forward algebra map `g.hom` to its inputs.
The spectrum action uses inverse pullback. The published `locus_smul` identifies
the moved locus with the image of the original locus under this point action.
`stabilizerConj g d` therefore constructs a multiplicative equivalence

```text
locusStabilizer d ≃* locusStabilizer (g • d),
h ↦ g * h * g⁻¹.
```

Its underlying map and the exact conjugate-subgroup equality are proved using
Mathlib's stabilizer transport for a group action on sets. These are setwise
stabilizers: individual points and the chosen rational presentation need not be
fixed.

Write `C_g` for the actual bounded rational comparison
`d.comparison g.hom : d.algebra → (g • d).algebra`, and write `S_d(h)` for the
published `stabilizerSectionMap d h`. The theorem
`stabilizerSectionMap_comparison` proves the equality of bounded algebra maps

```text
S_(g • d)(g * h * g⁻¹) ∘ C_g = C_g ∘ S_d(h).
```

The Lean proof applies the rational quotient's `hom_ext`: it suffices to compare
the maps after the base map from `P`. Both the comparison and the fixed-section
map have published base-map equations. After substituting these equations,
the base automorphism identity `g.inv(g.hom(a)) = a` proves the result.
The displayed conjugate is packaged as `stabilizerConj g d h` in the typed Lean
statement.

`spectralBound_comparison_iff` proves that `C_g(b)` has universal spectral bound
`r` exactly when `b` does, for every real `r`. The comparison is the forward map
of the already constructed `comparisonIso` for the bounded equivalence induced
by `g`. Bounded maps preserve spectral bounds by spectrum pullback. Applying
this fact to the inverse comparison proves reflection. No equality with the
quotient norm, norm-isometry assertion, or operator-bound assumption is used.
Universal inequalities also cover an empty spectrum without a nonemptiness
hypothesis.

`RationalSpectralTest.transport g t` moves the actual domain and quotient
section of `t` by these constructions and retains its positive radius. The
intrinsic laws show that `g * h * g⁻¹` satisfies the transported test if and only
if `h` satisfies the original test. On the locus stabilizer, this follows by
subtracting the transported section in the intertwining equation and applying
spectral-bound reflection. The ambient membership proof then carries the
setwise-stabilizer witness through `stabilizerConj`. In particular,
`RationalSpectralTest.subgroup_transport` states the exact equality

```text
H(transport g t) = (H(t)).map (MulAut.conj g).toMonoidHom,
```

where `H(t)` denotes the published `rationalSpectralSubgroup` with the test's
domain, element and radius.

`finiteRationalSpectralSubgroup_transport` proves the same equality for finite
families of tests. Its proof expands membership in the intersection and applies
the individual membership equivalence at each index. This includes the empty
family, whose subgroup is the whole group; it does not use a nonempty-index
lemma for images of intersections. The finite index universe is independent
of the field universe.

The construction is derived infrastructure for the tests of Berkovich's
unfinished *Etale equivariant sheaves on p-adic analytic spaces* (1995–1996),
section 1.1, printed/PDF pp. 1–2. That passage specifies finite compact-domain
and spectral-function tests with positive tolerances and non-strict bounds,
and asserts that the corresponding automorphism group is topological. The
present module supplies the conjugation law for the Library's restricted
unit-radius rational tests. Its proof route uses the Library's already
constructed quotient comparisons and fixed-section action; the source passage
does not state these particular Lean constructions. The underlying actual
strict affinoid quotients, bounded maps and rational algebras follow Berkovich's
*Non-archimedean analytic spaces*, Trieste lectures (2009), section 2.1 and
Definition 2.1.2 on p. 7, Definition 2.1.11 on p. 8, and Definition 2.2.1 and
Exercise 2.2.2(ii) on p. 9.

All automorphisms are `K`-linear, over a fixed base algebra, and all tested
sections belong to constructed unit-radius rational quotients. Trivial
valuations, nilpotents, zero quotients, empty rational loci and zero numerator
arity are not excluded. The forward section convention and inverse-pullback
spectrum convention are the published ones; the source's opposite pullback
convention gives the same test subgroups by closure under inversion. This
module defines no topology and claims no identification with the full analytic
automorphism topology. Arbitrary analytic domains, continuity of section
orbits, openness in another topology, structure sheaves and equivariant etale
sites remain separate obligations.

The registered Equish source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
receipt SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The Trieste source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
