# Actual division orders and twists of formal modules

The namespace `Langlands.FormalGroup.LocalDivision` connects the actual
integer order in a central division algebra with the formal order actions
in `ModuleLaw.OrderAction`. It constructs the conjugation used in
Drinfeld's action on his moduli problem and the resulting formal-module
twists.

## Source and provenance

Drinfeld, *Coverings of p-adic symmetric regions* (1976), section 2 A,
printed p.109 (PDF page 3), defines a formal `O_D`-module as a formal
`O`-module with an extending `O_D`-action. In the formula for the
`GL(d,K) × Dˣ`-action on triples, the twisted module has order action
`a ↦ ρ(g⁻¹ag)`. The same paragraph states triviality of the action of
integer-order units on the moduli classes.
The registered original is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

This file is a derived construction. Its integer ring and central scalar
map reuse `CentralDivision.localReducedNormValuation` and
`localDivisionIntegerMap`. The conjugation proofs use the multiplicative
valuation, centrality of `K`, and the unit equations. The formal twist
uses the actual endomorphism ring of formal coordinate maps. The
integer-unit isomorphism is one ingredient in Drinfeld's assertion about
moduli classes; the assertion for the complete framed triple is not
proved here.

## Hypotheses and the actual integer order

`K` is a topological nonarchimedean local field with its valuative
relation. `D` is a finite-dimensional central division `K`-algebra.
These constructions apply to every such `D`; no Hasse invariant is
specified.

`IntegerRing K D` is the integer subring
`(localReducedNormValuation K D).integer`, whose elements are actual
elements of `D` with valuation at most one. Its `𝒪[K]`-algebra structure
uses `localDivisionIntegerMap`, and its centrality proof is
`Algebra.commutes`. `coe_algebraMap` identifies the underlying scalar
with the original `K`-algebra map into `D`.

`value_conjugate` proves that the valuation of `g⁻¹ag` equals the
valuation of `a` for every `g : Dˣ`. It expands multiplicativity,
commutes the valuation factors in their commutative value monoid, and
cancels the factors of `g` and `g⁻¹`.

With `K` equipped locally with `LocalGalois.localNormedField`,
`integerRing_eq_levelIntegerRing` identifies this subring with
`Shimura.LocalDivision.integerRing K D`, the integer ring used by the
published division-level definitions. The proof is subring
extensionality and `localDivisionNorm_le_one_iff`. This is an equality
of the underlying subrings; no level or congruence subgroup is
redefined.

## Conjugation and coefficient extension

`conjugation K D g` is an actual `𝒪[K]`-algebra automorphism of
`IntegerRing K D` with formula `a ↦ g⁻¹ag`; its inverse has formula
`a ↦ gag⁻¹`. The valuation identity proves both maps preserve the
integer ring. Distributivity proves additivity, cancellation proves
multiplicativity and the inverse identities, and centrality proves
that the automorphism fixes integral scalars.

`conjugation_one` gives the identity automorphism.
`conjugation_mul` states
`conjugation (g*h) = (conjugation g).trans (conjugation h)`;
`AlgEquiv.trans` applies its left argument first, so this is the
inverse-conjugation convention. `conjugation_scalar` proves that units
from the central field act trivially by conjugation.

For a finite-coordinate formal `𝒪[K]`-module `M` over a commutative
`𝒪[K]`-algebra `R`, and an actual order action `E` on `M`,
`twist K D E g` has the same underlying `M` and action
`a ↦ E.action (conjugation K D g a)`. The extending scalar action is
inherited from `OrderAction.twist`. `twist_map` proves that extending
coefficients along any `𝒪[K]`-algebra homomorphism commutes with this
twist; both sides have the same defining endomorphisms.

## Integer-unit isomorphism

`integerUnit` maps a unit of the actual integer order into `Dˣ`.
`conjugation_integerUnit` identifies its order automorphism with the
same unit multiplication inside the integer ring.

For `u : (IntegerRing K D)ˣ`, `twistUnitIso K D E u` is an actual
order-linear formal isomorphism
`E ≅ twist K D E (integerUnit K D u)`. Its forward map is
`E.action u⁻¹` and its inverse map is `E.action u`.
Forward equivariance is the identity
`u⁻¹*a = (u⁻¹*a*u)*u⁻¹`; reverse equivariance is
`u*(u⁻¹*a*u) = a*u`. Applying the action ring homomorphism proves
these equations in the actual formal endomorphism ring. The two
inverse identities follow from the two unit identities. The
`twistUnitIso_hom` and `twistUnitIso_inv` lemmas expose the two maps.

This contribution imposes no special tangent or height condition.
It supplies no construction of a framing object, no general-base
gluing, no group action on framed moduli classes and no
representability assertion.
