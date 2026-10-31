# Identity and composition of finite rational chart sheaf direct image

Author: Worker 56.

This module is an internal categorical consequence of the concrete rational
chart pullback comparisons and the continuous finite rational site functor.
It constructs comparisons for the actual direct-image functors, with no
sheafification assumption or limit hypothesis on the coefficient category.

Work in the namespace
`Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart`.
Fix a complete ultrametric normed field `K`, presented affinoid algebras
`A,B,C,D`, and a coefficient category `E`. The field, coefficient objects and
coefficient morphisms have independent universes `u,v,w`. Charts have arbitrary
finite positive-radius rational presentations with explicit unit generation.
Their arrows are actual bounded quotient-algebra maps over the base algebra,
in the direction opposite to the corresponding spectrum maps.

Write `P(φ)` for `coefficientSheafPushforward φ E`. A bounded map `φ : A → B`
gives `P(φ) : Sheaf(B) → Sheaf(A)` on the finite rational chart topologies.
Its underlying presheaf is restriction along the opposite of
`pullbackFunctor φ`.

`coefficientSheafPushforwardIdIso A E` is the natural isomorphism
`P(id_A) ≅ identity`. It applies Mathlib's
`Functor.sheafPushforwardContinuousId'` to `pullbackIdNatIso A`. The latter
has actual bounded representative maps in both directions as components.
On a sheaf `F` and a chart `d`, the forward section map is
`F.obj.map (pullbackIdIso d).inv.op`, and the inverse is
`F.obj.map (pullbackIdIso d).hom.op`. The two component lemmas state these
formulas explicitly.

For arbitrary bounded maps `φ : A → B` and `ψ : B → C`,
`coefficientSheafPushforwardCompIso φ ψ E` is the natural isomorphism
`P(ψ) ⋙ P(φ) ≅ P(ψ.comp φ)`. It applies
`Functor.sheafPushforwardContinuousComp'` to the inverse of
`pullbackCompNatIso φ ψ`, whose original direction is from direct chart
pullback to iterated chart pullback. On a sheaf `F` over `C` and a chart `d`
over `A`, its forward section map is
`F.obj.map (pullbackCompIso φ ψ d).hom.op`, and its inverse uses the inverse
chart arrow. This orientation accounts for the contravariance of presheaves.
Both component formulas are proved from the Mathlib construction.

The source-identity equation identifies the composite comparison for
`id_A,φ` with the identity comparison evaluated on `P(φ)(F)`. The
target-identity equation identifies the comparison for `φ,id_B` with
`P(φ)` applied to the identity comparison on `F`. The associativity equation
identifies the two morphisms from `P(φ)(P(ψ)(P(χ)(F)))` to direct image
along the composite of three bounded maps: first combine `φ,ψ`, then
`ψ.comp φ,χ`; or first combine `ψ,χ` under `P(φ)`, then `φ,χ.comp ψ`.
These are equalities of sheaf morphisms for every `F`. Extensionality reduces
them to section maps. Functoriality combines successive section maps, and
the proved uniqueness of actual chart restrictions equates the resulting
chart arrows. No uniqueness of maps in `E` is used or assumed.

The original geometric context is Berkovich, *Non-Archimedean analytic spaces*,
Trieste lectures (2009), registered as
`berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
Printed/PDF p.8, Definition 2.1.11, gives bounded algebra maps and their
opposite affinoid-space direction. Page 9, Definition 2.2.1 and
Exercise 2.2.2(ii)-(iii), supplies positive-radius rational quotients and
intersections. Page 10, Fact 2.2.3(i) and the finite-cover discussion before
Fact 2.2.6, gives the local spectrum and covering context. The G-topology
paragraph after Fact 3.2.4 on p.15 uses general analytic domains and quasinets.
These passages were read directly in developing the imported constructions;
no source-specific errata file is supplied. The sheaf comparisons and their
coherence equations here are internally derived using Mathlib's
`CategoryTheory/Sites/Continuous.lean`, rather than numbered assertions of
the original source.

The finite rational topology uses finite point-covering families equipped
with actual restriction arrows. This module does not identify it with the
full analytic G-topology, prove descent for the quotient-algebra presheaf,
or construct analytic atlases, etale or equivariant sites. The explicit
algebraic unit-generation condition is retained without claiming its
equivalence to the source's absence of common spectral zeros.
