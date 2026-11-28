# Reduction of induced progenerator independence to a maximal Levi

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VI.10.1 (printed p.207 / PDF p.213), reduces the comparison of induced
progenerators to maximal Levis using transitivity of normalized induction from VI.1.4.
The registered source is `renard-2026-representations-groupes-reductifs-padiques`, with
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The module implements this reduction for actual rational parabolics using a rank-one gallery.

`InducedProgeneratorMaximalOppositeStatement` asserts the comparison for an opposite pair
with a common embedded Levi, the first parabolic being maximal proper. The inducing object
on both sides is `rationalNormKernelSummandInduction M ρ₀`, where `ρ₀` is irreducible and
embeds in the restriction of an irreducible supercuspidal `π` to `⁰M(F)`.
The field, point topologies and representation universes are those of
`InducedProgeneratorIndependenceStatement`.

For a pair with the same embedded Levi, the centralizer of the split component of the
Levi is the Levi itself. Both parabolic images intersect that centralizer in the full Levi
image. Thus `rationalParabolicGalleryAvoiding` gives a gallery, from which the proof retains
the rank-one walls. At each wall, the two parabolics lie in an outer parabolic and meet its
Levi in opposite parabolics of relative rank one. The proof takes their unipotent radicals
and applies `leviParabolicTransitivity` on each side. Applying the outer induction functor
to the maximal opposite comparison yields the isomorphism across the wall. The invariant
along the gallery records a presentation of the current parabolic range whose induction
of the fixed inducing object is isomorphic to the starting induction. At the endpoint,
`leviInductionIsoOfRangeEq` compares the presentation in the invariant with the specified
parabolic.

`inducedProgeneratorIndependence_of_maximalOpposite` pulls the second parabolic back by
conjugation by `g⁻¹` and uses `φ` to present its Levi with source `M`. Its Levi embedding
then agrees with that of the first parabolic, so the gallery compares their inductions of
the same object. The isomorphism `leviInductionIsoOfConj` transports the result forward by
`g` and gives the required pullback of the inducing object along `φ⁻¹`.
