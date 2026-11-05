# Finite coefficient models of supplied group-scheme homomorphisms

This is an internal construction derived from the published finite coefficient
scheme-map descent, flat-source generic-fibre injectivity, and spreading of
closed immersions. All rings, fields and schemes lie in the arbitrary common
universe `u`. It uses actual group objects, actual pullback functors, and the
published `Descent.pullbackComparison` isomorphisms.

`homModel G H f` chooses a `HomModel` of the supplied generic homomorphism `f`
for group schemes over the spectrum of a commutative domain `R` with fraction
field `K`. More generally, its construction only needs a commutative `R` and
its specified fraction-field structure. The source structural map is flat,
quasi-compact and quasi-separated. The target structural map is separated and
locally of finite presentation. The data contain a finitely generated
`R`-subalgebra `T` of the same field `K`, an actual homomorphism between the
pullbacks of `G` and `H` to `Spec T`, and the equality recovering `f` after
pullback to `Spec K` and the direct/iterated comparisons. It does not replace
the supplied homomorphism by an isomorphic but unidentified one.

The auxiliary `exists_fg_hom` first applies the published
`exists_fg_subalgebra_hom_pullback_of_hom_pullback_of_locallyOfFinitePresentation`
to the underlying scheme map. The comparison inverse followed by the iterated
pullback projection is an eligible finite-stage projection in that theorem.
The published inverse-comparison projection identity checks its first
projection, and the private second-projection lemma checks its base map.
Cancelling the comparison isomorphisms and using pullback uniqueness gives an
equality between the generic pullback of the descended scheme map and the
conjugate of the supplied group homomorphism.

`isMonHom_of_generic` recovers the group-homomorphism property of that scheme
map. The tensor unit and the square of a flat source are flat; the target is
separated. The published `AbelianScheme.genericFibre_map_injective` is stated
for an arbitrary domain, independently of the later discrete-valuation
hypothesis in its module. Its injectivity on these two sources, together with
`AbelianScheme.isMonHom_of_map`, recovers the unit and multiplication equations.
The finitely generated subalgebra is a domain with the same fraction field,
using Mathlib's actual subalgebra instance. This justifies this step without
assuming faithful flatness of the generic-point inclusion. `Grp.homMk` then
supplies the actual descended group-scheme homomorphism.

The separate auxiliary `exists_fg_closed_baseChange` starts with a homomorphism
between affine group schemes over `Spec R`, with source locally of finite
type, whose actual pullback to `K` is a closed immersion. It finds a finitely
generated `R`-subalgebra `T` of `K` where the actual pullback is closed. This
lemma does not need the fraction-field hypothesis. Maps between the affine
schemes are quasi-compact and quasi-separated. Local finite type of the source
structural map implies local finite type of the homomorphism. The published
`IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map` then
applies. Its universal quantification over compatible pullback maps is handled
by pullback uniqueness, both over `K` and over `T`.

These constructions do not yet choose a finite S-integer base or simultaneous
integral models. They do not assert reductive, parabolic, or connected fibre
properties. Those remain obligations of the full spreading target.
