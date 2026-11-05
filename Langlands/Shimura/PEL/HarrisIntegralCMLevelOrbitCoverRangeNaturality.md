# Naturality of the exact orbit-cover level range

This internal unit proves compatibility of the exact range equivalence with
the original Harris level arrows. It retains the actual universe-zero number
fields, central simple unitary algebra, Harris signature charts, abelian
family, supplied dual witness and dual-valued map, and full integral-order
action. Tensor/duality, Weil-transition, adelic and torsion finite-etaleness
prerequisites remain supplied. The original test scheme is quasi-separated,
connected and locally noetherian, with an algebraically closed geometric point
field, finite geometric fibres, invertible torsion orders and finite-etale
roots of unity. The old raw fixed-level set at `U` is required to be nonempty.
The groups, actions, raw quotients and covers are the existing actual
constructions, using the original opposite right-action convention.

Fix levels `U`, `V`, `Z`, `J`, a raw class `q` at `V`, a raw class `r` at `Z`
and a raw class `t` at `J`. An original Harris arrow `j : Z ⟶ J` is supplied
together with the equation that its existing right-orbit translation sends
`r` to `t`. Write `Y` for the selected cover of `q`, `x` for its distinguished
geometric lift, `Tq = Over.mk (Y.obj.hom ≫ T.hom)` and `fq : Tq ⟶ T` for the
map with underlying morphism `Y.obj.hom`. The direct source family has
integral action literally `(relativeEndRestrict B fq).comp a`.
Quasi-separatedness of `Tq.left`, finite geometric fibres at `x.left`,
invertible torsion orders and finite-etale roots of unity there remain
explicit inputs. The finite-etaleness of `fq.left` used in the comparison
comes from the actual source cover.

`harrisIntegralCMFiniteOrbitCoverHomLevel_postcomp_transport` applies to every
actual cover morphism `f` from `Y` to the selected cover of `r`. It proves
that `HomLevel` of `f` followed by the existing actual cover transporter of
`j` is the original direct raw tower map of `j` applied to `HomLevel f`.
The equality is in the direct tower on `Tq` with the literal restricted
action. To prove it, injectivity of actual restriction evaluation reduces the
equality to raw classes on the original base. The existing `HomLevel` value
formula and restriction-evaluation naturality rewrite both sides.
Associativity of actual slice-category composition and the transporter
fibre formula, applied at `x ≫ f.hom`, give the remaining equality. Thus this
comparison holds after every preceding actual cover morphism.

`harrisIntegralCMFiniteOrbitCoverHomLevelRangeMap` maps between the exact
subtypes in the existing `HomLevelRangeEquiv` at `r` and `t`. At `r`, the
subtype consists of direct raw fixed levels at `Z` whose actual restriction
evaluation belongs to the monodromy orbit of `r` and is fixed by every
element of the original fundamental group fixing `x`. At `t`, the identical
condition uses level `J` and the orbit of `t`, with the same source lift and
its full stabilizer. The definition takes the inverse source range
equivalence, postcomposes the resulting actual cover morphism by the actual
transporter of `j`, and applies the target range equivalence. It constructs a
map between these explicit subtypes rather than presupposing preservation
of their conditions.

`harrisIntegralCMFiniteOrbitCoverHomLevelRangeMap_val` proves that the
underlying direct level of this map is exactly the original direct raw tower
map of `j` on the underlying input level. Unfolding the range map gives
`HomLevel` of the reconstructed morphism followed by the transporter. The
arbitrary-morphism comparison above rewrites this to the direct tower map
of the reconstructed `HomLevel`. The source equivalence's inverse law,
followed by the underlying-value projection, identifies that `HomLevel` with
the original input level. In particular, the original tower transition
preserves target-orbit membership and full-stabilizer fixedness on this
exact range.

`harrisIntegralCMFiniteOrbitCoverHomLevelRangeEquiv_natural` proves the
commuting square: applying the source range equivalence to an actual cover
morphism and then the range map equals postcomposing that morphism by the
actual transporter and applying the target range equivalence. After
unfolding the range map, the source equivalence's other inverse law proves
the equality in the target subtype.

The full source-point stabilizer condition is retained throughout. This
unit neither equates that stabilizer with the image of the source
fundamental group nor removes the condition from the exact range. It gives
level-arrow compatibility for the direct raw comparison on selected
finite-etale covers; the comparison on the full admissible test category,
normalized rational-isogeny comparison, construction and admissibility of
the representing PEL scheme, smoothness and division-case projectivity
remain open. The unit is an internal deduction from the existing actual
restriction, tower, cover and range constructions, and introduces no new
original-literature assertion.
