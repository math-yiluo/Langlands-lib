# Identity and transporter compatibility of actual orbit-cover levels

This internal unit compares the existing direct raw levels obtained from actual
finite-etale orbit-cover morphisms with the original selected-cover level and
its Harris level transitions. It uses the original universe-zero number fields,
central simple unitary algebra, signature charts, abelian family, supplied dual
witness and dual-valued map, and full integral-order action. The tensor/duality,
Weil-transition, adelic and torsion finite-etaleness prerequisites remain
supplied. The original test scheme is connected, quasi-separated and locally
noetherian; its geometric point has algebraically closed field. Finite fibres,
invertible torsion orders and finite-etale roots of unity are explicit inputs.
The old fixed-level set at `U` is required to be nonempty.

For a raw class `q` at `V`, let `Y` be its existing selected finite-etale orbit
cover and `x` its distinguished actual geometric lift. The direct family over
`Tq = Over.mk (Y.obj.hom ≫ T.hom)` has integral action literally
`(relativeEndRestrict B fq).comp a`, where `fq` has underlying map `Y.obj.hom`.
Quasi-separatedness, finite fibres at `x.left`, invertible torsion orders and
finite-etale roots of unity on this source cover remain explicit inputs. No
new choice of family or action replaces this direct pullback.

`harrisIntegralCMFiniteOrbitCoverHomLevel_id` proves that applying the existing
cover-morphism-to-level construction to the identity of `Y` recovers exactly
`harrisIntegralCMFiniteOrbitCoverLevel`. The proof applies injectivity of
actual restriction evaluation. The Hom-level value formula, the selected-level
value formula, and the distinguished-point fibre comparison identify both
values with the same original raw class `q`.

`harrisIntegralCMFiniteOrbitCoverTransportLevel` specializes the existing
Hom-level construction to the actual cover morphism induced by an original
Harris arrow `j : V ⟶ Z`. Its target raw class `r` and the equality between
`r` and the actual right translation of `q` by `j` are supplied. The result is
a fixed raw level at `Z` on the same direct source family over `Tq`.

`harrisIntegralCMFiniteOrbitCoverTransportLevel_val` proves that actual
restriction evaluation of this level is exactly `r`. It uses the existing
Hom-level value formula, the theorem that the actual cover transporter takes
the distinguished source lift to the distinguished target lift, and the
fibre comparison at that target lift.

`harrisIntegralCMFiniteOrbitCoverTransportLevel_eq_map` identifies this
constructed level with the image of the selected cover's level under the
actual `map j` in its direct raw tower. The proof applies restriction
evaluation injectivity, then the new restriction/level-arrow compatibility
lemma in `HarrisIntegralCMRestrictionLevelCompatibility`, the selected-level
value formula and the supplied target equality. Thus the transition uses the
original Harris arrow and the literal restricted integral action.

All these declarations are deductions from existing actual orbit covers,
restriction evaluation and level towers. They assert no equality between a
fundamental-group image and a full point stabilizer, and establish no inverse
or surjectivity for the Hom-level map. Comparison on the full admissible test
category, normalized rational-isogeny comparison, existence of a representing
scheme, admissibility, smoothness and division-case projectivity remain open.
