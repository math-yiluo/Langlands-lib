# Global torsion sections from a normalized Harris orbit

This internal comparison works over a connected locally noetherian base with
an algebraically closed field-valued point and the existing finite geometric
fibre, torsion finite étaleness and unit hypotheses. It uses the actual
finite-étale action equivalence and the finite reduction of the existing
normalized Harris fixed-orbit tower. It does not assume an ordinary moduli
representer or replace the Harris level condition.

`harrisIntegralGlobalTorsionEquiv` identifies actual global `m`-torsion with
`harrisIntegralFixedTorsion`, the additive subgroup of actual geometric
`m`-torsion fixed by monodromy at the chosen point. The kernel universal
property identifies torsion values with morphisms into the actual
multiplication-kernel cover, and identifies restriction with precomposition
by the geometric point. The fibre of the identity cover is a singleton.
Thus a global section evaluates to a fixed value by monodromy naturality.
Faithfulness of the finite-étale action functor shows that sections with the
same evaluation are equal. Conversely, a fixed torsion point defines an
equivariant constant function from the fibre of the identity cover. Fullness
lifts that function to a morphism of covers, giving an actual global torsion
section with the specified evaluation. The equivalence is additive since its
forward map is the existing additive restriction homomorphism, with codomain
restricted to the fixed subgroup.

For a level contained in the principal congruence subgroup at `m`,
`harrisIntegralLevelSections` starts with the existing invariant level and
its existing normalized level condition. The preceding monodromy reduction
sends the source quotient to fixed finite torsion. At a normalized frame
representing the orbit this map agrees with the pointwise additive
equivalence to all finite torsion, after inclusion of the fixed subgroup. It
is therefore bijective onto that subgroup. Composing its additive
equivalence with inverse restriction gives an additive equivalence from the
actual source quotient `Λf/mΛf` to the group of actual global `m`-torsion
sections. `harrisIntegralLevelSections_restrict` proves that these sections
restrict at the reference point to the preceding representative-independent
orbit reduction.

This constructs actual sections from an existing normalized orbit. It does
not assert that such orbits always exist, identify reductions of finer
orbits with those orbits themselves, give the comparison with ordered finite
level on every geometric fibre, or prove moduli representability.
