# Nonvanishing of the lower canonical scalar in the weighted weak expansion

`LowerDensityCanonicalScalarNonzeroStatement` concerns the original lower
density package `PM` from `RationalWeakExpansionCFamily`. Fix the ambient
connected reductive group, the standard Levis, the chosen normalizer lift and
Levi inclusion, the actual split component `sc` of the inducing Levi, the
irreducible admissible representation `π`, and the original Haar measure on
the Levi quotient with its Borel measurable structure. The `BorelSpace`
instance is an explicit binder of the statement. If `π` is square integrable
modulo the rational points of that split component (viewed inside the literal
Levi), then `PM.canonicalScalar ≠ 0` in the rational unramified character
function field of the lower inducing Levi. The field and representation-carrier
universes are independent.

## Implemented proof

The general lemma `DynamicInducedOrbit.DensityPackage.canonicalScalar_ne_zero_of_squareIntegrable`
starts with a density package on a dynamic parabolic. Assume the inducing
representation is irreducible and square integrable modulo an actual split
center for the given quotient Haar measure.

1. The actual generic irreducibility theorem
   `ActualCommonLeviV3.exists_actual_induction_irreducibility_factor` supplies a
   nonzero regular function on the inducing characters outside whose zeros the
   induction from the opposite parabolic is irreducible. Transport that
   irreducibility to the literal Levi induction via `normalizedInductionLeviEquiv`.
2. Intersect the package's nonempty open **forward** convergence start with the
   nonzero locus of the irreducibility function and the regular locus of the
   reverse presentation. This intersection is open and nonempty: the product
   of the two nonzero regular functions has dense nonvanishing locus. No
   intersection of the two integral convergence starts is asserted or used.
3. If the canonical scalar were zero, `conditionalCanonicalRationalScalar_spec`
   would make the continued composite zero at each character of this
   intersection. The forward continuation agrees there with the actual
   integral, which is nonzero by `conditionalForwardFamily_ne_zero`. A nonzero
   intertwiner **out of** an irreducible representation is injective, so the
   reverse continuation must be zero. In the common compact picture, clearing
   the nonzero reverse denominator shows that its polynomial numerator is
   zero on the intersection.
4. Apply `rationalUnramifiedPolynomial_eq_zero_of_isOpen` to that numerator on
   each fixed input vector. It vanishes everywhere, so clearing on the
   package's nonempty reverse start forces the actual reverse compact
   operator to be zero there. Transporting back to induced representations
   contradicts `conditionalReverseFamily_ne_zero`.

For the exact lower package, `lowerCentral_isActualSplitCenter` uses the split
component `sc ≫ j.inv`, where `j` is the published `lowerParameterIso`. Its image
on rational points agrees with conjugation of the original rational split
center, by `leviRationalPointHomeomorph_lowerParameterIso`. The theorem
`lowerDensityCanonicalScalarNonzero` then applies the general lemma to the
published `lowerRepresentation_isSquareIntegrable` for the transported
`lowerMeasure`, and to the irreducibility of `lowerRepresentation`. This uses
the original measure, modulo the original split component, and requires no
new analytic premise beyond the density package and the stated square
integrability.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), IV.3 (5)–(6), printed p.287
(PDF p.53), uses the scalar of the two opposite intertwining operators, and
proves nonvanishing at a square-integrable representation. V.2 and V.2.1,
printed pp.292–293 (PDF pp.58–59), use its inverse in the Plancherel density.
The registered source is `waldspurger-2003-plancherel`.

The result here is a derived nonvanishing assertion **in the function field**,
not a nonzero evaluation at every square-integrable parameter. The Lean proof
uses the package's canonical rational scalar, the two actual convergence
starts, and generic opposite irreducibility, not the Hermitian adjunction and
specialization argument of IV.3 (6). It supplies the scalar nonvanishing input
for the weighted domain's interior criterion. It does not prove unweighted
joint convergence, regularity of a density ratio on the unitary orbit, or any
of the three exact regularity, pointwise expansion, and packet targets.
