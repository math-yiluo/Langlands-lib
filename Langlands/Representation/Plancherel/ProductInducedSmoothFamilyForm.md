# Positive cover integrals on actual smooth induced families

This derived construction combines Waldspurger's actual smooth family model
with the canonical inverse-formal-degree fiber forms. The original passages are
Waldspurger, *La formule de Plancherel pour les groupes p-adiques (d'après
Harish-Chandra)* (2003), V.2, printed p.293 / PDF p.59, and VI.1, printed
pp.295–296 / PDF pp.61–62. VI.3, printed pp.301–302 / PDF pp.67–68, subsequently
chooses an orbit measure. The present module concerns integration on the
unitary parameter cover and does not identify that measure with an orbit
measure or construct the density-weighted spectral form of VII.2.

The group, subgroup decomposition, compact open subgroup and normalized
induction are the existing canonical objects. The explicit hypotheses are
local compactness, nonarchimedean group topology, second countability, Borel
measurability, local compactness of the parabolic, closedness of the parabolic
and unipotent subgroups, compact-open factorization, ambient unimodularity,
the full parabolic Haar-modulus identity, continuous Levi projection and
continuous positive characters. The inducing object is irreducible admissible
and square integrable modulo the specified central normal subgroup `C`.
Its quotient carries the same Borel inversion-invariant Haar measure `μ`
at every unitary twist. Compact-open cofinality of the Levi remains explicit.
No irreducibility of the induced representation is required.

The parameter cover has supplied group coordinates
`e : unitaryUnramifiedCharacters ν ≃* (J → Circle)` with `J` finite.
The coefficient carrier has no assumed norm or topology. Group, character
index, carrier and finite-coordinate universes remain independent.
The parameter measure `η` is a finite Borel measure; positive definiteness
requires positive measure on every nonempty open set. These are explicit
conditions on cover integration, not assertions of source normalization.

`unitaryTorusProductForm` is exactly the existing `formalDegreeProductForm`
in the actual normalized product-induced fiber at the character
`unitaryTorusParameter ν e z`. Its square integrability and irreducibility
come from the proved unitary-twist invariance results. Unitarity follows from
membership in the actual unitary character subgroup. No chosen positive
inducing form is a construction input.

`unitaryTorusProductForm_inner` applies the proved degree-normalized compact
restriction isometry at each parameter. It identifies the varying fiber
pairing with one `formalDegreeFixedProductCompactForm` on the literal
compact restrictions. `productInducedSmoothFamilyRestriction` restricts the
existing family equivalence to the actual smooth submodule and its full
stabilizer covariance, including the possibly nontrivial coefficient action.

`isSmooth_unitaryTorusProductForm_pairing` uses this pointwise identity and
the proved finite scalar-smooth pairing theorem. Compactness of the torus
then proves actual Bochner integrability against `η` in
`integrable_unitaryTorusProductForm_pairing`.

`productInducedSmoothFamilyCore` faithfully pulls back
`finiteSmoothEquivariantFamilyCore`, using the fixed canonical compact form.
Its positivity and definiteness therefore use the proved finite-family
integral result: a continuous nonnegative self-pairing of zero integral
vanishes everywhere because `η` is positive on nonempty open sets.
`productInducedSmoothFamilyCore_inner_integral` proves that its pairing is
the integral of the actual inverse-degree fiber pairings.

`productInducedSmoothInvariantTensorCore` restricts the existing positive
finite smooth tensor core to the actual diagonal invariant tensors.
`productInducedSmoothTensorFamilyEquiv_inner` proves that evaluation followed
by normalized extension preserves the entire integrated form. The proof
uses the published pointwise restriction formula under the same integral.

`productInducedSmoothOrbitCoverCore` pulls the family core back through the
proved equivalence from coherent smooth sections on every actual orbit
representative. Its integral formula evaluates the sections at the literal
parameter representatives. `productInducedSmoothTensorOrbitEquiv_inner`
combines the family isometry with the inverse laws of coherent extension
and pullback. This uses the already proved representative coherence and
choice independence, without assuming coherent choices of vector lifts.

The module supplies positive forms on the actual dependent family and
coherent-section spaces and identifies their invariant tensor description
isometrically. It does not prove independence of arbitrary coordinate changes
or cover measures, select the locally measure-preserving orbit measure,
construct the density `μ(ω)`, prove global action invariance, construct the
global finite-support spectral form, or establish a Plancherel isometry.
