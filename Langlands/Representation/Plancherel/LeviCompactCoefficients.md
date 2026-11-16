# Compact probability coefficients in the positive Levi normalization

This internal adapter provides the exact compact probability normalization on
`leviProductInducedCoefficientObject`. Its source motivation is Waldspurger,
*La formule de Plancherel pour les groupes p-adiques*, V.3 (printed p. 295 / PDF p. 61), registered as
`waldspurger-2003-plancherel`. It combines already constructed Library objects;
it does not assert the analytic extension or unitarity theorem of V.3.

The ambient group and representation carrier have independent universes.
The hypotheses are the displayed semidirect decomposition, closed radical,
radical unimodularity, locally compact nonarchimedean second countable
Hausdorff group, Borel structure, closed locally compact parabolic, continuous
Levi projection, compact open subgroup `K`, factorization `G = P K`, ambient
unimodularity, the displayed subgroup modular-character identity and inducing
admissibility. The product tensor lemmas additionally display quotient
compactness; it follows from the supplied compact representatives.

`leviCoefficientTensorEquiv` composes the inverse value-preserving
`productInducedCoefficientLeviEquiv` with
`CompactInduction.coefficientTensorEquiv`. The latter uses the duality obtained
by integrating over **the Haar probability measure on the supplied `K`**.
`leviCoefficientMap` is the corresponding actual coefficient map.
`leviIntegrand` is the original diagonal contraction, restricted to `K`.
The integral and pure tensor theorems identify these constructions at every
group argument. The tensor normalization theorem holds for all algebraic
tensors. The action theorem proves the source convention
`E((x₁,x₂)v)(g) = E(v)(x₂⁻¹ g x₁)`, and bi-invariance follows from the existing
smooth coefficient result.

`leviProductForm` and `leviFormalDegreeProductForm` pull back the existing
compact product forms through the same value-preserving equivalence. The
latter uses the actual central quotient `M / C`, its displayed Haar measure
`μ`, square integrability and irreducibility of the inducing representation.
Its rescaling theorem proves the inverse of
`representationFormalDegree C hC μ hcof hsq hi`, with no new formal degree
or quotient measure. The two pure tensor formulas retain the actual compact induced pairings.
The coefficient-form comparison uses the same compact duality equivalence.
Independence of the product form uses irreducibility only on the inducing
representation.

The proofs use value preservation before integration, the published compact
coefficient integral, the product tensor normalization comparison, intertwiner
equivariance and pullback of positive forms. They are elementary adapters of
the imported constructions. No equality with the separate Bruhat quotient
normalization of `leviProductInducedCoefficientMap` is claimed. No
irreducibility of a parabolically induced representation is assumed.
