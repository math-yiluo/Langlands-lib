# Compact probability integral on the actual product-induced source

This derived comparison expands the published actual compact source form into
an integral of the actual coefficient-tensor form. It is a prerequisite for
comparing Waldspurger's fixed compact picture under unitary twists: see
Waldspurger (2003), V.2, printed p.293 / PDF p.59, for the two-factor Hermitian
form, and VI.1, printed pp.295–296 / PDF pp.61–62, for the fixed compact picture.
The form here has the already specified compact probability normalization.
It does not identify that normalization with an arbitrary Bruhat measure.
The comparison concerns `productForm`, before multiplication by the inverse
formal degree. The separately published `formalDegreeProductForm_eq` supplies
that rescaling; this module introduces no new formal degree or orbit measure.

The ambient group and coefficient carrier have independent universes. The
semidirect decomposition, closed parabolic and unipotent radical, compact open
`K`, factorization `G = P K`, local compactness, nonarchimedean topology, second
countability, Borel structure, ambient unimodularity, full parabolic modulus
identity and compact-open cofinality on the Levi remain explicit. The inducing
representation is admissible and has a supplied invariant positive form.
No irreducibility is assumed for it or for either induced representation.
These are conditional statements about the displayed subgroup and representation
data; no realization for every reductive rational-point group is asserted.

`productIntegralPairing` defines the scalar pairing of two original source
functions by integrating their pointwise coefficient-tensor pairing over
`K × K`. The coefficient form is linear in the second variable and conjugate
linear in the first, as in V.2. The definition and its integrability lemma do
not require the parabolic modulus identity or `G = P K`; those hypotheses enter
the comparison with the previously constructed invariant source form.

`integrable_productForm_pairing` proves integrability of the coefficient-core
pairing of two original source functions over `K × K`. The measure is exactly
`(measure K hK).prod (measure K hK)`, the product of the compact probabilities
already used in each induced factor. Local constancy of induced evaluations
gives continuity of their scalar pairing; compactness gives integrability.
No topology on the coefficient vectors is assumed.

`productForm_inner_integral` identifies the whole published source form with
that product integral. Surjectivity of the published product-induction tensor
equivalence reduces both source functions to algebraic tensors. Double tensor
induction reduces to pure tensors, where the published source and coefficient
product formulas and `integral_prod_mul` give the identity. The proved scalar
integrability justifies integral additivity in both induction steps.

`productForm_inner_integral_integral` gives the same formula as an iterated
integral by Fubini, using the established integrability. No separately selected
Haar measure on the product is introduced. Actual unitary-twist isometry,
formal-degree normalization of the fixed compact picture, orbit descent,
the spectral density and Plancherel isometry remain further obligations.
