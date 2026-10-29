# The regular Hodge determinant over the actual cocharacter reflex field

This construction descends the already constructed actual
regular Hodge determinant to the existing cocharacter reflex field,
with the complex inclusion, coefficient, uniqueness, homogeneity,
complex determinant evaluation and change-of-coefficient-ring laws.
The arithmetic types and variable index have `Type 0` scope, matching
the exact reflex-descent proposition. The arithmetic telescope retains
all three scalar towers and the actual CM-section hypothesis.

`kottwitzReflexDeterminant` uses `PolynomialDescent.descend` along the
inclusion of `D.kottwitzCocharacterReflexField C` into `ℂ`. Its
coefficient-range proof is obtained by forming the subtype from the
published theorem `kottwitzHodgeDeterminantReflexDescent` applied to
the retained CM-section hypothesis, every finite family and each monomial.
There is no assumed descent-proof parameter. The field is not defined from the
coefficients. The polynomial is uniquely determined by its image in
the complex polynomial ring. The inclusion and coefficient laws come
from the helper, as do uniqueness and reflection of homogeneity.
The complex evaluation identity then uses the published actual
Hodge-action determinant identity.

`kottwitzReflexDeterminantBaseChange` maps coefficients along a ring
homomorphism to any commutative ring. The coefficient formula, identity,
complex-inclusion specialization, composition law and evaluation
identities follow from the corresponding Mathlib polynomial-map laws.
Homogeneity is preserved by any coefficient map. No reducedness or
field assumption is imposed on these target rings, so the formulas
also apply to rings with nilpotents. This is a polynomial construction;
it does not construct a Hodge module over every such ring.

The original source is Robert E. Kottwitz, *Points on Some Shimura
Varieties over Finite Fields* (1992), section 5, printed pp.389–390
(PDF pp.17–18), registered as
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
Those two pages were read again for this construction. The first
defines the Hodge determinant and states its reflex-field and integral
coefficient properties. The second uses the polynomial on actual Lie
sections in the moduli problem. This unit implements only field
coefficient descent and its ring-map laws. Integral coefficients, the
Lie-section determinant condition, local order and lattice hypotheses
and representing scheme levels remain separate obligations.

Worker 57 authored this construction. The generic descent helper is
also by Worker 57. The arithmetic membership theorem is imported from the independently
published `HodgeDeterminantReflexProof` module; its authorship is retained
in that module. This unit adds the polynomial construction and its laws.
