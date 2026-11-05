# Formal-degree normalization of the actual fixed compact picture

This is a derived consumer of Waldspurger, *La formule de Plancherel pour
les groupes p-adiques*, V.2, printed p.293 (PDF p.59), and VI.1, printed
pp.295–296 (PDF pp.61–62), source `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
V.2 rescales the tensor product of the two actual induced forms by the inverse
Schur degree. VI.1 identifies the unitary unramified twisted product inductions
with one fixed compact picture. This unit proves that these existing maps
preserve the actual degree-normalized forms.

The general-framework assumptions of `FixedCompactProductForm` remain
explicit: semidirect decomposition and closedness, the indicated locally
compact and nonarchimedean topology, second countability and Borel structures,
compact open `K` with `G = PK`, ambient unimodularity, the parabolic modulus
identity, and compact-open cofinality in `M`. In addition, `C` is a normal
central subgroup of `M`; the same quotient `M ⧸ C` has the same specified
inversion-invariant Haar measure `μ` everywhere. The original inducing
representation is irreducible and square integrable modulo this actual
subgroup. No irreducibility of an induced representation is assumed.
The group, character-index and coefficient-carrier universes are independent.

`formalDegreeFixedProductCompactForm` restricts the existing
`formalDegreeProductForm` to the compact product subgroup and pulls it through
the inverse untwisted `productCompactRestriction`. No positive inducing form
is among its inputs. `formalDegreeFixedProductCompactForm_eq` proves that
every positive inducing form computes it as `fixedProductCompactForm`
rescaled by the inverse of the actual `representationFormalDegree`.
This follows by transporting `formalDegreeProductForm_eq`; the integral
formula then expands the unscaled compact form. The compact measure remains
exactly the product of the two specified compact Haar probabilities.

`formalDegreeProductInducedCompactEquiv_inner` applies to every unitary
unramified character and every pair of original twisted product-induced
sections. The positive inducing form used in its proof is obtained from
the proved square-integrability unitarization theorem. Rewriting the two
canonical forms with that form and its unitary twist reduces the identity
to the previously proved `productInducedCompactEquiv_inner` and
`representationFormalDegree_unitaryTwist`. The latter compares the degrees
with the same `C`, quotient and Haar measure; no change of measure is made.
The continuity of the positive character family and of the actual Levi
projection, and norm one of the twisting character, remain explicit.

`formalDegreeProductCompactIsometry` bundles the exact existing
compact-equivariant restriction equivalence with the proved equality of
the pulled-back fixed form and the restricted canonical twisted source
form. Its value lemma identifies that map literally. The construction uses
no topology or completion of the coefficient or section carrier.

No arbitrary Bruhat-measure normalization, orbit measure, spectral-family
descent, wave-packet convergence or whole-task completion condition is proved
here. Actual rational-point realization of the displayed general-framework
structural assumptions is a separate obligation.
