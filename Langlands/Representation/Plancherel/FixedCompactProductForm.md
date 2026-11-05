# The fixed compact product form and actual unitary twist isometry

This derived unit compares the actual compact restriction of the product
induction with its positive Hermitian form. Its source context is Waldspurger,
*La formule de Plancherel pour les groupes p-adiques*, V.2, printed p.293
(PDF p.59), and VI.1, printed pp.295–296 (PDF pp.61–62), source
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
V.2 constructs the induced Hermitian forms and their inverse-degree tensor
product; VI.1 identifies the unitary unramified twisted product inductions with
one fixed compact picture by literal restriction and retention of the original
functionals. The comparison here is before formal-degree rescaling.

The group universe `uG`, character-index universe `uI`, and coefficient-carrier
universe `uV` are independent. The general-framework inputs are the displayed
semidirect decomposition, closed subgroups, local compactness, second
countability and Borel structure, a compact open subgroup `K` with `G = PK`,
ambient unimodularity, and the exact parabolic modulus equality.
Admissibility, compact-open cofinality and a positive invariant form on the
original canonical `SmoothRep` are supplied. Irreducibility of either induction
and a topology on its coefficient module are not required.

`productCompactRestriction` is the existing normalized compact restriction
equivalence for the untwisted product induction, with the membership and subtype
formulations of `G = PK` converted explicitly. Its forward and inverse
evaluation lemmas identify the original function values at every compact point.

`fixedProductCompactForm` restricts the original untwisted `productForm` to
`K.prod K` and pulls it back through the inverse restriction equivalence. It is
a positive definite form invariant under the actual compact product action.
Its integral formula follows by applying `productForm_inner_integral` to the
two extended sections and using the inverse evaluation lemma pointwise.
The measure is exactly `(measure K hK).prod (measure K hK)`, the product of
the two specified compact Haar probabilities; no new product Haar is chosen.

`productInducedCompactEquiv_inner` says that the already constructed
`productInducedCompactEquiv` for every unitary unramified character preserves
the whole original product-induced Hermitian form. The family of positive
characters is continuous, the actual Levi projection is continuous, and
the twisting character has norm one everywhere. Rewriting both forms as
compact product integrals reduces the proof to the published pointwise
evaluation of the restriction map and `productCompactTwistTensorEquiv_inner`.
The fixed compact form itself has no twisting character as an argument.

`productInducedCompactIsometry` bundles that exact existing compact-equivariant
representation equivalence with equality of the pulled-back fixed compact form
and the restricted twisted source form. Its value lemma identifies the map
literally; the form equality follows by extensionality from the proved inner
product identity. This uses no topology or completion on the section carrier.

The result does not supply formal-degree invariance, a comparison with an
arbitrarily scaled Bruhat measure, orbit measure or spectral family, analytic
convergence, or any whole-task completion condition. Those consumers remain
separate obligations.
