# The compact Hermitian form on the actual product-induced source

This is a derived comparison for Waldspurger, *La formule de Plancherel pour
les groupes p-adiques* (2003), V.1, printed p.288 (PDF p.54), V.2,
printed p.293 (PDF p.59), and I.3, printed p.243. The source equips
`L(omega,P)` with the inverse formal degree
times the tensor of the two induced Hermitian forms. This module places that
form on the existing `productInducedCoefficientObject`, the actual normalized
product-induced function carrier, and proves compatibility with the existing
compact integral coefficient comparison.

## Setting and normalization

The canonical `SmoothRep` and existing semidirect-decomposition framework are
used throughout. The group is locally compact, second countable and
nonarchimedean, with Borel measurable structure. The subgroups `P` and `U`
are closed, `P` is locally compact, and the supplied semidirect decomposition
has Levi subgroup `M`. A compact open subgroup `K` satisfies `G = P K`.
Ambient unimodularity and the full parabolic modular-character identity are
explicit. Group and representation-carrier universes are independent.

The inducing representation is admissible and has a supplied invariant
positive Hermitian form, conjugate-linear in its first variable.
Compact-open cofinality on `M` supplies its Hermitian smooth-dual form. Both
induced factors use the existing intrinsic Haar probability on `K`. The
product comparison uses compactness of the left quotient, deduced from the
supplied compact representatives. No comparison with an arbitrarily chosen
Bruhat-density measure is asserted.

The coefficient-form comparisons additionally use a Hausdorff group,
continuity of the Levi projection, and compact-open cofinality on `G`.
Admissibility of induction is derived from the existing theorem using
compact representatives; irreducibility of induction is never required.
Independence from every inducing positive form requires irreducibility of
the admissible inducing representation.

The degree-normalized form uses a normal central subgroup `C` of `M`, its
Borel quotient, and a fixed inversion-invariant Haar measure `mu`. The
inducing representation is irreducible and square integrable modulo `C`.
The actual positive Schur degree is `representationFormalDegree` for this
quotient and measure. Neither an arbitrary scalar nor an additional
unitarizability assumption supplies the normalization.

## Constructions and proofs

`productForm` pulls the existing compact tensor form back along the inverse
of `normalizedProductInductionTensorEquiv`. This transports positivity and
invariance to the actual product-induced function carrier. Its value on two
pointwise product sections is the product of the exact two compact-induced
pairings, as proved by `productForm_inner_tensor`.
`productForm_independent` transports the existing arbitrary-positive-form
independence of the whole tensor.

`dualTensorEquiv_form` compares the existing canonical coefficient-tensor
form with the compact tensor form using `dualTensorEquiv`. The dual factor
is compared by `integralDualEquiv_form`, evaluated on the inverse images of
the two induced-dual vectors. The inverse identities give equality of the
dual pairings. The pure-tensor product identity then extends to all tensors
by induction in both variables and additivity of the Hermitian forms.

`productForm_eq_coefficientForm` pulls that equality back along the inverse
product-induction comparison. Its equivalence is precisely the existing
`coefficientTensorEquiv`, whose coefficient function was already proved to
equal the compact integral of the original diagonal contraction. Thus this
comparison uses the same actual coefficient map and probability.

`formalDegreeProductForm` transports the existing actual-degree tensor form
to the source carrier. `formalDegreeProductForm_eq` computes it with every
positive inducing form, removing the auxiliary choice supplied by the
proved square-integrable unitarizability theorem.
`formalDegreeProductForm_inner_tensor` gives the inverse-degree product
formula on pointwise product sections.
`formalDegreeProductForm_eq_coefficientForm` identifies the entire form with
the same inverse-degree rescaling of the pulled-back canonical coefficient
form.

This unit does not yet prove representative transport for these forms,
identify the central quotient with a realized rational split center, construct
spectral families, or prove wave-packet or Plancherel identities. Those remain
separate obligations. The compact probability and structural hypotheses
remain visible; this is a conditional general-framework comparison.
