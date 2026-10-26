# A scalar integral form on actual normalized GL induction

Author: Worker 117.

`Langlands.PadicField.TopologicalData.normalizedIntegralForm` constructs an
actual `InvariantPositiveForm` on `T.normalizedParabolicInduced B σ` from a
supplied invariant positive form on the actual Levi representation `σ` and
explicit scalar integration data. The field and carrier universes `uF` and
`uV` are independent. The construction applies to every supplied compatible
realization `T` and block shape `B`, without any topology or norm on the
representation carrier.

This is a conditional constructor, not a proof of scalar integral existence or
of `GLNormalizedInductionUnitarityStatement`. Its inputs include a subgroup
`K`, a measure on `K` positive on every nonempty open set, the actual
factorization `G = P K`, and the following property of scalar integration.
Every locally constant function `φ : G → ℂ` with left covariance
`φ(q*x) = δ_P(q)*φ(x)` must have an integrable restriction of every right
translate to `K`, with the same integral as the unshifted restriction.
The translation parameter ranges over all `g : G`. The scalar `δ_P` is the
existing positive full Levi modulus, through its specified coercions to the
complex numbers.

The statement does not require compactness or a Haar probability normalization
after these analytic inputs have been supplied. Those stronger conclusions
belong to the separate `GLParabolicCompactScalarIntegralStatement`. This
constructor neither assumes nor proves an invariant measure on `P \ G`.

## Implemented construction

The private lemma `normalized_pairing_covariant` applies
`T.normalizedParabolicInduced_covariant` to both arguments of the input
Hermitian form. Its conjugate-linear first argument and linear second argument
produce the product of the two positive half-modulus factors. The input form's
Levi invariance removes the two Levi actions. Complex conjugation fixes the
real square root, and `NNReal.mul_self_sqrt` identifies its square with the
full modulus. This keeps the existing positive normalization and
right-translation convention.

The constructor then applies the independently published generic
`Langlands.Induction.integralInvariantPositiveForm` to the twisted and inflated
inducing representation, using the supplied form's `InnerProductSpace.Core`.
That core need not be invariant under the modulus twist. The constructed
inner value is the complex scalar integral of
`k ↦ b.inner (f(k)) (h(k))`.

The published `Induction.pairing_isLocallyConstant` supplies local constancy.
The scalar hypothesis and the covariance lemma supply integrability by taking
the translation to be `1`, and invariance by taking an arbitrary ambient
element. All Hermitian laws, nonnegativity and definiteness are then the laws
of the imported generic constructor. Its definiteness argument uses full
support to pass from an almost-everywhere vanishing nonnegative diagonal to
pointwise vanishing on `K`, and the factorization extends vanishing to `G`.
There is no integral of carrier-valued functions, identification with a smooth
conjugate dual, admissibility, finite dimension or completion.

## Provenance and remaining obligations

This is an internal specialization of the generic compact integral constructor,
combined with the Library's actual normalized covariance and modulus
definitions. The compact-picture route is motivated by Casselman,
*Introduction to the theory of admissible representations of p-adic reductive
groups*, draft May 1, 1995, section 2.4, printed/PDF pp.26–27 and section 3.1,
pp.32–33, especially Propositions 3.1.3 and 3.1.4.

The registered source is `casselman-1995-admissible-representations`, SHA-256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
The retained original is
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
Those sections and the page images were read during development of the parent
unitarity proof. This generalized conditional interface is derived content,
not a separate verbatim theorem in the source.

The compact subgroup, probability Haar measure, parabolic disintegration and
full ambient scalar invariance remain separate proof obligations. This module
also supplies no finite-tensor positivity theorem or closed unitarity proof.
