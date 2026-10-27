# Tensor compatibility of normalized refined induction

Author: Worker 321.

`Langlands.Parabolic.refinedInductionTensor` proves the published proposition
`Langlands.Parabolic.RefinedInductionTensorTheorem.{uF,uV}`. For every actual
p-adic field, compatible topology, outer block shape, refinement, and smooth
complex inner-Levi factor family, it supplies the actual equivariant linear
equivalence from normalized refined induction of the transported external
tensor to the external tensor of the normalized block inductions. Its inverse
satisfies the pointwise pure-tensor formula in `CanonicalInverse`.

The proof preserves independent field and coefficient universes, the natural
output carrier universe `max uF uV`, every finite family including the empty
family, and the positive-half normalization. It imposes no dimension,
admissibility, irreducibility, finite-length, or supplied-equivalence
hypothesis. The statement pair and its import closure are unchanged.

The implemented proof has three steps.

1. `RefinedInductionTensor.pointwiseMap_bijective` specializes the published
   `Induction.finiteProductTensorMap_bijective` to complex coefficients,
   index type `Fin B.length`, groups
   `GeneralLinear (B.size i) F.Carrier`, inner parabolic subgroups
   `(S i).parabolic F.Carrier`, and the actual normalized inducing actions
   `blockInducingRepresentation F T B S A`.
   The compatible topology supplies `generalLinearNonarchimedean` and
   `generalLinearLocallyCompactSpace`, while `parabolicQuotientCompact`
   supplies compactness of each actual left quotient. The generic map is
   therefore bijective. Composing with the published
   `inducedNormalizationEquiv` transfers this bijectivity to `pointwiseMap`.
   This normalization equivalence uses the identity on coefficients and
   retains the prescribed positive half-moduli.
2. `comparison_of_pointwiseMap_bijective` upgrades the actual pointwise
   intertwiner to an equivariant linear equivalence using
   `Representation.IntertwiningMap.ofBijective`. Taking its symmetric
   equivalence gives the direction required by `Comparison`. The inverse of
   this symmetric equivalence is the original pointwise map; its evaluation
   on a pure tensor is exactly `pointwiseMap_tprod_eval`. This proves
   `CanonicalInverse` and constructs an element of the required nonempty
   subtype.
3. `refinedInductionTensor` introduces the full telescope of the published
   proposition and combines the preceding two lemmas. Its theorem type is
   precisely `RefinedInductionTensorTheorem.{uF,uV}`.

The imported generic bijectivity proof uses compact quotients and
uniform open right stabilizers. At a compact open product level, distinct
double-coset classes form a finite set. Values at representatives lie in the
appropriate fixed coefficient spaces and lift to tensors of factor fixed
spaces. Finite sums of compact local sections reconstruct each target
function. For injectivity, a tensor is put at a common compact open level and
expanded in those sections; evaluation at representatives detects its
coefficients. These are the mechanisms supplied by
`FiniteProductTensorBijectiveProof`; the present module supplies the actual
normalized parabolic specialization. All finite products, tensor expansions,
and comparisons include the empty index family.

The provenance is a derived specialization of the published generic
pointwise-map proof and the actual refined normalization and function-map
adapters. Its literature motivation is I. N. Bernstein and A. V. Zelevinsky,
*Induced representations of reductive p-adic groups I*, Ann. Sci. ENS (4)
10 (1977), 441–472, Proposition 1.9(e),(g), printed p.445 / PDF p.6,
and section 2.3, printed p.446 / PDF p.7. The registered original is
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Those passages were read directly: they give compact/smooth agreement for
compact quotients, compact induction's external-factor compatibility, and
the parabolic application. The finite-family formula with the actual
refined subgroup and its canonical inverse is an internal specialization,
not a literal finite-family statement in the original. This proof makes no
adjacent-swap, association, naturality, or admissibility claim.
