# Finite rational tensor comparison: proof

Author: Worker 737.

`Langlands.Analytic.StrictTestDomain.finiteRationalTensorComparison` proves
the published proposition `FiniteRationalTensorComparisonStatement.{u}`.
Let `K` be a complete ultrametric normed field, `P` and `Q` actual presented
strict affinoid `K`-algebras, `d` rational data over `P`, and
`φ : P → Q` a bounded `K`-algebra map whose ring map is finite. Then the
canonical ring map

`d.tensorComparison φ : d.algebraicBaseChange φ →+* (d.pullback φ).algebra`

is bijective. There are no further hypotheses. The coefficient valuation may
be trivial. The numerator tuple may be empty, quotients may be zero, rings may
have nilpotents, and `φ` need not be injective. The theorem's type is exactly
the published proposition.

## Strategy

The proof puts a complete ultrametric norm on the ordinary tensor product
`M := d.algebraicBaseChange φ`. This norm is only a device inside the proof;
the statement and the tensor product carry no topology. With this norm both
factor maps into `M` and the comparison out of `M` are bounded. The bounded
pushout property of the pulled-back rational quotient, already proved in
`RationalPullbackProof`, then gives a bounded inverse.

### The pushout criterion

`algebraicBaseChange_induction` is induction on `M` through sums of products
`d.tensorLeft φ x * d.tensorRight φ y`. `tensorRight_apply_map` restates the
published equation `tensorLeft_comp_baseMap` pointwise.

`bijective_tensorComparison_of_normedModel` assumes a complete ultrametric
normed `K`-algebra `E` and a ring isomorphism `ι : M ≃+* E`. The isomorphism
must send the left factor's scalars to the scalars of `E`, both
`ι ∘ tensorLeft` and `ι ∘ tensorRight` must be bounded, and
`tensorComparison ∘ ι⁻¹` must be bounded. Under these hypotheses the
comparison is bijective. The proof
turns `ι ∘ tensorLeft` and `ι ∘ tensorRight` into bounded algebra maps `a` and
`b` that agree on `P`. The published `d.extension φ a b hab` is the bounded
map `C` out of `(d.pullback φ).algebra` with `C ∘ d.comparison φ = a` and
`C ∘ (d.pullback φ).baseMap = b`. Induction on `M` and the pure-tensor
formula `tensorComparison_mul` give `C ∘ tensorComparison = ι`, so the
comparison is injective. The bounded map `tensorComparison ∘ ι⁻¹ ∘ C`
agrees with the identity on `(d.pullback φ).baseMap`. The published
uniqueness theorem `hom_ext` for maps out of the rational quotient therefore
makes it the identity, so the comparison is surjective.

### The coefficient quotient

Finiteness gives generators `c : Fin n → Q` whose coefficient map
`φ.coefficientMap c` is surjective
(`BoundedAlgHom.finite_iff_exists_surjective_coefficientMap`).
`coefficientSum` is the additive map
`w ↦ ∑ k, tensorLeft (w k) * tensorRight (c k)` from `Fin n → d.algebra` to
`M`. It satisfies `coefficientSum (x • w) = tensorLeft x * coefficientSum w`.
`coefficientSum_baseMap` shows that coefficients from `P` give the right factor.
`coefficientSum_surjective` shows that it is surjective. `coefficientSum_mul`
expresses a product of two coefficient sums through chosen coefficients
`s i j` of the products of generators.

`coefficientKernel` is its kernel, an actual `d.algebra`-submodule.
`CoefficientQuotient` is the quotient of `Fin n → d.algebra` by this kernel,
with Mathlib's quotient norm. `coefficientSection` sends `m` to the class of
any chosen coefficient tuple of `m`. It is a bijective additive map
(`coefficientSection_bijective`), and `coefficientSection_eq_mk_iff` says that
the class of `w` corresponds to `coefficientSum w`. It intertwines
multiplication by `tensorLeft x` with the action of `x`, and therefore also the
scalar actions of `K`.

The following bounds are proved for the quotient seminorm, using only
representatives and `le_mul_norm_quotient_of_forall_mk` or its two-variable
form:

* `norm_smul_coefficientQuotient_le` and
  `norm_scalar_smul_coefficientQuotient_le`: the actions of `d.algebra` and
  of `K` are bounded by the norm of the scalar.
* `norm_coefficientSection_mul_le`: if every `s i j` has norm at most `‖μ‖`,
  then the class of `x * y` has norm at most `‖μ‖` times the product of the
  norms of the classes of `x` and `y`. The ultrametric inequality on the
  finite product bounds the double sum from `coefficientSum_mul`.
* `norm_coefficientSection_tensorLeft_le`: the left factor is bounded.
* `exists_norm_coefficientSection_tensorRight_le`: bounded coefficient lifts
  in `P` make the right factor bounded.
* `exists_norm_tensorComparison_le`: the comparison is bounded, using the
  bounds of `d.comparison φ`, of `(d.pullback φ).baseMap` on the generators,
  and `tensorComparison_mul`.

`isUltrametricDist_submoduleQuotient` shows that the quotient of an
ultrametric seminormed group by a submodule is ultrametric.

### The normed model

`bijective_tensorComparison_of_generators` assumes bounded coefficient lifts
for `c`, a closed coefficient kernel, and a nonzero scalar `μ` whose norm
bounds coefficients of all products of generators. It equips `M` with the
norm `‖m‖ = ‖μ • coefficientSection m‖`. This is the norm induced by an
additive bijection onto the quotient, which is a normed group because the
kernel is closed. The norm is submultiplicative by
`norm_coefficientSection_mul_le`. It is
ultrametric, and complete because the additive bijection is an isometry onto
the complete quotient. With the scalar algebra structure given by
`tensorLeft ∘ algebraMap K d.algebra`, it is a normed `K`-algebra. The three
boundedness hypotheses of the pushout criterion follow from the bounds above,
with `ι` the identity.

### The three remaining inputs

The proof provides the three hypotheses for every complete ultrametric
coefficient field. It splits on whether every scalar has norm at most one.

* Closed kernel: `PresentedStrictAffinoidAlgebra.isClosed_submodule_pi`
  proves that every submodule of `Fin m → P` is closed. For a nontrivially
  valued field this is `isClosed_submodule_pi_of_noetherian_banach` from
  `ClosedSubmodulesBanach`, using the published Noetherianity of actual
  presented quotients from `TateNoetherian`. For a field whose scalars all
  have norm at most one, `one_le_norm_pi_of_scalar_norm_le_one` shows that
  nonzero tuples have norm at least one. It uses Worker 56's published
  `one_le_norm_of_scalar_norm_le_one`. Distinct points therefore have
  distance at least one, and `isClosed_pi_of_scalar_norm_le_one` shows that
  every subset is closed.
* Bounded lifts: `BoundedAlgHom.exists_coefficientMap_preimage_norm_le`. In
  the nontrivially valued case this is the published open-mapping bound
  `coefficientMap_exists_preimage_norm_le` from `FiniteBanachModule`. In the
  other case every tuple has norm at most one
  (`norm_pi_le_one_of_scalar_norm_le_one`, from the published
  `norm_le_one_of_scalar_norm_le_one`) and every nonzero element has norm at
  least one, so the constant one works.
* Scale: `exists_structure_scale` chooses coefficients of all products of
  generators. In the nontrivially valued case, `μ` is a scalar whose norm
  exceeds the sum of their norms. In the other case `μ = 1`, because all
  tuples have norm at most one.

`finiteRationalTensorComparison` combines these three inputs with
`bijective_tensorComparison_of_generators`. When `n = 0`, the quotient,
the tensor product and the norm are all zero, and the same argument applies.

### Implementation note

The published ring instance on `d.algebraicBaseChange φ` is elaborated as
`id inferInstance`. With it, rewriting by `Finset.mul_sum` or
`Finset.sum_mul_sum` on this type fails to match instance paths. The private
lemmas `mul_sum_fin` and `sum_mul_sum_fin` restate these two identities over
an arbitrary commutative ring, so their instance paths are those found by
instance search. For the same reason the proof never puts a `Module`
instance on the tensor product. Instead it uses the additive section above.

## Provenance

The target is a derived specialization of Berkovich, *Non-archimedean
analytic spaces* (Trieste lectures, 2009), Definition 2.1.7 and Fact
2.1.8(iii), printed/PDF p. 8, with the rational quotient equations of
Exercise 2.2.2(ii), printed/PDF p. 9. Those passages identify the ordinary
and completed tensor products for a finite module. The Lean proof follows
the suggested route of a separated complete quotient norm on the finite
tensor product. It does not construct completed tensor products or invoke a
finite Banach equivalence. Instead it obtains the inverse from the bounded
pushout property of the constructed pulled-back rational quotient. No
flatness, exactness, bounded inverse or bijectivity is assumed.

Registered source: `berkovich-2009-trieste-analytic-spaces`, retained PDF
SHA256 `8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
