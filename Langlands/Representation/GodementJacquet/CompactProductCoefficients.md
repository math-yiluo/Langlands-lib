# Uniform compact expansions of product-induced pairings

This is internal coefficient infrastructure for the Godement–Jacquet induction
argument. It combines the actual tensor coefficient expansion with the finite
sampled Schwartz expansion of a uniformly locally constant family. It does not
assert convergence, a noncompact integration formula, rational continuation or
generation of the matrix-zeta value module.

For an admissible finite family of complex representations with cofinal compact
open subgroups, `exists_uniform_compact_productCoefficient_expansion` treats
locally constant families of smooth tensor functionals and tensor vectors on an
arbitrary compact topological space. Their pairings, as functions of the product
group, are uniformly locally constant in the compact parameter. Compactness
supplies compact support. `exists_finite_schwartz_expansion` therefore writes the
family as a finite sum of Schwartz functions times sampled coefficient functions.
Each sampled coefficient belongs to the actual bi-smooth coefficient space,
because admissibility makes every tensor vector smooth. Applying
`exists_finite_productCoefficient_expansion` to every sample and reindexing the
finite dependent sum by `Fin N` gives the conclusion. Scalar coefficients are
absorbed into the Schwartz functions. All finite data are chosen before both
the compact parameter and the group element; the factor functionals are actual
elements of the factors' smooth algebraic duals.

The result is derived entirely from the named tensor, smooth-vector,
and locally constant function APIs. No coefficient expansion is a premise.

`compactProductPairingKernel` is the actual complex bilinear function
`h(k)(blockTensor σ(m)(f(k')))`, where the dual-valued and tensor-valued sections
have the same positive half-modulus covariance as normalized induction. There
is no complex conjugation or contragredient replacement of a coefficient family.

For supplied p-adic topological data and any compact open subgroup `K`,
`exists_compactProductPairing_expansion` applies the uniform theorem on `K × K`.
Both section evaluations are locally constant by
`Induction.eval_isLocallyConstant`; their compositions with the two continuous
subtype projections remain locally constant. Cofinal compact open subgroups in
each block are obtained from `compactOpenSubgroupBasis` and the supplied
nonarchimedean and local compactness instances. Thus the result requires only
admissibility of the actual block representations and compactness of `K`, and
chooses Schwartz weights, smooth factor functionals and factor vectors before
both compact variables and the Levi variable. No Iwasawa factorization is needed
for this finite expansion.

`exists_compactProductCoefficientFormula` specializes
`exists_compactInducedCoefficientFormula` to `B.blockTensor σ`, using
`FiniteTensor.isAdmissible_external` to discharge tensor admissibility. In
positive ambient rank it gives one compact open Iwasawa subgroup and one Borel
Haar probability measure, chosen before the block representations on the fixed
family of carriers. For every admissible block family it gives an actual
equivalence from the smooth contragredient of its normalized product induction
to the normalized induction of the tensor representation's smooth
contragredient. The equivalence is chosen before all functionals, sections and
group elements; their actual matrix coefficient equals the stated compact
integral, and that integral is integrable. This is a coefficient formula, without
noncompact matrix-zeta convergence or a product-generator assertion.
