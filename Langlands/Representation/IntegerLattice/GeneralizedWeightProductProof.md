# All-integer ordered products on actual generalized-weight blocks

This file proves
`Langlands.commutingTupleGeneralizedWeightProduct :
Langlands.CommutingTupleGeneralizedWeightProductStatement` in arbitrary
carrier universe `u`. For every natural rank, finite-dimensional complex
carrier, actual commuting invertible tuple `A`, unit label tuple `c` and
integer lattice point `n`, the actual restricted action has all three ordered
product formulas in the published statement. The tuple, block, action, units,
normalized differences and coordinate character are the unchanged published
constructions. Nilpotence, a basis and a decomposition are not caller inputs.

## Ordered generator reconstruction

`representation_eq_ordered_product` reuses the published generator
reconstruction for every lattice representation. The generator unit values
commute, and therefore so do their integer powers. The proof identifies the
noncommutative finite product with the product over `List.finRange d`, whose
entries are distinct and exhaust the coordinates. Mapping the unit coercion
through the list product gives the increasing `List.ofFn` product. Each factor
is first raised to its genuine integer power in the unit group and then
coerced to an endomorphism. Applying this result to the actual restricted
representation proves
`generalizedWeightBlockRepresentation_eq_ordered_product`, the first target
identity. This comparison does not require finite dimension.

## Scalar normalization at every integer exponent

The scalar unit in the definition of `normalizedBlockGenerator` commutes with
every endomorphism unit, by centrality of the scalar algebra map. The private
helper `scalar_unit_mul_zpow` uses `Commute.mul_zpow` and the scalar unit
homomorphism to separate scalar and operator powers for every integer
exponent. Cancellation of the nonzero scalar power then proves
`generalizedWeightBlockGenerator_zpow_eq_smul`: each original block-generator
power equals the corresponding complex scalar power times the normalized-unit
power. Negative and mixed-sign exponents require no extra case split.

The private list induction `list_prod_smul` collects the scalar factors
without changing the endomorphism order. `List.prod_ofFn` and
`coe_coordinateCharacter` identify the resulting scalar with the actual
coordinate character. This gives
`generalizedWeightBlockRepresentation_eq_normalized_product`, the second
target identity, again without finite-dimensionality.

## Actual nilpotence and finite binomial expansion

The proof imports
`Langlands.IntegerLattice.normalizedGeneratorDifference_isNilpotent` from
`Langlands.Representation.IntegerLattice.GeneralizedWeightBlockBasisProof`.
This published helper proves nilpotence of each actual normalized difference
on the actual generalized-weight intersection. Its restriction argument is
established before the common basis is chosen, so the present proof requires
no choice or use of such a basis.

The private helper `nilpotent_submodule_pow_ambient_finrank` adapts this
nilpotence to the precise truncation in the target. Given a nilpotent
endomorphism of any submodule `W`,
`Module.End.ker_pow_le_ker_pow_finrank` shows that its power at
`Module.finrank ℂ W` kills every vector. `Submodule.finrank_le` and
`pow_eq_zero_of_le` extend vanishing to the exponent `Module.finrank ℂ V`.
This is a generic dimension argument; the actual-block nilpotence input is
supplied by the imported theorem.

The private helper `block_binomial_product_of_bound` applies the published
all-integer theorem `Langlands.renardCIIIUnipotentBinomial.1` to each actual
normalized unit. Its difference from the identity is definitionally the
actual `normalizedGeneratorDifference`. Substituting the resulting finite
sum for each factor in the normalized ordered product yields the third
identity. The coefficients are exactly `Ring.choose (n.toAdd i : ℂ) k`, and
the bound is the ambient dimension, as in the unchanged target. The final
theorem introduces all the inputs, collects the first two identities, and
uses this binomial adapter with the proved ambient bound for every coordinate.

## Degenerate cases

No step assumes a positive rank, a nonzero carrier or a nonzero block. At rank
zero the ordered lists are empty, their products are identity endomorphisms,
and the coordinate character is one. For a zero carrier the ambient dimension
is zero; the kernel argument still proves the zeroth power vanishes on the
zero block, where the identity endomorphism is zero. The published binomial
theorem permits bound zero, so its empty sums agree with the actual unit powers
in this zero endomorphism ring. Zero blocks at other labels are also included,
with no cancellation of an endomorphism or assumption that it is nonzero.

## Source and provenance

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix C.III, printed
pp.279–280 / one-based PDF285–286, especially the three lines of the display
for `A_j(n)` on PDF286. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The source pages were read directly, including visual inspection of the
PDF286 display. The source works in a common triangular basis. The present
proof instead uses the intrinsic block representation, its published
nilpotence helper, and the existing all-integer binomial theorem. The ordered
list formulation and ambient-dimension truncation are derived details already
specified in the target, rather than additional claims of a minimal bound.

The registered supplementary 2010 errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. The correction to old p.322 line -4 groups the entire
scalar-times-unipotent factor inside its integer power. The 2026 display
already has these parentheses. All operator powers here are genuine unit
integer powers before coercion, preserving that grouping. This result proves
the three product identities; decomposition, weight support and assembly of a
global basis remain separate assertions.
