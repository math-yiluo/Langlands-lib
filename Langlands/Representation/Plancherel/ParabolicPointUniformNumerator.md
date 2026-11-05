# The uniform regular numerator for actual rational-point parabolics

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. It removes
the structural hypotheses of `CompactIntertwiningUniformNumerator` for the
actual rational-point data of the host statement. It then combines the uniform
numerator with the published weak-regularity and local-divisibility theorems.

## Opposite Iwahori bases of dynamic subgroups

`exists_dynamic_oppositeIwahoriContractionBasis`. Let `k` be a nonarchimedean
local field and `G` a smooth affine separated group scheme over `k`. Give
`G(k)` its rational-point topology, and assume it is locally compact and
nonarchimedean. Then for every cocharacter `χ` there is a point `g` of the
centralizer `Z(χ)(k)` such that `U(χ)(k)`, `Z(χ)(k)` and `U(χ⁻¹)(k)` have the
published `Jacquet.HasOppositeIwahoriContractionBasis` for `g`.

The proof is the argument of the published `rationalOppositeIwahoriBasisStatement`,
which is stated only for standard cocharacters of a split torus; here it is
applied to an arbitrary cocharacter. Its inputs are all published:
closedness of both dynamic radicals (`isClosed_rationalPoint_subgroup` with the
affine dynamic representatives), the central contracting point
`exists_central_contractingPoint`, normalization of both radicals by the
centralizer, uniqueness of the factorization
`dynamic_opposite_factorization_unique`, and the open opposite cell
`opposite_cell_mem_nhds_one`, after identifying the point topology with the
scheme-chart topology (`rationalPointTopology_eq_rationalSchemeTopology`). They
are fed into the published abstract criterion
`hasOppositeIwahoriContractionBasis_of_contraction`.

## Parabolic root presentations

Let `r` be a parabolic root presentation of `p : P ⟶ G` with Levi `l` and split
component `a`. Let `λ` be the published split-component cocharacter
`groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ p`.
`parabolicOppositeRadicalPoints r` is the subgroup `U(λ⁻¹)(k)` of rational
points of the opposite dynamic radical.

- `parabolicLevi_le_normalizer_oppositeRadicalPoints`: the literal Levi point
  subgroup `parabolicLeviPointSubgroup p l` normalizes it.
- `eq_one_of_mem_parabolic_of_mem_oppositeRadicalPoints`: it meets the actual
  parabolic points `range p` only in `1`.
- `parabolicLevi_exists_oppositeBasis`: if `G` is smooth and separated and `n`
  is any supplied geometric unipotent radical, then the actual radical points
  `range (n ≫ p)`, the literal Levi points and `parabolicOppositeRadicalPoints r`
  have an opposite Iwahori contraction basis for one point `g`.

The published equalities `range_comp_radical_eq`,
`levi_eq_splitComponentCocharacter` and `parabolic_eq_splitComponentCocharacter`
identify the radical, Levi and parabolic with `U(λ)`, `Z(λ)` and the dynamic
parabolic `P(λ)`. The published `centralizer_inverseCocharacter` and
`eq_one_of_mem_opposite_unipotent_of_mem_parabolic` give normalization and the
trivial intersection.

## The host-level numerator and rationality

The section `Host` takes the actual data of the host statement: presentations
`r` and `r'` with the same Levi composite (`hLevi : l ≫ p = l' ≫ p'`) and the
same split component, geometric radicals `n` and `n'`, and subgroups `Ppt`,
`Upt`, `U'pt` of `G(k)` given with their defining equalities to the actual
point subgroups `range p`, `range (n ≫ p)` and `range (n' ≫ p')`. It also takes
all compact-picture, measure and squared-modulus data of the published
`parabolicLevi_standardCompactRationalOn_of_dominated`.

`parabolicLevi_exists_uniform_standardCompactOperator_numerator`: for an
admissible finite-length representation `π` of the literal Levi point subgroup
and any parameter set `Ω` of full convergence, there is one nonzero `b` in the
concrete regular algebra of the full rational norm family such that
`χ ↦ b(χ) •` (the actual `standardCompactOperator`) satisfies
`IsPolynomialOperatorOn Ω`. The proof applies `parabolicLevi_exists_oppositeBasis`
to `r, n` (source) and to `r', n'` (target). Here the target Levi is rewritten
to the source Levi by `hLevi`. Local compactness of `U'pt` follows from
closedness. The proof then applies
`exists_uniform_standardCompactOperator_numerator`.

`parabolicLevi_standardCompactRationalOn_of_dominated_of_finiteLength`: on an
open `Ω` of full convergence with the published local integrable domination
`CompactIntegralLocallyDominatedOn`, the actual compact standard operator
satisfies the published `StandardCompactRationalOn`. This is the published
`parabolicLevi_standardCompactRationalOn_of_dominated`. Its divisibility input
is the published `rationalUnramifiedLocalHypersurfaceDivisibility`, and its
numerator input is the theorem above.

## Scope and provenance

The module does not prove full convergence, local domination, radical
unimodularity or the squared-modulus compatibility. These remain explicit
inputs, exactly as in the published weak-regularity theorem. It does not choose
the region or prove the host theorem. All steps are internal compositions of
the published Library declarations named above and of
`CompactIntertwiningUniformNumerator`; no literature theorem replaces a proof.
