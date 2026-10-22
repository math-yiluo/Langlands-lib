# Total projectors from finite fixed-level strata

Worker 173 supplies a total equivariant endomorphism from finite fixed-level
strata and a supplied family of compact-isotypic component maps. The component
maps, their projector properties, and the finiteness of the fixed-level strata
are explicit inputs. This is internal infrastructure derived from published
Library constructions and elementary finite-sum algebra, with no new assertion
attributed to the original literature.

## Algebraic range and kernel of a pointwise sum

The first two theorems are in namespace `Langlands`. They work over an arbitrary
commutative ring `R`, a group `G`, and an `R`-module `V`, with independent type
universes. Fix a representation `ρ`, an arbitrary index type, and a family
`e` of actual equivariant endomorphisms. Assume:

- for every vector `v`, only finitely many `e i v` are nonzero;
- every component is idempotent: `e i (e i v) = e i v`;
- distinct components are orthogonal: `e i (e j v) = 0` when `i ≠ j`.

`pointwiseFiniteSum_range` proves

\[
\operatorname{range}\Bigl(\sum_i e_i\Bigr)
=\sup_i\operatorname{range}(e_i).
\]

The sum is the published `pointwiseFiniteSum`. For the forward inclusion,
evaluate at a vector and express its finite-support sum as a finite sum of
vectors in the supremum of the component ranges. For the reverse inclusion,
the published `pointwiseFiniteSum_component` identity shows that the total
fixes each vector in a component range, placing that vector in its own range.

`pointwiseFiniteSum_ker` proves

\[
\ker\Bigl(\sum_i e_i\Bigr)=\inf_i\ker(e_i).
\]

If the total kills a vector, applying a component and using the published
`component_pointwiseFiniteSum` identity shows that this component kills it.
Conversely, if all components kill the vector, their pointwise sum is zero.
Both equalities are in the actual complete lattice of subrepresentations.

## Finite support from compact open subgroups

The remaining declarations are in namespace `Langlands.CompactCoefficientClass`.
Assume `G` is a nonarchimedean group with a topology and is weakly locally
compact. The group universe `uG`, representative-carrier universe `uV`, and
ambient-carrier universe `uW` are independent. Let `A` be an arbitrary smooth
complex representation of `G` and let `P c` be an actual equivariant
endomorphism of `A` for each existing compact-coefficient class `c`.

`finiteSupport_of_finite_fixedStratum` assumes that
`annihilatorSubrepresentation c A ≤ (P c).ker` for every class, and that the
existing set `fixedStratum K.toSubgroup` is finite for every compact open
subgroup `K`. It concludes that `c ↦ P c v` has finite support for every `v`.
There is no admissibility or finite-length assumption on `A`. Neither
idempotence nor a range identification is needed for this support theorem.

The proof first obtains an open subgroup fixing `v` from smoothness. The
published `compactOpenSubgroupBasis` supplies a smaller compact open subgroup
`K`, which also fixes `v`. The published
`apply_eq_zero_of_annihilator_le_ker` shows that `P c v = 0` whenever `c` has
no nonzero `K`-fixed vector. Thus all nonzero terms lie in the finite stratum
for `K`, and `finiteSupport_of_finite_stratum` applies. The compact open
subgroup can depend on the vector.

## The total endomorphism and its laws

`totalProjectorOfFiniteStrata P hker hstrata` is the actual equivariant
endomorphism formed by `pointwiseFiniteSum` with the just-proved finite support.
Its construction uses only the kernel containments and fixed-stratum finiteness.
It introduces no additional choice of a representative for any class.

The following laws also assume that the supplied components are idempotent
and pairwise orthogonal:

- `totalProjectorOfFiniteStrata_idempotent` says that the total applied twice
  equals the total applied once, for every vector.
- `totalProjectorOfFiniteStrata_range` additionally assumes
  `(P c).range = isotypicSubrepresentation c A` for every class. It identifies
  the total range with the published `totalIsotypicSubrepresentation A`, at
  the same representative universe `uV`.
- `totalProjectorOfFiniteStrata_ker` additionally assumes
  `(P c).ker = annihilatorSubrepresentation c A` for every class. It identifies
  the total kernel with the published `totalAnnihilatorSubrepresentation A`.

The first is the published idempotence theorem for pointwise sums. The other
two apply the algebraic range/kernel theorems above and rewrite the component
subrepresentations using the supplied equalities. All finiteness and component
existence hypotheses remain explicit. This pair proves neither compact
coefficients of the total range nor that every compact-coefficient object is
fixed by the total. Those are separate inputs needed for the final
product-Levi decomposition.
