# Arithmetic equivariance of the full logarithm

Let `F` and `E` be fields in independent universes with an `F`-algebra structure
on `E`. The acting group is the actual group `E ≃ₐ[F] E`. No cyclicity,
normality, finiteness of the extension, or number-field hypothesis on `F` is
required. The constructions involving coordinate sum and the logarithmic
lattice additionally assume `NumberField E`.

## Arithmetic actions and the logarithm

`fullLogPermutation F E` is a group homomorphism to the real linear
automorphisms of `InfinitePlace E → ℝ`. Its formula is

`(fullLogPermutation F E g x) w = x (g⁻¹ • w)`.

It uses Mathlib's arithmetic action on actual infinite places, under which
`(g • w) a = w (g⁻¹ a)`. Inverse precomposition gives the homomorphism law
in the stated order. `fullLogPermutation_apply` records the exact formula.
`infinitePlace_mult_smul` says that this action preserves the multiplicity
of each infinite place; its proof uses preservation of the real-place predicate.

The action on actual ring-integer units is Mathlib's
`Units.mulDistribMulActionRight`, induced from the arithmetic action on
`𝓞 E`. The file installs this existing action as a local instance.
Consumers writing the same unit-action notation can install the same instance.
`unit_smul_coe` proves that its field value is exactly `g (x : E)`.

`fullLogEmbedding_equivariant` proves that the full normalized logarithm
intertwines these two actions. At a place `w`, both sides equal
`mult w * Real.log (w (g (x : E)))`: multiplicity is invariant, and
evaluation at `g⁻¹ • w` precomposes by `g`. This proof requires only the
field and algebra assumptions; it makes no finiteness assumption on the
set of places.

## Hyperplane and lattice stability

For a number field `E`, `infiniteLogSum_permutation` proves that the finite
sum of all coordinates is unchanged, using the bijection of places induced
by `g⁻¹`. Consequently `fullLogPermutation_mem_hyperplane` is the equivalence
between membership of a vector and of its image in the sum-zero hyperplane.

`fullLogHyperplaneAut F E` restricts the permutation homomorphism to real
linear automorphisms of `fullLogHyperplane E`. Its inverse is the restriction
for `g⁻¹`; the inverse and homomorphism laws follow from those of the full
permutation. `fullLogHyperplaneAut_apply` identifies its underlying full
coordinate vector. `fullLogEmbeddingToHyperplane_equivariant` then follows
from the full-coordinate equivariance by subtype extensionality.

`fullLogUnitLattice_invariant` says that this hyperplane action carries every
element of the actual logarithmic unit lattice into that lattice. The proof
uses `mem_fullLogUnitLattice` to choose a unit representing the lattice
element and applies equivariance: its image is the logarithm of the
arithmetically transformed unit. Applying the same result to `g⁻¹` gives
stability in both directions.

## Provenance and scope

This is the infinite-place specialization of Milne, *Class Field Theory*,
v4.03 (2020), Chapter VII, proof of Proposition 3.1, printed p.209
(PDF p.218). That passage defines the inverse-precomposition action on
real place coordinates and states that the full logarithm commutes with
the group action. The multiplicity-weighted logarithm imported from
`FullLogEmbedding` implements the source's normalized archimedean
absolute values. The preceding passage also supplies the full image
lattice, implemented in `FullLogUnitLattice`.

The linear-equivalence packaging, multiplicity lemma, restricted action,
and image-stability proof are internal adapters of those formulas and
Mathlib's existing arithmetic actions. This contribution establishes no
cohomology or Herbrand formula, quotient action on units modulo torsion,
or comparison of the integral permutation representation with the real
coordinate representation. Those remain separate steps.
