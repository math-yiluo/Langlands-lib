# Finite-coordinate statements for affine point topologies

Author: Worker 105.

Source: Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), Proposition 2.1 and its proof, printed page 2. Registered
literature ID `conrad-2011-weil-grothendieck-adelic-points`, SHA256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`, original
`/home/taskhub/central-library/Conrad--Weil and Grothendieck approaches to adelic points--2011.pdf`.

The declarations are in namespace
`Langlands.AlgebraicGeometry.PointTopology`. They are proposition-valued
`def`s specifying proof targets, not proofs or assumed fields of a topology.
They use the actual algebra-map carrier `AlgPoint R A S` and its evaluation
topology from `Langlands.AlgebraicGeometry.PointTopology.Affine`.

## Targets and exact hypotheses

Let `R`, `A`, and `S` be commutative rings, with `R`-algebra structures on
`A` and `S`. Only `S` has a topology, and its ring operations are continuous.
No topology on `R` or `A` is assumed.
Each of the four declarations explicitly binds `IsTopologicalRing S`, so the
continuity hypothesis remains part of its elaborated type.

- `FiniteCoordinateEmbedding R A S` asserts that for every natural number
  `n` and every family `a : Fin n → A` generating `A` as an `R`-algebra,
  the actual evaluation map `p ↦ (i ↦ p (a i))` embeds the point space
  into `S^n` with the product topology. The hypothesis is exactly
  `Algebra.adjoin R (Set.range a) = ⊤`; the case `n = 0` is included.
- `FiniteCoordinateClosedEmbedding R A S` adds only Hausdorffness of `S`
  and asserts that this embedding has closed image. The family may have
  infinitely many polynomial relations; finite presentation is not assumed.
- `AffineLocalCompactness R A S` assumes `S` Hausdorff and locally compact,
  and asserts that finite generation of `A` as an `R`-algebra implies local
  compactness of the actual point space. It uses `Algebra.FiniteType R A`.
- `AffineCoordinateProperties R A S` groups these three targets, quantifying
  the additional Hausdorff and local-compactness instances only in the two
  conclusions that need them.

## Relation to the source and remaining scope

For `S = R`, these are the finite-coordinate comparison and
local-compactness conclusions in the proof of Proposition 2.1. For arbitrary
`S`, the same finite-generator argument evaluates coefficients through
`algebraMap R S`; these coefficients are fixed constants, so continuity of
an `R`-action or of a topology on `R` is unnecessary. This is the explicit
relative form of the source argument, rather than a new choice of topology.
A proof still has to establish the targets. The algebraic-map/actual-scheme
point equivalence is the one constructed in the imported module.

The generator comparison gives agreement for every finite coordinate
presentation. The uniqueness from all of Conrad's functorial axioms,
products and fibre products, closed-immersion maps, and coefficient-change
embeddings remain separate obligations. This focused statement unit does
not claim Proposition 2.1 or the whole-paper task complete.
