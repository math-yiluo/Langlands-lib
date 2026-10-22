# Finite-image and unramified reductions

`Langlands.Weil.RepresentationStructure` conjoins two proposition definitions,
`UnramifiedReduction` and `FiniteImageExtension`. Both concern actual
finite-dimensional complex representations on actual normed complex vector
spaces. They keep the group and representation-space universes independent.
Continuity uses the usual operator topology through
`LinearMap.toContinuousLinearMap`. These are statements, not proved theorems.

## Unramified reduction

`UnramifiedReduction` takes a topological group `W` and a surjective
homomorphism `d : W →* Degree`, where `Degree` is the existing multiplicative
notation for the additive integers. Its kernel is open, compact and
nonarchimedean with its inherited topology. The kernel is the specified inertia
subgroup in this generic integer-extension formulation. No Frobenius lift,
matrix root, finite quotient or character correction is supplied as data.

For every continuous representation `rho`, the first conjunct asserts the
existence of continuous representations `tau` and `sigma` on the same space.
Here `tau` is trivial on the degree kernel, every operator of `tau` commutes
with every operator of `rho`, `sigma(w) = rho(w) * tau(w)`, and `sigma` has
finite image. Thus the existence of the required commuting unramified
correction is the conclusion, not a hypothesis. For a general representation
the correction need not be scalar.

If `rho` is irreducible in Mathlib's actual representation-theoretic sense,
the second conjunct asserts that `rho` is an unramified continuous scalar
twist of a continuous irreducible finite-image representation on the same
space. It uses the existing `Langlands.twist`. The character takes values in
complex units; it is not required to be unitary. Equality on the same
underlying space is appropriate: twisting can be undone without changing that
space. No isomorphism-class witness is assumed.

For the same irreducible `rho`, the final equivalence says that its image is
finite exactly when its determinant has finite order as a character:
there exists one positive integer `n` for which
`det(rho(w))^n = 1` for every `w`. This criterion is deliberately restricted
to irreducibles. A sum of an infinite-order character and its inverse can have
trivial determinant and infinite image.

The criterion is a derived consequence of the irreducible twist reduction.
If `rho = chi ⊗ sigma` with `sigma` of finite image and dimension `r > 0`,
then `det rho = chi^r * det sigma`. A finite-order determinant forces the
scalar character to have finite order, because complex roots of a fixed
positive order form a finite set. The product representation then has finite
image. Conversely, determinants of a finite image have finite order.

## Finite-image extension

`FiniteImageExtension` takes a compact Hausdorff nonarchimedean group `Gamma`
and a continuous surjection `phi` to the existing genuine profinite completion
of the integers. It uses the already accepted `Pullback phi` and its actual
projection, with the existing topology in which integer degree is discrete.
For a continuous representation `rho` of that pullback, finite image is
equivalent to existence of a unique continuous representation `sigma` of
`Gamma` whose restriction along the projection is `rho`.

This is the generic structural formulation of the finite-image/Galois-type
bridge. It does not assert the same fact for an arbitrary dense homomorphism.
The integer pullback and compact nonarchimedean ambient group are essential
parts of the statement.

For context, a proof can pass from the open kernel on inertia to a finite
inertia quotient, normal in the ambient group by density. After this quotient
the problem is an extension of the profinite integers by a finite group.
A lift of the integer generator defines a procyclic section, and a
finite-image representation on its integer subgroup extends to that section.
Density gives uniqueness. In the other direction, a continuous complex
representation of a compact nonarchimedean group has finite image. This
paragraph explains the derived generalization; it is not a Lean proof.

To specialize this statement to the absolute Galois group of a local field,
the actual continuous surjective residue map and its normalized
finite-field-Galois/profinite-integer identification are still required.
Those arithmetic constructions are owned by the existing tasks
`5c4b0ffa-799b-46ec-a1f7-bd3132abe585` and
`0e7e34d9-8c49-4853-85d7-ab669c8b47b9`, and the local assembly belongs to
`503968de-16f8-4f63-ba13-b5e167e11dce`. No identification of the generic
ambient group or pullback with those field-theoretic objects is asserted here.

## Declaration-level original-source correspondence

| Declaration/clause | Original locator | Relationship |
| --- | --- | --- |
| `UnramifiedReduction`, commuting correction | Henniart 1980, section 2.3, Corollary 2, p. 158/PDF 5, and proof in sections 2.4-2.6, pp. 159-160/PDF 6-7 | The conclusion is the source's unramified representation commuting with the given representation and making its product finite-image. The integer-extension setting isolates the structural hypotheses used in the proof. |
| `UnramifiedReduction`, irreducible twist | Henniart 1980, section 2.3, Corollary 3, p. 158/PDF 5, proof p. 159/PDF 6; Tate, section 2.2.1, p. 10/PDF 19 | Tate explicitly describes this as the general fact for an extension of the integers by a profinite group. The target exposes the arbitrary unramified complex character rather than choosing an exponent of the norm character. |
| `UnramifiedReduction`, determinant criterion | Same reduction passages; Tate section 2 opening, p. 9/PDF 18, for the determinant quasicharacter | This is an explicitly derived finite-order consequence, with the positive dimension provided by irreducibility. It is not attributed to those passages as a separately numbered theorem. |
| `FiniteImageExtension` | Henniart 1980, section 2.1, p. 158/PDF 5; Tate, section 2.2, p. 10/PDF 19 | Both sources identify Galois type with finite image for local Weil representations. This statement generalizes the structural argument to the accepted integer pullback over a profinite ambient group. It quantifies the extension and its uniqueness, without assuming either. |
| `RepresentationStructure` | The preceding rows | A conjunction of the two exact targets; no additional mathematical assertion is hidden in the packaging. |

Read retained originals:

- Guy Henniart, *Representations du groupe de Weil d'un corps local*,
  L'Enseignement Mathematique (2) 26 (1980), 155-172.
  Literature ID `henniart-1980-weil-representations`,
  SHA-256 `451a8bd31a58be9bf5ce49588503c2d229b1a73bf3e65ae0c7b2f491c1c4e017`.
  `C:/Central-Library/Henniart--Representations du groupe de Weil dun corps local--1980.pdf`.
- John Tate, *Number theoretic background*, Corvallis Part II,
  Proc. Sympos. Pure Math. 33 (1979), 3-26.
  Literature ID `tate-1979-number-theoretic-background`,
  SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  `C:/Central-Library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`.

## Exact dependencies

- `Langlands.Representation.Twist.Definitions`:
  artifact `c83db975-8b79-4fbb-9901-2db836910a0a` version 1.
  Uses `Langlands.twist` on the unchanged representation space. No twist
  definition or accepted twist-law target is duplicated.
- `Langlands.Weil.Pullback`:
  artifact `993e4326-4390-4fc8-94a7-82829061b1ea` version 1.
  Uses `Degree`, `ProfiniteIntegers`, `Pullback`, and `projection`, with their
  actual groups and topologies.
- Prepared environment `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` version 1:
  Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
  Mathlib supplies `Representation`, its genuine `IsIrreducible` predicate,
  endomorphism determinants, complex topology, compactness and nonarchimedean
  group structure.

Neither the staged continuity target nor the unfinished parameter-definition
framework is imported. The topological bridge and generic Weil algebraic laws
may be used in a later proof after their exact accepted statements and proofs
are verified. Statement compilation and fingerprints do not prove the
reduction or extension assertions.
