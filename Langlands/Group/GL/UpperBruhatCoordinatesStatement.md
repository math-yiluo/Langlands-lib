# Actual upper Bruhat cell coordinate homeomorphisms

Author: Worker 779.

`Langlands.GeneralLinear.UpperBruhatCoordinatesStatement.{u}` is a closed,
transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperBruhatCoordinatesStatement`. This module states the
proposition; it proves nothing about it. The module imports the published
`Langlands.Group.GL.UpperBruhatCells` unchanged and uses only its actual
constructions and those it imports.

## The proposition

The proposition quantifies over every field `K : Type u` and every topology
`TopologicalSpace K` such that `IsTopologicalDivisionRing K` and `T2Space K`
hold. It also quantifies over every natural rank `n`, including `n = 0`, and
every permutation `w : Equiv.Perm (Fin n)`. Throughout, all names are in
`Langlands.GeneralLinear`:

| Symbol | Lean term |
| --- | --- |
| `B` | `upperTriangularSubgroup n K`, invertible upper triangular matrices with arbitrary invertible diagonal |
| `U` | `upperUnipotent n K`, upper triangular matrices with all diagonal entries one |
| `N` | `permutationUnipotentMinus n K w` |
| `p` | `permutation n K w` |
| `C` | `UpperBruhatCell n K w`, the subtype of `upperBruhatCell n K w` |

For each such `K`, `n` and `w`, the proposition asserts the conjunction of exactly
the following two coordinate assertions:

```lean
(∃ eB : (upperTriangularSubgroup n K × permutationUnipotentMinus n K w) ≃ₜ
    UpperBruhatCell n K w,
  ∀ x, eB x = upperBruhatCellMap n K w x) ∧
∃ eT : (upperUnipotent n K × (Fin n → Kˣ) × permutationUnipotentMinus n K w) ≃ₜ
    UpperBruhatCell n K w,
  ∀ x, (eT x).val =
    x.1.val * permutation n K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val
```

1. There is a homeomorphism `eB : B × N ≃ₜ C` whose value at every argument is
   the published `upperBruhatCellMap n K w`. By the definition of that map
   (its evaluation lemma is `upperBruhatCellMap_val`), the underlying group
   element of `eB (b, v)` is `b * p * v`.
2. There is a homeomorphism `eT : U × (Fin n → Kˣ) × N ≃ₜ C` such that for
   every `x`, the underlying group element of `eT x` is
   `x.1.val * p * Iwasawa.diagonalUnits x.2.1 * x.2.2.val`.

Both conjuncts require the stated multiplication formula at every argument.
An abstract homeomorphism between the same spaces would not satisfy them.
`≃ₜ` is Mathlib's `Homeomorph`, an equivalence that is continuous in both
directions.

## Conventions

The group is `Langlands.GeneralLinear n K`, Mathlib's
`Matrix.GeneralLinearGroup (Fin n) K` of invertible matrices. The published
permutation matrix has entry `if w j = i then 1 else 0` at `(i, j)`
(`permutation_entry`), so it sends `e_j` to `e_(w j)`. Conjugation
`p * g * p⁻¹` has entry `g (w⁻¹ i) (w⁻¹ j)` (`permutation_conjugate_entry`).
The permutation is not reversed or inverted anywhere in the statement.

`N` is the published `U ∩ {g | p * g * p⁻¹ ∈ lowerUnipotent n K}`, which is
Shalika's `U_w⁻ = U ∩ w⁻¹ Ubar w`. By the published
`mem_permutationUnipotentMinus_iff_entries`, its elements are exactly the
elements of `U` whose entry at `(i, j)` vanishes whenever `w i < w j`. The cell
`C` is the subtype of the actual set
`{g | ∃ b₁ ∈ B, ∃ b₂ ∈ B, g = b₁ * p * b₂}`.

`Iwasawa.diagonalUnits` is the published field-general group homomorphism
`Langlands.GeneralLinear.Iwasawa.diagonalUnits`. It sends `d : Fin n → Kˣ` to
the invertible diagonal matrix with diagonal entries `d i`, and it uses no
valuation.

The domain of `eT` is Lean's right-associated product
`U × ((Fin n → Kˣ) × N)`. Thus `x.1 ∈ U` is the left unipotent factor,
`x.2.1 : Fin n → Kˣ` is the torus coordinate and `x.2.2 ∈ N` is the right
factor. Matrix multiplication associates to the left, giving
`((x.1 * p) * diagonalUnits x.2.1) * x.2.2`. The torus factor stands to the
right of `p`, between `p` and the `N` factor. The first factor of `eT` lies in
`U`, not in `B`.

The `eT` formula is the formula of the published `upperBruhatTorusMap n w`,
whose domain is `U × (Fin n → Kˣ) × U`. Precisely, the value of `eT x` is that
map's value at `(x.1, x.2.1, x.2.2)`, where `x.2.2` is regarded as an element of
`U` through the inclusion `N ≤ U`. This identification holds by the published
definitions (`upperBruhatTorusMap_val`); it is not an additional conjunct.

## Topologies

The statement uses only the existing instances:

- `K` carries the given topology. `Kˣ` carries Mathlib's standard units
  topology, induced by `u ↦ (u, u⁻¹)` into `K × Kᵐᵒᵖ`.
- Matrices carry the product (entrywise) topology. `Langlands.GeneralLinear n K`
  carries Mathlib's topology on units of the matrix ring, induced by
  `g ↦ (g, g⁻¹)`.
- `B`, `U` and `N` carry the subgroup subtype topologies, and `C` carries the
  subtype topology induced from the general linear group.
- `Fin n → Kˣ` carries the product topology, and the domains of `eB` and `eT`
  carry the binary product topologies.

No replacement topology, such as one induced from matrix entries alone or a
quotient topology, is used.

## Hypotheses, rank zero and exclusions

The only hypotheses are the type-class assumptions listed above.
`IsTopologicalDivisionRing K` makes addition, multiplication and negation
continuous, and inversion continuous at every nonzero element. The Hausdorff
hypothesis `T2Space K` is part of the requested scope. The proposition makes no
claim about non-Hausdorff topological fields.

The caller supplies no factorization, uniqueness of coordinates, surjectivity,
continuous inverse, quotient-map property, local compactness, completeness,
countability, valuation, analytic structure or geometry certificate. Bijectivity
and continuity of both inverses are part of the conclusion.

In rank zero every group involved is trivial and `C` is a singleton. That case
is included and is not excluded by any hypothesis.

The proposition asserts nothing about the following: transpose or Weyl-transpose
stability of an individual cell, local closedness of `C` in the general linear
group, the Bruhat decomposition of the whole group, closure or dimension
relations between cells, analytic or manifold structure, the factorization
`U = U_w⁺ · U_w⁻` as a separate claim, submersivity, measures, distributions or
integration.

## Original source and provenance

The registered original is `shalika-1974-multiplicity-one`, J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974),
171–193. The copy at
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256 `788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed pp.174–176 are one-based PDF pages 5–7; they were rendered and checked
visually. No errata file for this source exists in the project literature or
Library notes.

Source content:

- Printed p.174 calls the double cosets `G_w = HUwU`, where `H` is the diagonal
  torus and `w` is a representative in `N(H)`. It defines
  `U_w⁺ = U ∩ w⁻¹ U w` and `U_w⁻ = U ∩ w⁻¹ Ubar w`.
- Printed p.175 states Lemma 1.7 for a local field `k`. In its proof, Shalika
  sets `G₀ = HU × U_w⁻` and defines `φ((hu, u⁻)) = huwu⁻`. He shows that `φ` is
  injective and immersive and that `G_w` is locally closed, hence locally
  compact. The Arens–Pontryagin theorem then makes `φ` a homeomorphism of `G₀`
  with its image `G_w`. The text continues: "The proof shows that we may
  identify `G_w` with `U × H × U_w⁻`." The last factor is misprinted as `H_w⁻`.
- Printed p.176 defines `π(u₁, h, u₂) = u₁whu₂` on `U × H × U`, with the torus
  to the right of `w`. In the proof of Lemma 1.9, the image of
  `(u₁, h, u₂⁻)` under the second map of the displayed composite is printed as
  `u₁hu₂⁻`, without `w`. We follow the displayed definition of `π`.

Correspondence with the Lean statement: `HU` is `B`, Shalika's `w` is `p`,
`G_w` is `C` and `U_w⁻` is `N`. The torus `H` is parametrized by `Fin n → Kˣ`
through the injective homomorphism `Iwasawa.diagonalUnits`. Conjunct 1 is the
homeomorphism `φ` of the proof of Lemma 1.7, where the first coordinate `b ∈ B`
plays the role of `hu`. Conjunct 2 is the identification of `G_w` with
`U × H × U_w⁻` in the order of `π` on printed p.176:
`(u, h, u⁻) ↦ u w h u⁻`.

Internal extension: Shalika proves these statements only for local fields.
His argument uses local compactness, analytic manifolds and the
Arens–Pontryagin theorem. This proposition quantifies over all Hausdorff
topological fields. It is an explicitly internal generalization of the actual
matrix formulas, not a claim about the original's stated hypotheses. The
intended proof route uses rational coordinate formulas and does not use the
open-mapping argument. If `g = b * p * v` with `b ∈ B` and `v ∈ N`, then
`g * p⁻¹ = b * (p * v * p⁻¹)` factors as an upper triangular matrix times a
lower unipotent matrix. The entries of the lower unipotent factor are rational
functions of the entries of `g`. Their denominators are bottom-right principal
minors of `g * p⁻¹`, which do not vanish on `C`. The torus coordinates come
from the elementary splitting `B = U · diagonal` and the published identity
`permutation_mul_diagonalUnits`, which moves a diagonal matrix across `p`. This
route is a proof plan only. None of it is proved or assumed here.

## Intended use

This proposition is a common geometry prerequisite for the Whittaker
multiplicity-one and Shalika distribution arguments. Its proof is a separate
unit. Consumers must use the actual maps above and may not add any of the
excluded geometric conclusions as hypotheses.
