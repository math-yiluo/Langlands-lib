# JPSS adjacent-rank tensor star data

This module constructs the tensor star map and the sign matrix introduced at
the beginning of Section 6.2, printed page 431, of Jacquet, Piatetski-Shapiro
and Shalika, *Rankin-Selberg Convolutions*, Amer. J. Math. 105 (1983),
367–464. The source parameter is `t = r + 2`: the rectangular matrices have
`r + 1` rows and `r + 2` columns, the coefficient representation is on
`GL_(r+1)(F)`, and the sign matrix belongs to `GL_(r+2)(F)`.

The registered original is `jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`,
at `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`.
The defining passages are printed page 428, Section 6.1 formula (6)
(also called (6.1.6)), and printed page 431, the opening definition of
Section 6.2 before its Proposition. These are one-based PDF pages 63 and
66; both scanned passages were read visually. No source-specific errata
note was found in the current Library or shared project notes.

## Character and Fourier conventions

The source of the star map uses the inverse character `bar ψ`; its target
uses `ψ`. In Lean the inverse additive character is `ψ.scale (-1)`.
The Fourier factor itself is the **full plus `ψ` transform** of (6.1.6):

```text
Fψ Φ(m) = rectangularFourierIntegral ψ ν Φ m
        = ∫ a, Φ(a) * ψ.complex (∑ i, ∑ j, a i j * m i j)
            ∂rectangularMeasure ν (r + 1) (r + 2).
```

The pairing is the unsigned entry pairing, equal to `tr(a * mᵀ)`, and the
measure is the published nested product of the supplied scalar Haar
measure:

```text
Measure.pi (fun _ : Fin (r + 1) =>
  Measure.pi (fun _ : Fin (r + 2) => ν.measure)).
```

This is the published `rectangularFourierEquiv ψ ν (r+1) (r+2) hself`.
It is not the partial Fourier transform used to construct `ρ₀`.
Its inverse at `m` is the same plus integral at `-m`.
Only `hself : IsSelfDual ψ ν` is supplied.

All generic declarations are in `Langlands.RankinSelberg`. Write
`w = GeneralLinear.weylLong (r+1) F`, the matrix with ones on the
anti-diagonal, and `h^ι = GeneralLinear.inverseTranspose (r+1) F h`.
Here `h^ι = (h⁻¹)ᵀ`. The published `inverseTransposePullback σ` is the
representation `h ↦ σ(h^ι)` on the original carrier `V`.
The construction makes no identification with a smooth contragredient.

## Parameters

The field and coefficient carrier have independent universes:
`F : Type uF` and `V : Type uV`. The functional and coefficient-image
constructions use

```text
[Field F] [TopologicalSpace F] [IsTopologicalRing F]
[AddCommGroup V] [Module ℂ V]
```

with arbitrary `r : ℕ`,
`ψ : UnitaryAdditiveCharacter F`,
`σ : Representation ℂ (GeneralLinear (r + 1) F) V`, and
`ℓ : Whittaker.glFunctionals (ψ.scale (-1)) r σ`.
The topological-ring hypotheses support the existing character-scaling
interface; these constructions need no Haar measure or self-duality.

The tensor map has exactly the field/topology/measure hypotheses of
`rectangularFourierEquiv`:

```text
[Field F] [TopologicalSpace F] [IsTopologicalRing F]
[MeasurableSpace F] [BorelSpace F] [LocallyCompactSpace F]
[T2Space F] [TotallyDisconnectedSpace F].
```

Its explicit arguments, in order, are `ψ`, `ν : AdditiveHaarMeasure F`,
`hself : IsSelfDual ψ ν`, `σ`, and `ℓ`; `F`, `V`, and `r` are implicit.
There are no extra product Borel, sigma-finiteness, Fourier-closure or
character-nontriviality premises. There is no topology, norm or
completeness on `V` or on its coefficient image, and no smoothness,
admissibility, irreducibility, Whittaker-type or nonzero-functional
hypothesis. In particular `ℓ = 0` and `r = 0` are allowed.
The sign matrix needs only `[CommRing F]` and a natural number `r`.

## Functional and actual coefficient images

`adjacentRankStarFunctional ψ σ ℓ` has type

```text
Whittaker.glFunctionals ψ r (Whittaker.inverseTransposePullback σ).
```

It is `dualFunctional (ψ.scale (-1)) σ ℓ`, transported by
`functionalsCongr` along the proved character equality

```text
inverseStandardCharacter (ψ.scale (-1)) r = standardCharacter ψ r.
```

The equality is `inverseStandardCharacter_scale_neg_one ψ r`.
The transport preserves the underlying linear form. The lemmas
`adjacentRankStarFunctional_val` and `adjacentRankStarFunctional_apply`
give, respectively,

```text
(adjacentRankStarFunctional ψ σ ℓ).val = ℓ.val.comp (σ w)
(adjacentRankStarFunctional ψ σ ℓ).val v = ℓ.val (σ w v).
```

`adjacentRankStarFunctional_ne_zero` carries the hypothesis `ℓ.val ≠ 0`
to nonzeroness of this transformed form by the published
`dualFunctional_nonzero`.

Write `ℓ* = adjacentRankStarFunctional ψ σ ℓ`.
`adjacentRankStarModelEquiv ψ σ ℓ` is the complex-linear equivalence

```text
(glCoefficientModel (ψ.scale (-1)) r σ ℓ).toSubmodule ≃ₗ[ℂ]
  (glCoefficientModel ψ r (inverseTransposePullback σ) ℓ*).toSubmodule.
```

These are the actual images of coefficient maps. The definition takes
the underlying linear equivalence of the published `dualModelEquiv`
and composes it with a private equality-of-character equivalence.
That equivalence is constructed by eliminating the character equality
and using `LinearEquiv.refl`; its evaluation lemma proves that the
underlying functions are unchanged.

The public forward and inverse evaluation lemmas are
`adjacentRankStarModelEquiv_apply` and
`adjacentRankStarModelEquiv_symm_apply`. On underlying functions both
maps are

```text
D(W)(h) = W(w * h^ι).
```

The inverse lemma follows by applying the forward lemma at
`weylInverseTranspose h`, then using the involution of this change of
variable and the inverse law of the linear equivalence.
`adjacentRankStarModelEquiv_modelMap` proves

```text
D(modelMap σ ℓ v) = modelMap (inverseTransposePullback σ) ℓ* v.
```

Its proof compares underlying functions, uses the forward evaluation
lemma, and expands `σ(w * h^ι)` with the representation multiplication
law. Thus the coefficient of `v` goes to the coefficient of the same
`v`. Neither injectivity of `v ↦ modelMap σ ℓ v` nor replacement of
its image by all equivariant functions is used.

## The tensor equivalence and its laws

`adjacentRankStarEquiv ψ ν hself σ ℓ` has type

```text
adjacentRankTestSpace (ψ.scale (-1)) σ ℓ ≃ₗ[ℂ]
  adjacentRankTestSpace ψ (inverseTransposePullback σ) ℓ*.
```

The published `adjacentRankTestSpace` is the algebraic complex tensor
product of rectangular Schwartz–Bruhat functions with the actual
coefficient image. The definition is literally

```text
TensorProduct.congr
  (rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself)
  (adjacentRankStarModelEquiv ψ σ ℓ).
```

It acts on the whole tensor space. The pure-tensor formulas
`adjacentRankStarEquiv_tmul` and `adjacentRankStarEquiv_symm_tmul`
are definitional equalities:

```text
T(Φ ⊗ₜ W)       = Fψ(Φ) ⊗ₜ D(W)
T.symm(Φ' ⊗ₜ W') = Fψ.symm(Φ') ⊗ₜ D.symm(W').
```

The lemmas `adjacentRankStarEquiv_zero`, `_add`, `_smul`, and `_sum`
state preservation of zero, addition, complex scalar multiplication,
and a sum over any `Finset`. Their proofs are the corresponding
linearity laws of the equivalence. Inverse identities are included
in its `LinearEquiv` structure.

Let `E₋` and `E₊` denote the published `adjacentRankTestEvaluation`
for the source and target models. The two evaluation lemmas
`adjacentRankStarEquiv_tmul_evaluation` and
`adjacentRankStarEquiv_symm_tmul_evaluation` state

```text
E₊(T(Φ ⊗ₜ W)) m h =
  rectangularFourierIntegral ψ ν Φ m * W(w * h^ι)

E₋(T.symm(Φ' ⊗ₜ W')) m h =
  rectangularFourierIntegral ψ ν Φ' (-m) * W'(w * h^ι).
```

Here `W` and `W'` mean their underlying `glModelFunction`s. The
proofs rewrite the pure-tensor formulas, the published tensor
evaluation formula, the corresponding forward/inverse Fourier
evaluation, and the forward/inverse coefficient evaluation.
No second self-duality premise at `ψ.scale (-1)` is introduced.

## The actual sign matrix

`adjacentRankZetaDiagonal F r` is
`Fin.snoc (fun _ : Fin (r+1) => (-1 : F)) 1`.
Its `castSucc` entries are `-1` and its last entry is `1`.
`adjacentRankZeta F r : GeneralLinear (r+2) F` has both value and
inverse equal to `Matrix.diagonal (adjacentRankZetaDiagonal F r)`.
The matrix-unit identities are proved by multiplying diagonal
matrices and checking that each diagonal entry squares to one.

| Lemma | Equation |
| --- | --- |
| `adjacentRankZeta_val` | `ζ.val = Matrix.diagonal (adjacentRankZetaDiagonal F r)` |
| `adjacentRankZeta_entry` | `ζ i j = if i = j then adjacentRankZetaDiagonal F r i else 0` |
| `adjacentRankZeta_diagonal_castSucc` | each of the first `r+1` diagonal entries is `-1` |
| `adjacentRankZeta_diagonal_last` | the final diagonal entry is `1` |
| `adjacentRankZeta_offDiagonal` | `ζ i j = 0` when `i ≠ j` |
| `adjacentRankZeta_inv` | `ζ⁻¹ = ζ` |
| `adjacentRankZeta_mul_self` and `adjacentRankZeta_sq` | `ζ * ζ = 1` and `ζ ^ 2 = 1` |
| `adjacentRankZeta_inverseTranspose` | `ζ^ι = ζ` |
| `adjacentRankZeta_det` | `Matrix.det ζ.val = (-1 : F) ^ (r+1)` |
| `adjacentRankZeta_rankZero` | at `r = 0`, `ζ.val = !![-1, 0; 0, 1]` |

Here `ζ = adjacentRankZeta F r`. The inverse identity follows
directly from the constructed matrix unit; the inverse-transpose
identity also uses that a diagonal matrix equals its transpose.
The determinant proof takes the product of the diagonal entries,
splits off the last entry, and evaluates the product of `r+1`
copies of `-1`. The rank-zero proof checks the four entries.
All these laws hold over any commutative ring, including
characteristic two.

## Canonical p-adic specialization and scope

In the namespace `Langlands.RankinSelberg.Padic`,
`adjacentRankStarEquiv F ψ ν hself σ ℓ` is a transparent wrapper of
the generic equivalence for every `F : PadicField.{uF} p` with
`[Fact p.Prime]`. Its local topology, valuative relation, local
field structure, and Hausdorff instance come from
`F.canonicalTopologicalData`, exactly as in
`AdjacentRankIntegralModel.Padic`. Total disconnectedness follows
from the corresponding nonarchimedean ring, and the measurable
structure is `borel F.Carrier`. The carrier `V : Type uV` retains
its independent universe. The supplied data remain `ψ`, `ν`,
`hself`, `σ`, and `ℓ`.

`Padic.adjacentRankStarEquiv_tmul_evaluation` is the generic forward
pure-tensor evaluation at these canonical instances. No measure on
a general linear group or quotient is needed.

This is derived Lean packaging of the defining map and matrix in
JPSS Section 6.2, using the published full Fourier equivalence,
Whittaker dual constructions, character equality, and adjacent-rank
tensor definitions by their Lean names. JPSS does not separately
state the `LinearEquiv` packaging or its elementary API.
The module proves these constructions and computation laws only.
It does not assert Proposition (6.2.1), Lemma (6.2.2),
model-integral convergence, induced-image equality, determinant-shell
expansions, or adjacent-rank gamma or L-factor identities.
