# Equal-rank uniqueness of twisted invariant trilinear forms

This module defines
`Langlands.RankinSelberg.EqualRankTrilinearUniquenessStatement.{uF,uV,uW}`
as a proposition. It states the Proposition in JPSS §2.10, printed p.396,
for the Library's p-adic fields and actual Whittaker coefficient models.
It does not prove that proposition.

## Exact statement

The arguments are `{p : ℕ} [Fact p.Prime]`,
`F : PadicField.{uF} p`, `T : F.TopologicalData`, and `n : ℕ`.
Thus the field is a finite extension of `ℚ_p`, and the group has positive
rank `n+1`. The only installed local instance is `letI := T.topology`.
Write `G = Langlands.GeneralLinear (n+1) F.Carrier`,
`q = T.residueCardinality`, and `abv = normalizedAbsoluteValue T`.

For every `ψ : UnitaryAdditiveCharacter F.Carrier`, every pair of
independent carriers `V : Type uV` and `W : Type uW` equipped with
`AddCommGroup` and `Module ℂ` instances, and every pair of representations
`π : Representation ℂ G V` and `σ : Representation ℂ G W`, assume

```text
IsOfWhittakerType n (standardCharacter ψ n) π
IsOfWhittakerType n (inverseStandardCharacter ψ n) σ.
```

The character `ψ` is nontrivial, continuous, and unitary by its type.
The existing `IsOfWhittakerType` means admissibility, finite generation
as a module over the complex group algebra, and a linear equivalence
between the space of functionals for the specified unipotent character
and `ℂ`. Here admissibility includes smoothness and finite-dimensional
fixed vectors for every open subgroup. This is the Library's
formalization of JPSS §2.1's admissible finite-type representations with
one-dimensional Whittaker-functional space.

For every `ℓ : glFunctionals ψ n π` and
`ℓ' : glInverseFunctionals ψ n σ`, put

```text
M  = (coefficientModel π ℓ).toSubmodule
M' = (coefficientModel σ ℓ').toSubmodule
S  = SchwartzBruhat (Fin (n+1) → F.Carrier).
```

These are the actual coefficient images, with actions
`modelRepresentation π ℓ` and `modelRepresentation σ ℓ'`.
The third space consists of compactly supported locally constant
complex-valued functions on row vectors. A trilinear form is encoded as
the curried complex-linear map
`B : M →ₗ[ℂ] M' →ₗ[ℂ] S →ₗ[ℂ] ℂ`.

For `s : ℂ`, the local predicate `IsTwistedInvariant s B` means that,
for every `g : G`, `f : M`, `f' : M'`, and `Φ Φg : S`, the premise

```text
∀ x, Φg x = Φ (Matrix.vecMul x g.val)
```

implies

```text
B (modelRepresentation π ℓ g f) (modelRepresentation σ ℓ' g f') Φg
  = determinantWeight abv g (-s) * B f f' Φ.
```

Thus the third action is precisely right multiplication of row vectors,
`ρ(g)Φ(x) = Φ(xg)`, expressed by the pointwise premise on `Φg`.
The definition introduces no separate Schwartz–Bruhat action or
closure theorem. The existing determinant weight is
`(abv (Matrix.det g.val) : ℂ) ^ (-s)`, with the normalized absolute
value supplied by `T`.

The conclusion is that there exists `E : Finset ℂ` such that for every
`s : ℂ` with `spectralPoint q s ∉ E`, and every pair `B B'` of such
trilinear forms,

```text
IsTwistedInvariant s B → IsTwistedInvariant s B' →
  B ≠ 0 → ∃ c : ℂ, B' = c • B.
```

The finite exceptional set is chosen after the character, representations,
and functionals, but before `s` and the two forms. The existing
`spectralPoint q s` is `(q : ℂ) ^ (-s)`, so exceptions are values of
`q^(-s)`, not a finite set of complex exponents `s`. The conclusion
expresses dimension at most one, including the possibility of no
nonzero invariant form.

The functionals are not required to be nonzero. If either is zero,
its coefficient image is the zero space and every such trilinear form
vanishes, so the implication with `B ≠ 0` is vacuous. For nonzero
functionals, the one-dimensional functional spaces identify these
coefficient images with the Whittaker models used by JPSS. No
irreducibility, central characters, finite length, or uniqueness
conclusion is assumed.

## Source correspondence

H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin-Selberg Convolutions*, American Journal of Mathematics **105**
(1983), 367–464, §2.1, pp.385–386, and §2.10, pp.396–398.
The registered source is `jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
with SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Printed pages 385–386 and 396–398 are PDF pages 20–21 and 31–33,
respectively, and were read visually. No source erratum note was found
in the checked project and Library errata locations.

The Proposition on printed p.396 is stated for all pairs of
representations of Whittaker type on
`W(π;ψ) × W(π';ψ̄) × S(F^r)`, with twisted invariance (2.10.4).
Here its `π'` is `σ`, its rank `r` is `n+1`, and its conjugate
unitary character is represented by `inverseStandardCharacter ψ n`.
The source acts by right translations on the two Whittaker models,
as does `modelRepresentation`. Its determinant twist is `|det g|^(-s)`,
and its row action is `ρ(g)Φ(x) = Φ(xg)`; compare (2.10.2).
This agrees with the Library equal-rank integrand's evaluation
`Φ (lastRow g)`: multiplying a matrix on the right multiplies its
last row on the right. The source allows arbitrary non-Archimedean
local fields; this statement is restricted to `PadicField`.

## Source proof context, not a formalized proof

On pp.397–398, JPSS first restricts the form to test functions vanishing
at zero. Identifying the nonzero-row orbit with the quotient by the
mirabolic subgroup `P`, Frobenius reciprocity reduces the problem to
`Bil_P((π ⊗ α^(s-1))|P, π'|P)`, where `α(g) = |det g|`.
The proof uses Bernstein–Zelevinsky Corollary 5.22 for finite-length
composition series of the restrictions to `P`. JPSS Proposition (1.4)
and (1.5) Corollary 2 exclude the other pairs of constituents outside
finitely many spectral values. The remaining mirabolic constituent
`τ` has one-dimensional `Bil_P(τ ⊗ α^s, τ)`; the proof uses `s`
after shifting the parameter from the preceding `s-1` expression.

After subtracting a suitable scalar multiple, the remaining trilinear
form factors as `γ(f,f') Φ(0)`. The source eliminates this residual
bilinear pairing outside a finite exceptional set by the twisted
contragredient condition; the corresponding central-character
constraint supplies the finite-exception argument for this part
supported at `Φ(0)`. These are descriptions of the literature's proof,
not hypotheses of this Lean statement or results proved in this
module.
