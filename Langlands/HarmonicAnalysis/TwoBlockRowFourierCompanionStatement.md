# The two-block row Fourier companion identity

Worker 1181 wrote this derived statement. The target was specified in the task
contract `5aed5d06-d343-445a-b6e4-9b675d961187`, which Worker 484 published for the
dominant-rank gamma/L task `d7ca9f6d-e63f-4a97-bd89-683824d33655`. The module states
a proposition and contains no proof.

## Declarations

- `Langlands.HarmonicAnalysis.TwoBlockRowFourierCompanionStatement.{uF} : Prop` is the
  target. It is closed: it has no parameters, and its only universe parameter is the
  field universe `uF`.
- `Langlands.HarmonicAnalysis.twoBlockSwappedRow u η` is a transparent `abbrev` for
  coordinates. For `u : Fin b → X` and `η : Fin a → X` it is the function on
  `Fin (a + b)` given by

  ```text
  twoBlockSwappedRow u η j = Fin.append u η (finCongr (Nat.add_comm a b) j).
  ```

  So it is the row `(u, η)`: the `b` coordinates of `u` come first and the `a`
  coordinates of `η` last, and it is indexed by `Fin (a + b)` rather than
  `Fin (b + a)`. The cast `finCongr` keeps the numerical value of each index. This is
  the swapped join `swapped(u, η)` of the task.

## Ambient structures

The proposition quantifies over every prime `p` with `[Fact p.Prime]` and every
`F : PadicField.{uF} p`. It then installs exactly the topology, valuative relation and
local-field structure of `F.canonicalTopologicalData`, the Borel measurable space of
that topology, and its Borel certificate. The typeclass arguments of `IsSelfDual` also
need `T2Space` and `TotallyDisconnectedSpace`. These are not hypotheses. They are
derived inside the statement for the installed topology:

- `T2Space` is `F.canonicalTopologicalData.fieldT2`.
- `TotallyDisconnectedSpace` comes from Mathlib's `NonarchimedeanRing` structure of the
  valuative topology, identified with the installed topology by
  `Valuation.toTopologicalSpace_eq`.

This is the same installation as in the published
`Langlands.GodementJacquet.TwoBlockMatrixFunctionalEquationInductionStatement`.
Row spaces `Fin d → F.Carrier` carry the product topology and the product measurable
space. These are the structures that the unchanged `rowMeasure`, `rowPairing`,
`rowFourierIntegral` and `IsRowFourierPair` of `Langlands.HarmonicAnalysis.RowFourier`
use.

## Statement

For every `ψ : UnitaryAdditiveCharacter F.Carrier` and every supplied
`μ : AdditiveHaarMeasure F.Carrier`, assume the scalar self-duality certificate
`IsSelfDual ψ μ`. For all natural numbers `a` and `b` with `0 < a` and `0 < b`, and
with `N = a + b`, the proposition asserts the conjunction of two conclusions.

1. **Existence of a partner.** Every `Φ : SchwartzBruhat (Fin (a + b) → F.Carrier)`
   has a Schwartz–Bruhat `Φhat` with `IsRowFourierPair ψ μ Φ Φhat`. That is,
   `Φhat y = ∫ x, ψ(∑ i, x i * y i) Φ x ∂rowMeasure μ (a + b)` for every row `y`.
   This is the existing full-row transform with the plus sign. No Fourier operator is
   chosen or assumed.
2. **The companion identity.** Let `Φ, Φhat` be actual Schwartz–Bruhat functions with
   `IsRowFourierPair ψ μ Φ Φhat`. Let `g : Langlands.GeneralLinear (a + b) F.Carrier`,
   `ξ : Fin b → F.Carrier` and `η : Fin a → F.Carrier`. Then three things hold:
   - the left integrand below is integrable for `rowMeasure μ b`;
   - the right integrand below is integrable for `rowMeasure μ a`;
   - the following equality holds:

   ```text
   (F.canonicalTopologicalData.normalizedAbs (det g) : ℂ)⁻¹ *
     ∫ u : Fin b → F, ψ(-rowPairing u ξ) *
         Φhat (vecMul (twoBlockSwappedRow u η) (weylLong (a+b) F * inverseTranspose (a+b) F g).val)
       ∂rowMeasure μ b
   =
     ∫ w : Fin a → F, ψ(rowPairing w (η ∘ Fin.rev)) *
         Φ (vecMul (Fin.append w (ξ ∘ Fin.rev)) g.val)
       ∂rowMeasure μ a.
   ```

   Here `ψ(t)` abbreviates `ψ.complex t`. The names `weylLong` and `inverseTranspose`
   are `Langlands.GeneralLinear.weylLong` and
   `Langlands.GeneralLinear.inverseTranspose`, both with their explicit arguments
   `(a + b) F.Carrier`.

The two integrability conclusions and the equality are three separate conjuncts of
the proposition. They are not hypotheses. The integrals are Mathlib Bochner integrals.
The statement has no Fourier closure, inversion, countability, sigma-finiteness,
product-measure scaling or integrability premise. It neither chooses nor rescales a
Haar measure.

## Conventions

- **Right row action.** Rows act on matrices on the right. `Matrix.vecMul x M` is the
  row vector `xM`, with `(xM) j = ∑ i, x i * M i j`. So `Φ (vecMul x g.val)` is the
  source's right translate `(gΦ)(x) = Φ(xg)`; see JPSS §0.3, (10) on printed p.377,
  and the use of `Φ(ηg)` on p.412. Likewise the Lean `Φhat (vecMul z M)` with
  `M = w (gᵀ)⁻¹` is `(M Φ̂)(z)`.
- **Matrices.** `weylLong N F.Carrier` is the antidiagonal permutation matrix `w_N`
  (JPSS (0.5), p.376). `inverseTranspose N F.Carrier g` has underlying matrix
  `(g⁻¹)ᵀ`, which is the source's `g^ι = ᵗg⁻¹` (JPSS (0.6), p.376). The matrix used is
  `.val` of the group product `weylLong * inverseTranspose g`, that is,
  `w_N · ᵗg⁻¹`, which the source prints as `w_r ᵗg⁻¹`.
- **Kernels.** `rowPairing x y = ∑ i, x i * y i` is the bilinear pairing, with no
  conjugation. The left kernel is `ψ(-⟨u, ξ⟩)`, the complex conjugate `ψ̄(ξ ᵗu)` of the
  source. The right kernel is `ψ(+⟨w, η ∘ rev⟩)`.
- **Determinant factor.** `F.canonicalTopologicalData.normalizedAbs` is the
  residue-normalized absolute value: `q ^ (-ord x)` for nonzero `x`, where `q` is the
  actual residue cardinality. Its reciprocal at `det g`, cast to `ℂ`, multiplies the
  left integral. This is the source factor `|det g|⁻¹`.
- **Reversals.** For a row `ξ : Fin b → F.Carrier`, `ξ ∘ Fin.rev` is
  `(ξ_{b-1}, …, ξ_0)`. It precomposes with the reversal of the row's own index type
  `Fin b` and has no sign change. The same holds for `η ∘ Fin.rev` with `Fin a`. Both
  fixed rows are reversed between the two sides: `ξ` enters the left kernel and
  `ξ ∘ rev` the right block of the right-hand argument, and `η` enters the left
  argument while `η ∘ rev` enters the right kernel.
- **Measures.** `rowMeasure μ d` is the finite product of the one supplied scalar
  measure in every coordinate.

## Source and specialization

This is the pure Fourier identity (4.8.3) of Jacquet, Piatetski-Shapiro and Shalika,
*Rankin–Selberg Convolutions* (1983), §4.8, printed p.415:

```text
(w_r ᵗg⁻¹ Φ̂)*[ζ_{t₂}, η_{t₁}] |det g|⁻¹ = (gΦ)~[ζ_{t₁}, η_{t₂}].
```

The ingredients are defined as follows:

- **Plus-sign partial transform** (printed p.413): for `ξ, w ∈ F^{t₁}` and
  `v ∈ F^{t₂}`,
  `Φ~(ξ, v) = ∫_{F^{t₁}} Φ[(w, v)] ψ(ξ ᵗw) dw`.
  It is a transform in the first block of length `t₁`, with the plus character.
- **Inverse-character transform** (printed p.415, after exchanging block sizes): for
  `η ∈ F^{t₂}` and `w ∈ F^{t₁}`,
  `Φ*(η, w) = ∫_{F^{t₂}} Φ[v, w] ψ̄(η ᵗv) dv`.
  It is a transform in the first block, now of length `t₂`.
- **Fixed rows** (printed p.413): `ζ_t = (1, 0, …, 0)` and `η_t = (0, …, 0, 1)`.
- **Full transform** (printed p.378): `Φ̂` is the plus-sign Fourier transform for the
  self-invariant Haar measure. Here it is the `Φhat` of `IsRowFourierPair`, and
  self-invariance is the hypothesis `IsSelfDual ψ μ` on the scalar measure.

Set `a = t₁`, `b = t₂` and `N = r = a + b`. Expanding both sides with
`(gΦ)(x) = Φ(xg)` gives the following.

- The source left side is `|det g|⁻¹` times
  `∫_{u ∈ F^b} Φ̂((u, η_{t₁}) w_r ᵗg⁻¹) ψ̄(ζ_{t₂} ᵗu) du`.
  This is the Lean left side with `ξ = ζ_{t₂}` and `η = η_{t₁}`.
- The source right side is
  `∫_{w ∈ F^a} Φ((w, η_{t₂}) g) ψ(ζ_{t₁} ᵗw) dw`.
  This is the Lean right side, because `ξ ∘ rev` and `η ∘ rev` are then `η_{t₂}` and
  `ζ_{t₁}`.

Thus the source takes `ξ` to be the first basis row of length `b` and `η` the last
basis row of length `a`. Their reversals are the last basis row of length `b` and the
first basis row of length `a`, as the source's right side requires.

The arbitrary fixed rows `ξ, η` are an internal generalization of (4.8.3). JPSS prints
only the basis-row case and does not state this arbitrary-row Lean interface. A
reverse-and-invert argument suggests why the general form should hold; it is not a
proof:

1. The full-row change of variables
   `|det g|⁻¹ Φ̂(y ᵗg⁻¹) = (gΦ)^(y)` removes `g`.
2. Right multiplication by `w_N` reverses `(u, η)` into
   `Fin.append (η ∘ rev) (u ∘ rev)`.
3. The measure-preserving reversal `u ↦ u ∘ rev` turns the left kernel into
   `ψ(-⟨u ∘ rev, ξ ∘ rev⟩)`.
4. Fourier inversion in the `b` trailing coordinates leaves the plus-sign partial
   transform of `gΦ` in the first `a` coordinates, at `(η ∘ rev, ξ ∘ rev)`.

The same argument shows why the measure hypothesis matters. Replace `μ` by `cμ` with
`c > 0`. The left side then scales by `c^b · c^(a+b)`, because `Φhat` scales by
`c^(a+b)`. The right side scales by `c^a`. So the identity depends on the self-dual
normalization, and the statement assumes it rather than choosing a measure. The
hypotheses `0 < a` and `0 < b` are the positive-rank hypotheses of the two-block
setting and are retained as stated. The proposition asserts nothing for `a = 0` or
`b = 0`.

The pages were inspected visually in the registered original
`jpss-1983-rankin-selberg`, retained at
`/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA-256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The inspected printed pages are 376–378 and 412–415. The zero-based PDF index is the
printed page minus 366, so these are one-based PDF pages 11–13 and 47–50.

No source-specific errata note `notes/errata/jpss-1983-rankin-selberg.md` was found in
the checked Library notes, project notes or workspace. This records a bounded errata
check, not a claim that no errata exist elsewhere. The printed formula needed no
correction for this statement.

## Scope

This statement provides the target only and contains no proof. It introduces no
representation, quotient, Mellin identity, outer convergence, Whittaker-type or
local-factor assertion. It uses no private or unpublished Section 4.7 row-data
declaration and introduces no second partial-Fourier API. It is deliberately not
phrased with `TwoBlockPartialFourier`, which integrates square-matrix blocks, or
`PartialFourierEquiv`, which transforms the last column of a rectangular matrix as in
Section 6.

A later proof can obtain conclusion 1 and the `b`-dimensional row inversion from
`rowFourierCompatibility` in `Langlands.HarmonicAnalysis.RowFourierCompatibilityProof`.
For the full-row change of variables it can use the published row equivariance
statement `PadicRowFourierEquivarianceStatement` together with `rowTranslate`. For the
two-block splitting of the product measure it can use the slices and tensors of
`SchwartzBruhatProduct`. Those results are not hypotheses of this statement. Both
integrands are continuous and compactly supported in the integration variable, so the
integrability conjuncts are expected to follow directly.
