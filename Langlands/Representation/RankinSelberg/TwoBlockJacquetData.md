# Two-block scalar sections and absolute Jacquet integral data

Author: Worker 264. Worker 484 specified the unit and its consumer interface
for the dominant-rank joint gamma/L task `d7ca9f6d`.

Source: H. Jacquet, I. I. Piatetskii-Shapiro, J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), registered as
`jpss-1983-rankin-selberg`. The relevant text is Section 4.6, printed pages
410–411 (one-based PDF pages 45–46), formula (4.6.1) and the integrand of
(4.6.2). No errata note for this source is registered.

All declarations are in the namespace `Langlands.RankinSelberg.TwoBlockJacquet`
of `Langlands.Representation.RankinSelberg.TwoBlockJacquetData`. The module
contains data and defining identities only; see the last section for what is
not claimed.

## Source data

On printed page 410, `Q` is the lower standard parabolic of `G_t` of type
`(t₁, t₂)`, and `σ_u = Ind(G_t, Q; σ₁ × σ₂)` is normalized induction. The
source realizes `σ_i` on its Whittaker model `W(σ_i; ψ̄)`. A section `f`
therefore takes values in `W(σ₁; ψ̄) ⊗ W(σ₂; ψ̄)`, a space of functions on
`G_(t₁) × G_(t₂)`, and `f(g; h₁, h₂)` denotes the value at `g` evaluated at
`(h₁, h₂)`. The covariance (4.6.1) reads

```
f((a₁ 0; x a₂) g; h₁, h₂) = f(g; h₁a₁, h₂a₂) |det a₁|^(-t₂/2) |det a₂|^(t₁/2),
```

and (4.6.2) is the integral over `x ∈ M(t₁ × t₂)` of

```
f((1 x; 0 1) g; e, e) θ((1 x; 0 1)).
```

Here `θ` is the source's standard character of upper triangular unipotent
matrices, defined in (0.3) on printed page 377 (one-based PDF page 12) as
`θ(n) = ∏_(i=1)^(r-1) ψ(n_(i,i+1)) = ψ(Σ_i n_(i,i+1))`, with the positive `ψ`.
On the upper radical
`(1 x; 0 1)` it is `ψ(x_(t₁,1))`, the character of the bottom-left entry of
`x`. The source asserts on page 410 that (4.6.2) converges for `u ≫ 0`.
This module does not formalize that assertion.

## Formal setting

`F : PadicField.{uF} p` with `p` prime. The parameters are
`m : Fin 2 → ℕ` and `h : ∑ i, (m i + 1) = t + 1`. The block shape is the
published `B = succBlockShape m h`, so block `i` has rank `m i + 1`. Blocks of
rank one (`m i = 0`) are included. The carriers are an arbitrary dependent
family `W : Fin 2 → Type uW` with complex module structures, and
`σ i : Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)` are
arbitrary representations. They need not be smooth, irreducible or generic.
The field universe `uF` and the carrier universe `uW` are independent.

In the source, `(t₁, t₂) = (m 0 + 1, m 1 + 1)`. The source evaluates a
Whittaker function `f(g)` at `(h₁, h₂)`. For an arbitrary carrier this module
instead evaluates with supplied linear functionals `ell i : W i →ₗ[ℂ] ℂ`.
When `σ_i` is realized on a Whittaker model and `ell i` evaluates at the
identity, the scalar section below is the source's `f(g; h₁, h₂)`. This
identification is provenance only; the module proves nothing about Whittaker
functionals or models.

## Tensor contraction

`tensorContraction ell : PiTensorProduct ℂ W →ₗ[ℂ] ℂ` is defined for any
finite index type as `PiTensorProduct.lift` of the multilinear map
`v ↦ ∏ i, ell i (v i)`. That multilinear map is `MultilinearMap.mkPiAlgebra`
composed with the functionals. `tensorContraction_tprod` proves the
pure-tensor formula

```
tensorContraction ell (⨂ v_i) = ∏ i, ell i (v i).
```

`tensorContraction_pairFactorFunctional` proves by `rfl` that on Shahidi's
two-factor carrier, contraction against `Shahidi.pairFactorFunctional ℓ₁ ℓ₂`
is the published `Shahidi.pairFunctional ℓ₁ ℓ₂`. No second binary tensor
convention is introduced.

## Sections and scalar sections

`Sections F h σ` is an abbreviation for the carrier of the published actual
lower induction

```
F.canonicalNormalizedOppositeParabolicInduced B (B.blockTensor σ),
```

that is, `Induction.SmoothFunctions` of the opposite block parabolic for the
twisted inflated block tensor representation. `inducedRep F h σ` abbreviates
this representation, and `sectionEval F h σ f g` abbreviates `Induction.eval`
at `g`. No new section type or evaluation axiom is introduced. The canonical
topology `F.canonicalTopologicalData.topology` is supplied locally by `letI`,
as in the published induction modules.

For an ambient element `g` and an actual block Levi element `a : B.Levi F.Carrier`,

```
scalarSection ell f g a = tensorContraction ell (B.blockTensor σ a (sectionEval F h σ f g)).
```

`scalarSection_def` states this, and `scalarSection_one` evaluates at
`a = 1`. The following API is proved:

- Linearity in `f`: `sectionEval_add`, `sectionEval_smul`, `sectionEval_zero`,
  `scalarSection_add`, `scalarSection_smul`, `scalarSection_zero`. The bundled
  linear functional `scalarSectionMap ell g a` satisfies `scalarSectionMap_apply`.
- Pure tensors: if `sectionEval F h σ f g = ⨂ v_i`, then
  `scalarSection ell f g a = ∏ i, ell i (σ i (a i) (v i))`
  (`scalarSection_of_eval_eq_tprod`). The proof uses the published
  `BlockShape.blockTensor_tprod`.
- Right translation: `scalarSection ell (inducedRep F h σ g' f) g a =
  scalarSection ell f (g * g') a` (`scalarSection_inducedRep`). It holds by
  definition of the induced action.
- Covariance (4.6.1): `scalarSection_covariant`. Let
  `q : B.oppositeParabolic F.Carrier` with
  `B.oppositeLeviProjection F.Carrier q = b`. Then

  ```
  scalarSection ell f (q * g) a =
    ((F.canonicalTopologicalData.leviHalfModulus B b : ℂˣ) : ℂ)⁻¹ *
      scalarSection ell f g (a * b).
  ```

  The proof rewrites with the published
  `normalizedOppositeParabolicInduced_covariant`, multiplicativity of
  `B.blockTensor σ`, and `leviHalfModulus_apply`. The Levi factor `b` is
  multiplied on the right of `a`, as in the source's `(h₁a₁, h₂a₂)`. The
  published upper block modulus is
  `leviModulus B b = |det b₀|^(m 1 + 1) / |det b₁|^(m 0 + 1)`. Its inverse
  positive square root is therefore the source factor
  `|det a₁|^(-t₂/2) |det a₂|^(t₁/2)`.

## Upper radical

`upperRadical h R x`, for any commutative ring `R` and
`x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R`, is Shahidi's
`Shahidi.upper (m 0 + 1) (m 1 + 1) R x = (1 x; 0 1)`. It is transported to
`GeneralLinear (t + 1) R` by `GeneralLinear.reindex (finCongr (blockRanks_add h))`.
`blockRanks_add h` is the identity `(m 0 + 1) + (m 1 + 1) = t + 1`.

- `index_zero` and `index_one` identify the published block coordinates
  `B.index 0 i` and `B.index 1 j` with the cast coordinates `castAdd` and
  `natAdd`. `upperRadical_apply_cast` reads off entries in Shahidi coordinates.
- Group laws: `upperRadical_zero` (identity), `upperRadical_add`
  (`u(x + y) = u(x) u(y)`), `upperRadical_neg`, and `upperRadical_sub`.
- Entries in block coordinates: `upperRadical_index_zero_one` gives the
  upper-right rectangle `x i j`. `upperRadical_index_zero_zero` and
  `upperRadical_index_one_one` give the identity blocks, and
  `upperRadical_index_one_zero` gives the zero block.
- `upperRadical_injective`, and `continuous_upperRadical` for a topological ring.

## Positive kernel and sign convention

For a unitary additive character `ψ` of `R`,

```
positiveKernel ψ x = Shahidi.upperCharacter (m 0) (m 1) ψ (Multiplicative.ofAdd x).
```

This is the positive standard character on Shahidi's upper matrix, before the
total-rank reindexing. The proved identities are:

- `positiveKernel_apply`: `positiveKernel ψ x = ψ(x (Fin.last (m 0)) 0)`. This
  is the character of the corner entry, `x_(t₁,1)` in the source's one-based
  indexing. The proof uses `sum_superdiagonal_upper`, which shows that the
  superdiagonal of `(1 x; 0 1)` sums to that entry.
- `positiveKernel_eq_superdiagonal_upperRadical`: `positiveKernel ψ x` equals
  `ψ(∑ i : Fin t, u (castSucc i) (succ i))` for the total-rank matrix
  `u = upperRadical h R x`. This is the source's `θ(u)`.
- `norm_positiveKernel` (norm one), `positiveKernel_zero`, `positiveKernel_add`,
  and `continuous_positiveKernel` for a topological ring.

The source's block Whittaker models are taken with `ψ̄`, while the kernel of
(4.6.2) uses the positive `ψ`. The published `Shahidi.upperJacquetKernel`
follows Shahidi's convention and is the complex conjugate of the positive
character. `positiveKernel_eq_inv_upperJacquetKernel` and
`positiveKernel_eq_conj_upperJacquetKernel` make the sign conversion explicit.
`positiveKernel` must not be replaced by `upperJacquetKernel` with the same `ψ`.

## Integrand, integral and integrability

Let `ψ` be a unitary additive character of `F.Carrier` for the canonical
topology. The raw integrand is

```
integrand ψ ell f g x = scalarSection ell f (upperRadical h F.Carrier x * g) 1 * positiveKernel ψ x.
```

`integrand_def` states this. `integrand_apply` rewrites it as
`tensorContraction ell (sectionEval F h σ f (u(x) g)) * ψ(x (Fin.last (m 0)) 0)`.
`integrand_add`, `integrand_smul` and `integrand_zero` are the pointwise linear
identities. `integrand_inducedRep` is the raw right translation
`integrand ψ ell (inducedRep F h σ g' f) g = integrand ψ ell f (g * g')`.

Fix `[MeasurableSpace F.Carrier]` and a measure
`μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)` on the
product measurable space. The measure is an argument; no canonical,
Haar or self-dual normalization is chosen here. Then

```
jacquetFunction ψ ell μ f g = ∫ x, integrand ψ ell f g x ∂μ
```

is the ordinary Bochner integral (`jacquetFunction_def`, `jacquetFunction_apply`).
It is not the stable integral of the Shahidi construction. The
absolute-integrability conditions are Mathlib's `Integrable`:

```
IsAbsIntegrableAt ψ ell μ f g := Integrable (integrand ψ ell f g) μ
IsAbsIntegrable ψ ell μ f := ∀ g, IsAbsIntegrableAt ψ ell μ f g
```

Under these conditions the following are proved:

- Closure: `isAbsIntegrableAt_zero`, `IsAbsIntegrableAt.add`,
  `IsAbsIntegrableAt.smul`, `isAbsIntegrable_zero`, `IsAbsIntegrable.add`, and
  `IsAbsIntegrable.smul`.
- Linearity of the integral: `jacquetFunction_add` assumes integrability of both
  integrands at `g` and uses `integral_add`. `jacquetFunction_smul` holds
  without hypotheses by `integral_const_mul`. `jacquetFunction_zero` also holds
  without hypotheses.
- Right translation: `isAbsIntegrableAt_inducedRep_iff`,
  `IsAbsIntegrable.inducedRep`, and `jacquetFunction_inducedRep`, which states
  `jacquetFunction ψ ell μ (inducedRep F h σ g' f) g = jacquetFunction ψ ell μ f (g * g')`.
  These hold without integrability hypotheses because the integrands are
  equal as functions.

Without integrability, `jacquetFunction` is the Bochner integral's junk value
`0`. Only the identities above are claimed.

## Not claimed

This unit asserts no convergence of (4.6.2) for any `u`, `σ`, `ψ` or `μ`. It
also asserts no nonvanishing, Whittaker equivariance of `jacquetFunction`,
spanning of the Whittaker model of `σ_u`, unramified deformation, functional
equation, determinant-slice expansion or unfolding. None of these appears as a
hypothesis field or a structure. The bijection `f₀ ↦ f₀ φ_u` and the
majorization on printed page 411 are not formalized.

## Provenance of the derived API

The source states (4.6.1) and the integrand of (4.6.2). The following are
elementary Lean API with no separate source statement: the tensor
contraction, the bridge to `pairFunctional`, linearity, the pure-tensor
formula, the upper-radical group laws and entries, the kernel identities and
sign conversion, the integrability closure, and the right-translation
identities. The covariance lemma is the scalar form of (4.6.1). It is derived
from the published lower-induction covariance, not assumed.
