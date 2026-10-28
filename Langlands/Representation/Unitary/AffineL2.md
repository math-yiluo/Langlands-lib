# Normalized affine action on actual complex L²

Authors: Worker 452 (construction, proofs and original description) and
Worker 872 (independent verification and description edits).

This module constructs a complex representation of the actual p-adic
mirabolic matrix group on an actual complex L² space, with an isometric
operator for every group element. Its primary declaration is
`Langlands.AffineL2.mirabolicRepresentation`.

This is an internal construction derived from the published modules
`Langlands.Analysis.NormalizedL2Pullback`,
`Langlands.Analysis.AffineChangeOfVariables` and
`Langlands.Group.GL.MirabolicAffine`, together with Mathlib's
`Representation` and linear isometry APIs. It does not transcribe an
external literature result. Those dependencies supply, respectively, the
actual normalized L² pullback, the affine measurable equivalences with their
proved Haar pushforward laws, and the coordinates of the actual mirabolic
matrix group.

## Hypotheses and conventions

Fix a prime `p`, with `[Fact p.Prime]`, a field package
`F : PadicField.{u} p`, supplied `T : F.TopologicalData`, and any natural
number `n`. Every declaration uses exactly the local instances
`T.topology`, `T.valuativeRel` and `T.localField`. The vector space
`V = Fin n → F.Carrier` has the inherited finite product topology. The
measurable structure on `V` is arbitrary subject to `[BorelSpace V]`.
The measure `μ : Measure V` is any measure with
`[Measure.IsAddHaarMeasure μ]`. No measure normalization is chosen, and no
extra pushforward hypothesis is imposed.

The carrier is Mathlib's actual `Lp ℂ 2 μ`: complex measurable functions
with finite L² seminorm, identified modulo equality almost everywhere.
In particular, formulas for representatives below are almost-everywhere
identities with respect to `μ`; they assert no pointwise equality of chosen
representatives. Matrix multiplication acts on column vectors by
`Matrix.mulVec`, with no transpose or dual action.

Write `δ(A) = (T.determinantNorm n A : ℝ≥0)` for
`A : GeneralLinear n F.Carrier`. This is the positive residue-normalized
absolute determinant furnished by the supplied topological data. It is
nonzero because `T.determinantNorm n A` is a unit. Set

```
S(A,v)(x) = A.val.mulVec x + v,
S(A,v)⁻¹(x) = (A⁻¹).val.mulVec (x - v).
```

The published affine Haar laws give

```
μ.map S(A,v) = δ(A)⁻¹ • μ,
μ.map S(A,v)⁻¹ = δ(A) • μ.
```

In these identities `ℝ≥0` acts on measures through the usual nonnegative
extended real scalar. The construction invokes
`AffineChangeOfVariables.padic_map_haar_symm` directly for this same `μ`;
it does not replace `μ` by a selected product Haar measure.

## The affine operator

`operator F T μ A v` is the complex-linear isometry equivalence

```
Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 μ
```

obtained by applying `NormalizedL2Pullback.isometryEquiv` to the inverse
of the published `AffineChangeOfVariables.measurableEquiv A v`, the scalar
`δ(A)`, its nonvanishing proof, and the proved inverse-affine Haar law.
The published normalization is

```
NormalizedL2Pullback.normalization c = ((√c : ℝ) : ℂ)⁻¹.
```

Consequently `coeFn_operator` states that `operator F T μ A v f` is
represented almost everywhere by

```
x ↦ normalization δ(A) • f ((A⁻¹).val.mulVec (x - v)).
```

Its factor is the positive inverse half determinant `|det A|^(-1/2)`.
The inverse affine map is essential to the left representation order.
`norm_operator` records norm preservation by the isometry equivalence.
Both results specialize the published normalized pullback interface.

`operator_one_zero` identifies the operator at `(1,0)` with the identity
linear isometry equivalence. Its proof reduces the affine measurable
equivalence and determinant norm at the identity, then applies
`NormalizedL2Pullback.isometryEquiv_refl`.

`operator_mul_apply` proves the exact left affine multiplication law

```
operator A v (operator B w f)
  = operator (A * B) (v + A.val.mulVec w) f.
```

The proof applies `NormalizedL2Pullback.normalized_comp` to the two
inverse measurable equivalences. Inverting the published affine
composition identity gives

```
S(A,v)⁻¹.trans S(B,w)⁻¹
  = S(A * B, v + A.val.mulVec w)⁻¹.
```

Here `e.trans d` means first apply `e`, then `d`. Multiplicativity of
`T.determinantNorm n` identifies the normalization scalar. Proof
irrelevance identifies proofs of the same measure law and nonvanishing
condition; no additional scaling assertion is assumed. Extensionality
then gives `operator_mul`, at the equivalence level:

```
(operator B w).trans (operator A v)
  = operator (A * B) (v + A.val.mulVec w).
```

`operator_symm` proves

```
(operator A v).symm = operator A⁻¹ (-((A⁻¹).val.mulVec v)).
```

It uses the published inverse-affine equivalence identity,
`NormalizedL2Pullback.isometryEquiv_symm`, and the inverse law for the
absolute determinant. `operator_inv_apply` and `operator_apply_inv`
then give both cancellation identities on actual L² vectors.

## The actual mirabolic representation

For `g : GeneralLinear.mirabolic n F.Carrier`, let `A = linearPart g`
and `v = columnPart g`, using the published namespace
`Langlands.GeneralLinear.Mirabolic`. These are the actual leading block
and the final column above the bottom entry:

```
A.val i j = g.val.val i.castSucc j.castSucc,
v i = g.val.val i.castSucc (Fin.last n).
```

The inverse block is the leading block of the actual inverse matrix.
`mirabolicOperator F T μ g` is defined to be `operator F T μ A v`.
`mirabolicOperator_one` identifies the operator at the identity matrix
with the identity linear isometry equivalence. Its proof computes the
final column of the identity matrix as zero and uses `map_one` for the
monoid homomorphism `linearPart` together with `operator_one_zero`.
`mirabolicOperator_mul` uses `map_mul` for `linearPart` and the
published `columnPart_mul`, which give

```
linearPart (g * h) = linearPart g * linearPart h,
columnPart (g * h)
  = columnPart g + (linearPart g).val.mulVec (columnPart h).
```

Together with `operator_mul`, these give

```
(mirabolicOperator h).trans (mirabolicOperator g)
  = mirabolicOperator (g * h).
```

This uses the inherited multiplication of actual mirabolic matrices.
The coordinate product is the affine law above; no direct-product
group law is used.

`mirabolicRepresentation F T μ` is the actual

```
Representation ℂ (GeneralLinear.mirabolic n F.Carrier) (Lp ℂ 2 μ).
```

It sends `g` to the underlying complex-linear endomorphism of
`mirabolicOperator g`. The identity and multiplication fields are
proved by linear-map extensionality and the preceding isometry laws.
`mirabolicRepresentation_apply` states equality with that operator.
The exported identity and multiplication formulas are
`mirabolicRepresentation_one_apply` and
`mirabolicRepresentation_mul_apply`.

`coeFn_mirabolicOperator` and `coeFn_mirabolicRepresentation` give the
almost-everywhere formula

```
x ↦ normalization δ(linearPart g) •
      f (((linearPart g)⁻¹).val.mulVec (x - columnPart g)).
```

The published `linearPart` and `columnPart` entry identities above make
this a formula through the actual leading block and final column.
`mirabolicOperator_affineMatrix` identifies the isometry at the actual
matrix `[[A,v],[0,1]]` with `operator A v`, using the published
coordinate extraction after reassembly. The corresponding equality
on vectors is `mirabolicRepresentation_affineMatrix`.
`norm_mirabolicOperator` and `norm_mirabolicRepresentation` record norm
preservation.

## Boundary and scope

There is no positivity assumption on `n`; rank zero is included by the
same definitions and proofs. No strong continuity, Fourier or
Plancherel theorem, quotient measure, coefficient completion, induced
Hilbert model, or irreducibility assertion is made here. These remain
separate obligations for the normalized-induction irreducibility route.
