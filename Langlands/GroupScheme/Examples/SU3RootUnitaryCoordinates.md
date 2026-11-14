# Bilinear coordinates on the quadratic unitary parameter group

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryCoordinates`, namespace
`Langlands.GroupScheme.SU3Root`.

Throughout, `L / k` is a separable quadratic field extension (`Algebra.IsQuadraticExtension`,
`Algebra.IsSeparable`) with nontrivial automorphism `σ = conjugation k L`. For a commutative
`k`-algebra `S`, `tensorParameters k L S` is the published group of pairs `(u, v)` in
`S ⊗[k] L` with `v + bar(v) = u · bar(u)` and law
`(u, v)(u', v') = (u + u', v + v' + u · bar(u'))` (KP (2.7.2)), where `bar` is `id ⊗ σ`
(`tensorInvolution k L S`); `tensorParametersFunctor k L` is the published functor
`S ↦ tensorParameters k L S`.

## Field algebra

- `correction k L λ x y = σ(λ) x σ(y) − λ σ(x) y`, the bilinear correction of (C.4.2). It is
  `k`-bilinear (`correction_add_left/right`, `correction_smul_left/right`) and has trace zero:
  `correction λ x y + σ(correction λ x y) = 0` for every `λ` (`correction_add_conjugation`).
- `exists_algebraMap_mul_eq_of_traceZero`: if `f ≠ 0` and `f + σ f = 0`, every `z` with
  `z + σ z = 0` is `c · f` for some `c ∈ k`.
- `CoordinateData k L ι` (a *chart*) consists of a `k`-basis `e = basis` of `L` indexed by a
  finite type `ι`, an element `λ = traceOne` with `λ + σ λ = 1`, a nonzero `f = center` with
  `f + σ f = 0`, and coefficients `cᵢⱼ = coeff i j ∈ k` with
  `cᵢⱼ f = correction λ eᵢ eⱼ` (`coeff_mul_center`).
- `CoordinateData.traceBasis`: `(f, λ)` is a `k`-basis of `L`
  (`linearIndependent_center_traceOne`, by applying `x ↦ x + σ x`).
- `CoordinateData.ofBasis k L e λ hλ f hf hf'` is the chart with the given basis, `λ` and `f`
  and the (unique) coefficients they force.
- `canonicalCoordinateData k L : CoordinateData k L (ULift (Fin 2))` uses Mathlib's chosen
  basis `Module.finBasisOfFinrankEq` (reindexed to `ULift (Fin 2)`), the published trace-one
  element `traceOne k L`, and a chosen nonzero trace-zero element
  (`exists_ne_zero_add_conjugation_eq_zero`).

## The identification on every coefficient algebra

Fix a chart `D` and a commutative `k`-algebra `S`. `coeffs D S` are the images of the `cᵢⱼ`
in `S`.

- `tensorVec D S a = ∑ᵢ aᵢ ⊗ eᵢ` and `secondCoord D S a b = b ⊗ f + (1 ⊗ λ) u bar(u)` with
  `u = tensorVec D S a`.
- `form_tmul_center`: `form (coeffs D S) a a' ⊗ f = bar(1 ⊗ λ) u bar(u') − (1 ⊗ λ) bar(u) u'`.
- **`toParameters D S : Coordinates (coeffs D S) ≃* tensorParameters k L S`** is the group
  isomorphism `(a, b) ↦ (∑ᵢ aᵢ ⊗ eᵢ, b ⊗ f + (1 ⊗ λ) u bar(u))` from the bilinear coordinate
  group of `Langlands.GroupScheme.BilinearCoordinateGroup` with coefficients `cᵢⱼ`.
  Its inverse (`ofParameters`) sends `(u, v)` to the coordinates of `u` in the `S`-basis
  `1 ⊗ eᵢ` (`vecCoord`) and to the `f`-coordinate (`scalarCoord`) of the trace-zero part
  `x = v − (1 ⊗ λ) u bar(u)` (`traceZeroPart`, `traceZeroPart_add_bar`) in the `S`-basis
  `(1 ⊗ f, 1 ⊗ λ)`. `eq_scalarCoord_tmul` proves that a trace-zero `x` equals
  `scalarCoord x ⊗ f`: its `λ`-coordinate `q` satisfies `q ⊗ 1 = x + bar(x) = 0`, and
  `S → S ⊗[k] L` is injective since `k → L` is injective and `L` is flat over the field `k`.
  Multiplicativity is the identity `form ⊗ f = (correction term)` together with
  `(1 ⊗ λ) + bar(1 ⊗ λ) = 1`. This is the inverse of the coordinate change (C.4.1),
  `(u, v) ↦ (u, v − u bar(u) λ)`, followed by the coordinate `b` of `x = b f`.
- `toParameters_naturality`: for every `k`-algebra map `g : S → S'`, `toParameters` commutes
  with `Coordinates.map g` and the published `tensorParametersMap k L g`.

## The group scheme

Now `k` and `L` live in one universe `u`, and `ι : Type u`.

- `corepresentableBy k L D`: the polynomial ring `k[xᵢ, y]` (`coordinateAlgebra`)
  corepresents the underlying set functor of the published `tensorParametersFunctor k L`, by
  composing the corepresentation of the bilinear coordinate functor with `toParameters`.
- `chartGroupScheme k L D` is the resulting actual affine group scheme over `Spec k`, via the
  published `Corepresented.groupScheme`.
- **`unitaryParameterGroup k L`** `= chartGroupScheme k L (canonicalCoordinateData k L)` is the
  generic unitary parameter group `U_{L/k}` over `Spec k` of KP (2.7.2) as an actual group
  scheme. Its group of points over **any** test scheme `T` over `Spec k` (nonreduced ones
  included) is `tensorParameters k L Γ(T)` for the relative global sections `Γ(T)`
  (`unitaryPointsEquiv`), naturally in `T` (`unitaryPointsEquiv_naturality`, with the
  published `tensorParametersMap`).
- `identitySectionsEquiv R`: the relative global sections of the identity test scheme
  `Spec R → Spec R` are `R`, as an `R`-algebra isomorphism (`Scheme.ΓSpecIso`).
- `tensorParametersCongr k L e`: an isomorphism `e : S ≃ₐ[k] S'` of coefficient algebras
  induces `tensorParameters k L S ≃* tensorParameters k L S'`.
- **`unitaryRationalPointsEquiv k L`**: `rationalPoints (unitaryParameterGroup k L)` is
  isomorphic to the published field parameter group `rationalParameters k L`
  (pairs `(u, v) ∈ L²` with `v + σ(v) = u σ(u)`), by `unitaryPointsEquiv` at the identity test
  scheme, `tensorParametersCongr` along `identitySectionsEquiv`, and the published
  `rationalParametersEquiv`.

Every chart gives an isomorphic group scheme, since all charts corepresent the same functor;
the model construction compares charts through their common point model rather than through
this canonical one.

## Provenance

Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023): the group `U_{L/K}` and its law
are (2.7.2) (recalled at the start of Appendix C.4, printed p. 699); the coordinate change
(C.4.1) `X → Y × Z`, `(u, v) ↦ (u, v − u ū λ)` for `λ ∈ L_{tr=1}`, and the transported group
law (C.4.2) `(u, x)(u', x') = (u + u', x + x' − λ ū u' + λ̄ u ū')` are on printed p. 700. The
Lean `correction` is exactly the correction term of (C.4.2): from `x = v − λ u ū` and
`v'' = v + v' + u ū'` one gets `x'' = x + x' + σ(λ) u σ(u') − λ σ(u) u'`. Writing `x = b f`
for a fixed nonzero trace-zero `f` and `u` in a basis of `L` turns (C.4.2) into the bilinear
coordinate law of `BilinearCoordinateGroup`. The scheme `unitaryParameterGroup` is the
corepresentation of the published functor `tensorParametersFunctor`; the choice of the
canonical chart is an internal device, not from the source.
