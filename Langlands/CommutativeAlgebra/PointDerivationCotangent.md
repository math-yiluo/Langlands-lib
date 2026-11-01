# Point derivations of a local ring and the dual cotangent space

Author: Worker 254.

Module `Langlands.CommutativeAlgebra.PointDerivationCotangent`. This is a
helper for the proof of
`Langlands.Scheme.FieldPointTangentLocalRegularityStatement`
(`Langlands/AlgebraicGeometry/FieldPointTangentLocalRegularityProof.lean`).
It is pure commutative algebra. It proves that the derivations of a local ring
into its residue field that vanish on a coefficient field are exactly the dual
of the cotangent space `m/m²`.

## Provenance

The definitions and results here are derived and internal. The mathematics is
the algebraic core of Stacks Project Lemma 33.16.5 (Tag 0B2E), specialised to a
rational point. That source is registered as
`stacks-flasque-affine-vanishing-kunneth-a04446e5`, file `varieties.tex`,
lines 3058–3105. There, `m_x/m_x² = Ω_{X/S,x} ⊗ κ(x)` when `κ(x) = κ(s)`.

The Stacks proof uses the naive cotangent complex. This file does not. It uses
the direct splitting available at a rational point: every element `r` is its
"constant part" `ε(r)` plus an element `r - ε(r)` of the maximal ideal. This file
does not mention Kähler differentials. It works with derivations directly.

## Coefficient rings (any commutative rings)

Let `A`, `R` and `K` be commutative rings in one universe `u`, with
`ι : A →+* R` and `π : R →+* K`.

- `derivations ι π : Submodule K (R →+ K)` consists of the additive maps
  `δ : R → K` that satisfy the Leibniz rule along `π`,
  `δ (a * b) = π a * δ b + π b * δ a`, and vanish on `ι(A)`. The `K`-module
  structure is pointwise multiplication. `derivations_mul` and
  `derivations_base` restate the two defining properties.
- `derivationsCongr τ`: for a ring isomorphism `τ : K ≃+* K'`, postcomposition
  with `τ` is an additive equivalence
  `derivations ι π ≃+ derivations ι (τ ∘ π)`.
  - `derivationsCongr_apply` gives its value.
  - `derivationsCongr_smul` says it turns multiplication by `c` into
    multiplication by `τ c`.

## Field coefficients and a local ring

Now let `K` be a field and `R` a local ring. Assume
`hbij : Function.Bijective (π.comp ι)`.

- `surjective_of_bijective`: `π` is surjective.
- `ker_eq_maximalIdeal`: `ker π` is maximal because `π` maps onto a field, so
  it equals the maximal ideal `m` of the local ring `R`.
- `residueEquiv hbij : ResidueField R ≃+* K` is the induced isomorphism. It
  sends `residue r` to `π r` (`residueEquiv_residue`), and
  `residueEquiv_symm_apply` gives its inverse.
- `constPart hbij = ι ∘ (π ∘ ι)⁻¹ ∘ π` is a ring endomorphism of `R`. The
  following lemmas describe it:
  - `π_constPart`: `π (constPart r) = π r`.
  - `constPart_ι`: `constPart (ι c) = ι c`.
  - `sub_constPart_mem`: `r - constPart r ∈ m`.
  - `constPart_eq_zero_of_mem`: `constPart r = 0` for `r ∈ m`.
- `maximalIdealMap hbij δ : m →ₗ[R] ResidueField R` sends `a` to
  `residueEquiv⁻¹ (δ a)`. It is `R`-linear because `δ (r a) = π r · δ a` when
  `π a = 0`.
- `toDual hbij δ` is a functional on the cotangent space. It is built in two
  steps:
  - `Ideal.Cotangent.lift` descends `maximalIdealMap` to `CotangentSpace R`.
    This works because `δ (a b) = 0` for `a, b ∈ m`.
  - `LinearMap.extendScalarsOfSurjective` makes the result linear over the
    residue field.

  `toDual_toCotangent` evaluates it on classes.
- `subConst hbij : R →+ m` is `r ↦ r - constPart r`. Lemma
  `toCotangent_subConst_mul` gives the key identity in `m/m²`:

  `[ab - ε(ab)] = ε(a)•[b - ε(b)] + ε(b)•[a - ε(a)]`.

  It holds because the difference is `(a - ε a)(b - ε b) ∈ m²`.
- `ofDual hbij l` is the derivation `r ↦ residueEquiv (l [r - ε r])`.
  - The key identity gives the Leibniz rule.
  - It vanishes on `ι(A)` by `constPart_ι`.
  - `ofDual_apply` evaluates it.
- `equivDual hbij : derivations ι π ≃+ Module.Dual (ResidueField R)
  (CotangentSpace R)` has forward map `toDual` and inverse `ofDual`.
  - Left inverse: `δ (r - ε r) = δ r`, because `ε r` lies in `ι(A)`.
  - Right inverse: `ε a = 0` for `a ∈ m`.
- `equivDual_smul`: multiplication by `c : K` corresponds to multiplication by
  `residueEquiv⁻¹ c`.
- `rank_derivations hbij`: `Module.rank K (derivations ι π)` equals the rank
  over `ResidueField R` of `Module.Dual (ResidueField R) (CotangentSpace R)`.
  This is Mathlib's `rank_eq_of_equiv_equiv` applied to `equivDual` and the
  bijection `residueEquiv⁻¹`.

## Scope

No Noetherian or finiteness hypothesis is used. The rank equality holds for
arbitrary cardinal ranks. The geometric input lives in
`Langlands.AlgebraicGeometry.SectionTangentDerivations`, and the dimension
count lives in the proof module.

## Imports

`Mathlib.RingTheory.Ideal.Cotangent`, `Mathlib.LinearAlgebra.Dimension.Basic`
and `Mathlib.Algebra.Module.Hom`. No Library file is changed.
