# Rational points from a separable primitive element over a fraction field

Authors: Worker 254.

This module is commutative algebra. Everything lives in the namespace
`Langlands.CommutativeAlgebra.RationalPointSpecialization`. It imports only
Mathlib.

## Main result

`nonempty_algHom_of_isFractionRing`. Let `k` be a field with `[IsSepClosed k]`.
Let `P` be an integral domain and a `k`-algebra, with fraction field `F`
(`[IsFractionRing P F]`, compatible `k`-algebra structures,
`[IsScalarTower k P F]`). Let `K` be a field extension of `F`, compatible with
`k` (`[IsScalarTower k F K]`), that is finite (`[FiniteDimensional F K]`) and
separable (`[Algebra.IsSeparable F K]`). Let `R` be a commutative `k`-algebra
of finite type (`[Algebra.FiniteType k R]`) with a `k`-algebra map
`f : R →ₐ[k] K`. Assume

- `H`: for every nonzero `D : P` there is a `k`-algebra map `ψ : P →ₐ[k] k`
  with `ψ D ≠ 0`.

Then `Nonempty (R →ₐ[k] k)`.

Geometrically: `Spec K → Spec R` is a generic point over the variety
`Spec P`. If the `k`-points of `Spec P` are Zariski dense, a `k`-point of
`Spec R` is obtained by specializing that generic point.

## Auxiliary result

`exists_forall_eval_map_eq_zero`. Let `C` be a commutative ring, `F` a field,
`K` a nontrivial `F`-algebra and `k` a separably closed field. Let
`ι : C →+* F` be injective and `ψ : C →+* k` arbitrary. Let `y : K` be integral
over `F`, and let `g : C[X]` be separable with `g.map ι = minpoly F y`. Then
some `t : k` satisfies: every `h : C[X]` with `aeval y (h.map ι) = 0` also
satisfies `(h.map ψ).eval t = 0`.

## Proof

`exists_forall_eval_map_eq_zero`. Since `ι` is injective and `g.map ι` is the
monic polynomial `minpoly F y`, `g` is monic. Its image `g.map ψ` then has the
same positive degree as `minpoly F y`. It is separable because separability is
preserved by ring maps. As `k` is separably closed, `g.map ψ` has a root `t`
(`IsSepClosed.exists_root`). Let `h` satisfy `aeval y (h.map ι) = 0`. The
remainder `h %ₘ g` maps under `ι` to a polynomial that vanishes at `y` and has
degree less than `minpoly F y`. By `minpoly.degree_le_of_ne_zero` that image is
zero, so `h %ₘ g = 0` by injectivity. Hence `h = g * (h /ₘ g)`, and
`(h.map ψ).eval t = 0` because `t` is a root of `g.map ψ`.

`nonempty_algHom_of_isFractionRing`.

1. Take the primitive element `y` of `K / F` from
   `Field.powerBasisOfFiniteOfSeparable`. Its minimal polynomial is separable,
   so `u * minpoly F y + v * derivative (minpoly F y) = 1` for some `u, v`.
2. Write `R` as a quotient of `MvPolynomial (Fin n) k` by a surjection `π`
   (`Algebra.FiniteType.iff_quotient_mvPolynomial''`). For each `i`, the power
   basis gives `Q i : F[X]` with `f (π (X i)) = aeval y (Q i)`.
3. Collect the coefficients of `minpoly F y`, `u`, `v` and all `Q i` in a finite
   set `S`. `IsLocalization.exist_integer_multiples_of_finset` gives a nonzero
   common denominator `D : P`. By `H`, some `ψ₀ : P →ₐ[k] k` has `ψ₀ D ≠ 0`.
4. Let `C = Localization.Away D`. The maps `P → F` and `ψ₀` send `D` to units,
   so they extend to `ι : C →ₐ[k] F` and `ψ : C →ₐ[k] k`
   (`IsLocalization.Away.liftAlgHom`). The map `ι` is injective
   (`IsLocalization.lift_injective_iff` together with the injectivity of
   `P → F`). Every element of `S` lies in the range of `ι`, so the minimal
   polynomial, `u`, `v` and every `Q i` lift to polynomials `g'`, `u'`, `v'`
   and `Q' i` over `C` (`Polynomial.lifts_iff_coeff_lifts`).
5. The Bezout identity lifts to `g'` because `Polynomial.map ι` is injective,
   so `g'` is separable. The auxiliary result gives `t : k`.
6. Let `Θ : MvPolynomial (Fin n) k →ₐ[k] C[X]` send `X i` to `Q' i`. On
   generators, `aeval y ∘ map ι ∘ Θ` agrees with `f ∘ π`, so the two maps are
   equal. Let `Φ = eval t ∘ map ψ ∘ Θ`. If `π z = 0`, then
   `aeval y ((Θ z).map ι) = f (π z) = 0`, and the auxiliary result gives
   `Φ z = 0`. So `Φ` vanishes on the kernel of `π` and factors through
   `R ≅ MvPolynomial (Fin n) k ⧸ ker π`. The factored map is the required
   `k`-algebra map `R → k`.

## Provenance

These are internal helper lemmas. They supply the specialization step of the
proof of `Langlands.CommutativeAlgebra.SeparablyClosedRationalPointStatement`
in `Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof`. Spreading
out a separable primitive element over a localization `P[1/D]` and specializing
at a `k`-point where `D` does not vanish is a standard argument. The statements
and their Lean proofs are our own and follow no particular printed source.
