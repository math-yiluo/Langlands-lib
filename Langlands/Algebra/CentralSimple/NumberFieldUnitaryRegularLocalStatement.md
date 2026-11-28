# Regular local unitary elements of prescribed relative reduced norm

Module: `Langlands.Algebra.CentralSimple.NumberFieldUnitaryRegularLocalStatement`.

`Langlands.CentralSimple.NumberFieldUnitaryRegularLocalStatement.{u}` is a proposition; this
module states it and does not prove it.

## The statement

The data are those of `Langlands.CentralSimple.NumberFieldUnitaryNormTorusStatement`: a number
field `F`, a separable quadratic extension `E/F`, a finite-dimensional central simple
`E`-algebra `B` that is an `F`-algebra through `E`, and an involution
`τ : FirstKindInvolution F B` (an `F`-linear anti-automorphism of order two) acting on `E` by
`SU3Root.conjugation F E`, the nontrivial automorphism `e ↦ ē` of `E/F`. Moreover `n` is a
natural number with `Module.finrank E B = n ^ 2`, `z : Eˣ`, and `v : Global.Place F` is a place
of `F` (archimedean or finite), with actual completion `F_v = Global.placeCompletion F v`.
Write

* `τ_v = τ.baseChange F_v`, the involution `id ⊗ τ` of `F_v ⊗[F] B`;
* `ψ : F_v ⊗[F] E → F_v ⊗[F] B` for the `F_v`-algebra map
  `Algebra.TensorProduct.map (AlgHom.id F_v F_v) (IsScalarTower.toAlgHom F E B)`, that is
  `a ⊗ e ↦ a ⊗ e`; its image is central;
* `c_v` for `Algebra.TensorProduct.map (AlgHom.id F_v F_v) (conjugation F E).toAlgHom`, the
  conjugation `a ⊗ e ↦ a ⊗ ē` of `F_v ⊗[F] E`.

The hypothesis is the local hypothesis of `NumberFieldUnitaryNormTorusStatement` at the single
place `v`: there is a unit `x` of `F_v ⊗[F] B` in `UnitaryPoints.unitaryPoints τ F_v`
(`x τ_v(x) = 1`) whose relative reduced norm `UnitaryPoints.relativeNorm F E B F_v x` is
`z ⊗ 1` in `E ⊗[F] F_v`.

The conclusion asserts an element `x : F_v ⊗[F] B` and a polynomial
`f : (F_v ⊗[F] E)[X]` such that

1. `x * τ_v x = 1`;
2. `f` is monic of natural degree `n`;
3. `f` is *conjugate-reciprocal* for `z`: for every `i ≤ n`,
   `f.coeff (n - i) = (-1) ^ n * (1 ⊗ z) * c_v (f.coeff i)`;
4. `f.eval₂ ψ x = 0`, that is `∑ ψ(f_i) xⁱ = 0`;
5. `(derivative f).eval₂ ψ x` is a unit of `F_v ⊗[F] B`;
6. for every `c : Fin n → F_v ⊗[F] E`, `∑ i, ψ (c i) * x ^ i = 0` implies `c = 0`: the
   elements `1, x, …, x^{n-1}` are linearly independent over `F_v ⊗[F] E` acting through `ψ`.

Condition 3 with `i = n` gives `f.coeff 0 = (-1) ^ n * (1 ⊗ z)`. Conditions 2–6 say that `x`
is a regular semisimple element of `F_v ⊗[F] B` over `F_v ⊗[F] E` whose characteristic
polynomial `f` is separable (in the sense that `f'(x)` is invertible) and has constant term
`(-1)ⁿ z`; condition 3 is the symmetry of the characteristic polynomial of a unitary element.

## Provenance (derived)

Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), source
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, proof of Theorem 6.28, printed
p. 363 (PDF p. 373): "without loss of generality, one can assume the local solutions `x_v` of
`Nrd_{A/L}(x) = y` are semisimple regular elements", with `f_v` their characteristic
polynomials; on printed p. 364 (PDF p. 374) the characteristic polynomial
`tⁿ + a_{n-1}t^{n-1} + ⋯ + a_0` of a unitary element satisfies the relations (6.44),
`τ(a_0) a_0 = 1` and `a_0 τ(a_i) = a_{n-i}`. Kneser, *Lectures on Galois Cohomology of
Classical Groups* (1969), source `kneser-1969-galois-cohomology-classical-groups`, §5.6,
Step 1, printed pp. 79–80 (PDF pp. 85–86), proves the regularity claim place by place: at a
place split in `E`, the first component of `x_v` is replaced by a regular element of the same
reduced norm and the second component is determined by `x_v τ(x_v) = 1`; at a place not split
in `E`, `B ⊗ F_v` is a matrix algebra in which `τ` is the adjoint of a Hermitian form, and a
regular unitary matrix of determinant `z` exists. Kneser writes the coefficient relations as
`a_{n-i} = z a_i^I` with alternating signs in `f_v`.

The Lean statement is the conclusion of this step at a single place. With the coefficient
convention `f = ∑ f_i Xⁱ`, the relations (6.44) for a polynomial with `f_0 = (-1)ⁿ z` read
`f_{n-i} = (-1)ⁿ z f̄_i`; for `i = 0` this is `z z̄ = 1` and for `i = n` it is
`f_0 = (-1)ⁿ z`. "Regular semisimple" is written as conditions 5 and 6: the polynomial `f`
annihilates `x`, its derivative is invertible at `x`, and the powers `1, …, x^{n-1}` are
independent over `F_v ⊗[F] E`. The coefficients of `f` lie in `F_v ⊗[F] E`, the centre of
`F_v ⊗[F] B` through `ψ`, which at a place split in `E` is a product of two copies of `F_v`.
