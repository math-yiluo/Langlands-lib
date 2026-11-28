# Proof of the unitary Krasner lemma

Module `Langlands.Algebra.CentralSimple.NumberFieldUnitaryLocalRootNeighborhoodProof`. It proves
`Langlands.CentralSimple.NumberFieldUnitaryLocalRootNeighborhoodStatement` of
[`NumberFieldUnitaryLocalRootNeighborhoodStatement`](NumberFieldUnitaryLocalRootNeighborhoodStatement.md)
in its universe `u`:

```lean
theorem Langlands.CentralSimple.numberFieldUnitaryLocalRootNeighborhood :
    NumberFieldUnitaryLocalRootNeighborhoodStatement.{u}
```

Lean reports that it depends on `propext`, `Classical.choice` and `Quot.sound` only.

## Notation

`K` is a complete nontrivially normed field that is an `F`-algebra (at the end, the completion
`F_v`), `A = K ⊗[F] E`, `ψ = UnitaryKrasner.psi F E B K = id ⊗ (E → B)`,
`c = UnitaryKrasner.conjA K cE = id ⊗ cE` for an involutive automorphism `cE` of `E/F` with
`τ (algebraMap E B e) = algebraMap E B (cE e)`, `τ_v = τ.baseChange K`, `ζ = 1 ⊗ z`, and
`bA = Algebra.TensorProduct.basis K b`, the `K`-basis `1 ⊗ b j` of `A`. The coordinates of a
polynomial `g` over `A` are `fun i j => bA.repr (g.coeff i) j` for `i : Fin n`.

## Declarations

All auxiliary declarations are in the namespace `Langlands.CentralSimple.UnitaryKrasner`.

* `exists_root_nhds`: in a finite-dimensional commutative normed `K`-algebra `S`, let
  `G(y, p) = yⁿ + ∑ᵢ Lᵢ(p) yⁱ` for continuous linear maps `Lᵢ : P → S` on a finite-dimensional
  normed space `P`. If `G(y₀, p₀) = 0` and `n y₀^{n-1} + ∑ᵢ Lᵢ(p₀) i y₀^{i-1}` is a unit, there are
  neighbourhoods `N₀ ∋ y₀`, `V₀ ∋ p₀` such that for `p ∈ V₀` the polynomial `G(·, p)` has at most
  one root in `N₀`, and for every neighbourhood `N` of `y₀` the polynomial `G(·, p)` has a root in
  `N` for all `p` near `p₀`.
* `aeval_monic_eq`, `aeval_derivative_monic_eq`: evaluation of a monic polynomial of natural
  degree `n` and of its derivative, written with the sum over `Fin n`.
* `reflect_eq_of_conjRecip`: if `deg g ≤ n` and `g_{n-i} = (-1)ⁿ ζ c(g_i)` for `i ≤ n`, then
  `reflect n g = C ((-1)ⁿ ζ) * g.map c`.
* `aeval_inv_eq_zero_of_reflect`: if `deg q ≤ N`, `reflect N q = C a * r` and the unit `w` is a
  root of `r`, then `w⁻¹` is a root of `q` (Mathlib's `eval₂_reflect_mul_pow`).
* `exists_unitary_root_nhds`: the unitary root neighbourhood in an abstract finite-dimensional
  commutative `A`-algebra `S` with a `K`-algebra endomorphism `σ` acting on `A` by a ring
  endomorphism `cA`, for a root `y₀` of a monic `f` with `y₀ σ(y₀) = 1`, `f'(y₀)` a unit and the
  family `(bA j) y₀ⁱ` linearly independent over `K`. No topology on `S` is assumed: the proof puts
  one on `S`.
* `eq_zero_of_linearIndependent`: `K`-linear independence of `(bA j) yⁱ` (indexed by
  `Fin 2 × Fin n`, or any `ι × Fin n`) implies that `∑ᵢ cᵢ yⁱ = 0` with `cᵢ ∈ A` forces `c = 0`.
* `psi`, `conjA` (abbreviations), `psi_commute` (the image of `ψ` is central), `conjA_conjA`,
  `baseChange_psi` (`τ_v ∘ ψ = ψ ∘ c`), `baseChange_pow`, `baseChange_eval₂`
  (`τ_v (p.eval₂ ψ r) = p.eval₂ (ψ ∘ c) (τ_v r)`).
* `local_root_neighborhood`: the statement with `F_v` replaced by any such `K` and
  `conjugation F E` by any such `cE`.

## Proof

**Inverse function theorem (`exists_root_nhds`).** The map `Ψ(y, p) = (G(y, p), p)` on `S × P`
has, by the product and power rules for strict derivatives in a commutative normed algebra
(`HasStrictFDerivAt.fun_mul`, `HasStrictFDerivAt.pow`), the strict derivative
`D'(h, k) = (D(h, k), k)` at `(y₀, p₀)`, where `D(h, 0)` is `h` times the unit above. Hence `D'` is
injective, and, `S × P` being finite-dimensional, a continuous linear equivalence
(`LinearEquiv.ofInjectiveEndo`, `LinearEquiv.toContinuousLinearEquiv`). Mathlib's local inverse
`HasStrictFDerivAt.localInverse` then gives both conclusions: `eventually_left_inverse` on a
product neighbourhood `N₀ ×ˢ V₀` gives uniqueness, since two roots `y, y'` of `G(·, p)` satisfy
`Ψ(y, p) = (0, p) = Ψ(y', p)`; `eventually_right_inverse` and `localInverse_tendsto` along
`p ↦ (0, p)` give, for `p` near `p₀`, the root `(localInverse (0, p)).1`, which lies in `N`.

**The abstract unitary case (`exists_unitary_root_nhds`).** A `K`-basis of `S` embeds `S` into
square matrices over `K` through `Algebra.leftMulMatrix`; with the `L^∞`-operator norm on
matrices (`Matrix.linftyOpNormedRing`, `Matrix.linftyOpNormedAlgebra`), `NormedCommRing.induced`
and `NormedAlgebra.induced` make `S` a normed commutative `K`-algebra, complete because it is
finite-dimensional. The parameter space is `P = Fin n → ι → K` and `Lᵢ(p) = ∑ⱼ p i j • bA j`, so
that `Lᵢ` of the coordinates of `g` is `g_i` and `G(y, coordinates of g) = g(y)` for monic `g` of
natural degree `n`; at `f` the derivative condition is that `f'(y₀)` is a unit. Let `N₀`, `V₀` be
as in `exists_root_nhds`. The map `y ↦ Ring.inverse (σ y)` is continuous at `y₀` (`σ` is
`K`-linear on a finite-dimensional space, and `NormedRing.inverse_continuousAt` applies at the
unit `σ(y₀) = y₀⁻¹`) and sends `y₀` to `y₀`; the units form an open set; and the set of `y` for
which `(bA j) yⁱ` are linearly independent is a neighbourhood of `y₀`
(`LinearIndependent.eventually`). Intersect these neighbourhoods with `N₀` to obtain a
neighbourhood `N₁` where `σ(y)` is a unit, its inverse lies in `N₀`, and the family remains
linearly independent. Choose an open neighbourhood `U ⊆ V₀` of `p₀` on which `G(·, p)` has a
root in `N₁`.
For a conjugate-reciprocal monic `g` with coordinates in `U` and its root `y ∈ N₁`, write
`w = σ(y)`, a unit. Applying `σ` to `g(y) = 0` gives `(g.map cA)(w) = 0`, and
`reflect n g = C ((-1)ⁿ ζ) * g.map cA`, so `w⁻¹` is a root of `g`; it lies in `N₀`, so
uniqueness gives `y = w⁻¹`, that is `y σ(y) = 1`.

**Construction in `K ⊗[F] B` (`local_root_neighborhood`).** After substituting
`n = f.natDegree`, let `S = AdjoinRoot f`, finite and free over `A` with basis `1, X, …, X^{n-1}`
(`AdjoinRoot.powerBasis'`) and hence finite-dimensional over `K`. Since `ψ(A)` is central,
`p ↦ p.eval₂ ψ x` is a ring map (`Polynomial.eval₂RingHom'`) vanishing on `(f)`, and induces
`φ : S → K ⊗[F] B` with `φ(X) = x`. It is injective: `φ(∑ᵢ aᵢ Xⁱ) = ∑ᵢ ψ(aᵢ) xⁱ`, and the
hypothesis on `x` forces `a = 0`.
The conjugate-reciprocal relation at `i = 0` and `i = n` gives `ζ · ((-1)ⁿ c(f_0)) = 1` and
`f_0 = (-1)ⁿ ζ`, so `f_0` is a unit; from `X · divX f + f_0 = f` the class `X` is a unit of `S`.
The polynomial `f.map c` satisfies the conjugate-reciprocal relation for `c(ζ)`, and
`(f.map c).map c = f`, so `X⁻¹` is a root of `f.map c`; `AdjoinRoot.lift` gives a ring
endomorphism `σ` of `S` with `σ(a) = c(a)` on `A` and `σ(X) = X⁻¹`, which is `K`-linear.
From `x τ_v(x) = 1` and `φ(X⁻¹) x = 1` one gets `τ_v(x) = φ(X⁻¹)`; with `baseChange_eval₂` this
gives `τ_v(φ s) = φ(σ s)` for all `s` (induction on `AdjoinRoot`). The element `f'(X)` is a unit
of `S`: `φ(f'(X)) = f'(x)` is a unit, so multiplication by `f'(X)` is injective on `S` by
injectivity of `φ`, hence surjective. The family `(bA j) Xⁱ` is the basis
`bA.smulTower (powerBasis' f).basis` of `S` over `K`. Then `exists_unitary_root_nhds` gives `U`,
and for `g` with coordinates in `U` and its root `y ∈ S`, the element `φ(y)` satisfies
`φ(y) τ_v(φ y) = φ(y σ(y)) = 1`, `g.eval₂ ψ (φ y) = φ(g(y)) = 0`, and the independence of its
powers over `A` follows from `eq_zero_of_linearIndependent` and injectivity of `φ`.

**The places (`numberFieldUnitaryLocalRootNeighborhood`).** At an archimedean place `w` the
completion carries `Langlands.Global.AdelicSpaceLocalFields.infiniteNormedField F w`, and at a
finite place `v` it carries `Langlands.Global.AdelicSpaceLocalFields.normedField (𝓞 F) F v`,
complete by `Langlands.Global.AdelicSpaceLocalFields.completeSpace`. Both norms induce the
given topology of `Global.placeCompletion F v`, so the open set of `local_root_neighborhood`
(applied with `cE = conjugation F E`, involutive by `conjugation_involutive`) is open for the
topology of the statement.

## Sources

- Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.7, proof of Theorem
  6.28, printed p. 364 (PDF p. 374), equation (6.44) and the unitary Krasner lemma. The source
  applies local openness to the characteristic-polynomial coefficient map on the unitary locus.
  Registered source `platonov-rapinchuk-1994-algebraic-groups-number-theory`, SHA-256
  `c333b953ca0ace6306663f648cd853a75da55023bf873e0ef2688d997216717f`.
- Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.6, Steps 1–2, printed
  pp. 80–81 (PDF pp. 86–87). Newton approximation identifies the nearby separable quotients.
  Finiteness of their involutions then gives compatibility with the ambient involution at the
  chosen places. Registered source `kneser-1969-galois-cohomology-classical-groups`, SHA-256
  `55309defa8ea7b311d5d6959832029ee6a0245330b7d0e45b2524e62283809a0`.
