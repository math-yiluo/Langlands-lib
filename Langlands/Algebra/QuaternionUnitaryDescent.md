# Descent of a quaternion algebra with a unitary involution

Helper module for the proof of `Langlands.LocalUnitaryDivisionCommutativeStatement`.

Setting: fields `K ⊆ L` (`[Algebra K L]`), a finite-dimensional central division `L`-algebra `D`
with a compatible `K`-algebra structure (`IsScalarTower K L D`), `hd : reducedDegree L D = 2`,
a unitary involution `τ` relative to `σ : L →+* L`, and `hσK : σ` fixes `K`.

* `fixedSubalgebra hd hτ hσK` is `D₀ = {x | β x = x}` for `β = τ ∘ γ`
  (`Langlands.Algebra.QuaternionUnitaryInvolution`); it is a `K`-subalgebra because `β` is a ring
  endomorphism fixing `K` (`beta_algebraMap_base`).
* `betaLinear`: `β` is `K`-linear. `add_beta_mem`: `y + β y ∈ D₀`.
* `descent_eq` (Galois descent): for `θ ∈ L`,
  `(σθ - θ) y = σθ · (y + β y) - (θ y + β (θ y))`, a combination of two elements of `D₀`.
* `commute_of_commute_fixed`: if `σ θ ≠ θ`, an element commuting with `D₀` commutes with `D`
  (apply `descent_eq` and cancel the nonzero scalar `σθ - θ`).
* `two_mul_finrank_fixed`: `2 [D₀ : K] = [D : K]`. The `K`-linear maps
  `D₀ × D₀ → D, (a, b) ↦ a + θ b` and `D → D₀ × D₀, y ↦ (y + β y, θ y + β (θ y))` are both
  injective (apply `β`, resp. `descent_eq`), so the dimensions bound each other.

With `[FiniteDimensional K L]`:

* `fixed_finiteDimensional`, and `fixedDivisionRing`: `D₀` is a finite-dimensional domain over
  `K`, hence a division ring (`divisionRingOfFiniteDimensional`).
* `finrank_fixed`: `[D₀ : K] = 4` when `[L : K] = 2`, since `[D : K] = 2 · 4`.
* `fixed_isCentral`: if moreover `σ θ ≠ θ` for some `θ` and the `σ`-fixed elements of `L` are
  exactly `K` (`hfix`), then `D₀` is central over `K`: a central element of `D₀` is central in
  `D` (`commute_of_commute_fixed`), hence a scalar `ℓ ∈ L`, and `β`-fixed, so `σ ℓ = ℓ` and
  `ℓ ∈ K`.
* `reducedDegree_fixed`: `reducedDegree K D₀ = Nat.sqrt 4 = 2`.
* `nrd_fixed`: for `y ∈ D₀`, `Nrd_{D/L}(y) = Nrd_{D₀/K}(y)` (mapped into `L`). If `y` is a scalar
  of `L` it lies in `K` and both sides are its square. Otherwise its minimal polynomials over `L`
  and over `K` have degree at least two and divide the reduced characteristic polynomials, which
  have degree two; so they are equal, the minimal polynomial over `L` is the image of the one
  over `K` (`minpoly.dvd_map_of_isScalarTower`, equal degrees), and the constant coefficients
  (`reducedCharpoly_coeff_zero_two`) agree.
