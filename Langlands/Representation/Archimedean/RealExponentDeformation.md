# Deforming the exponents of real standard modules

Namespace `Langlands.Archimedean.RealExponentDeformation`.

This is an internal module. It supports the proof of `RealInducedSwapStatement`. The route
there moves the exponents of the swap by a complex parameter `z`, uses actual intertwiners for
generic `z ≠ 0`, and passes to the limit `z → 0`. This module supplies the tools that keep the
`(𝔤, K)`-equivariance in that limit.

The basic fact is the compact picture of a principal series. By the Iwasawa decomposition
`GL_n(ℝ) = B · O(n)`, a function in a principal series is determined by its values on `O(n)`,
and those values do not see the exponents of the characters. So two standard modules whose
lists differ only in their exponents can be compared on `O(n)`. The compact action is the same
for both. The right derivative along `X` changes by an explicit multiplication term, given by
the formula below. Everything is proved in Lean from Library results; no literature statement
is formalized here.

Throughout, `KF n ds` abbreviates the `O(n)`-finite functions
`kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)` of the real standard module of
the list `ds` of real blocks.

## Right derivatives of functions agreeing on `O(n)`

`diagWeight c X k = ∑ᵢ cᵢ (k X kᵀ)ᵢᵢ` for `c : Fin n → ℂ`, a real matrix `X` and
`k ∈ GL_n(ℝ)`. `diagWeight_of_eq_mul` says that `diagWeight` is linear in `c`, in the form
needed for `c = w • c'`.

`fderiv_skew_eq`: let `F` and `F'` be smooth on `GL_n(ℝ)` and agree on `O(n)`. Let `k ∈ O(n)`
and let `Z` be antisymmetric. Then the derivatives of their matrix extensions at `k` in the
direction `Z k` are equal. The proof differentiates along the curve `t ↦ exp(tZ) k`, which lies
in `O(n)`.

`rightDerivative_eq_of_eqOn` (**exponent change**): let `F ∈ PS(χ)` and `F' ∈ PS(χ')` agree on
`O(n)`, where `χᵢ(eˣ) = e^{τᵢ x}` and `χ'ᵢ(eˣ) = e^{τ'ᵢ x}`. Then for `k ∈ O(n)`

`R(X) F (k) = R(X) F' (k) + (∑ᵢ (τᵢ - τ'ᵢ) (k X kᵀ)ᵢᵢ) F(k)`.

Here `R(X)` is `rightDerivative (matrixModel ℝ n) X`. The proof splits `Y = k X kᵀ` into an upper
triangular part `U` and an antisymmetric part `Z`, as `RealJacquetFrobenius.upperPart` and
`skewPart`. Then `k X = U k + Z k`. Along `U k` the Library formula
`fderiv_upperTriangular_of_isExpEquivariant` gives
`∑ᵢ (τᵢ + (n-1)/2 - i) Uᵢᵢ F(k)`, and the same for `F'` with `τ'`. Note that `Uᵢᵢ = Yᵢᵢ`. Along
`Z k` the two derivatives agree by `fderiv_skew_eq`. Subtracting gives the formula.

There are two specializations:

* `rightDerivative_eq_of_eqOn_realPosition`: the same formula for the position characters
  `realPositionCharacter ds` and `realPositionCharacter ds'` of two lists of real blocks, with
  `τ = realPositionExponent ds` and `τ' = realPositionExponent ds'`.
* `rightDerivative_eq_of_exponent_shift`: suppose `realPositionExponent ds' i =
  realPositionExponent ds i + z aᵢ` for all `i`. Then for `F ∈ PS(ds)` and `F' ∈ PS(ds')` that
  agree on `O(n)`, `R(X) F' (k) = R(X) F (k) + z · diagWeight a X k · F(k)` on `O(n)`.

## Transfer between exponents

`blockFourierCoefficient_eq_of_eqOn`: on `O(n)`, the block Fourier coefficients of a function
depend only on its values on `O(n)`.

`IsShapeCompatible ds ds'` holds when two conditions hold:
* every position character of `ds'` has the same value at `-1` as that of `ds`;
* every induction block of `ds'` at position `p` has absolute weight at most that of an
  induction block of `ds` at the same position `p`.

`realPositionCharacter_signUnit_eq` and `isSignCompatible_one` turn the first condition into the
sign compatibility `RealKTypeTransport.IsSignCompatible 1` used by the Library transport.
`eqOn_extension_transport` says that the extension of the transport by `κ₀ = 1` of `f` agrees
with `f` on `O(n)`.

`exists_eqOn` (**transfer**): let `realRank ds' = n` and `IsShapeCompatible ds ds'`. Then every
`f : KF n ds` agrees on `O(n)` with some `f' : KF n ds'`. The candidate `f'` is the extension of
`f|O(n)` with the exponents of `ds'`. It is `O(n)`-finite in `PS(ds')` by
`RealKTypeTransport.extension_transport_mem`. It lies in the standard module of `ds'` by
`RealKTypeTransport.mem_realStandardModule_of_unitaryCompact`: the vanishing of the Fourier
coefficients in the window of an induction block of `ds'` follows on `O(n)` from that for the
wider window of `ds`.

`SameShape x y` holds for two characters of equal parity, or two inductions of equal weight.
For lists related by `List.Forall₂ SameShape`:
* `realRank_eq_of_forall₂` says the ranks agree;
* `isShapeCompatible_of_forall₂` says they are shape compatible.

Exponents may differ arbitrarily in both cases.

## Limits of intertwiners

`IsExponentShift n ds ds' a z` is a structure with these fields:
* `rank` and `rank'`: both lists have rank `n`;
* `forward` and `backward`: shape compatibility in both directions;
* `exponent`: `realPositionExponent ds' i = realPositionExponent ds i + z aᵢ` for every `i`.

`IsExponentShift.of_forall₂` derives it from `List.Forall₂ SameShape ds ds'`, the rank of `ds`
and the exponent identity.

`evalAt ds g` is evaluation at `g` as a linear functional on `KF n ds`. `ext_of_eqOn` says that
two elements of `KF n ds` that agree on `O(n)` are equal.

`isRealStandardIntertwiner_of_modulo_bot`: an intertwiner modulo `⊥`
(`IsRealIntertwinerModulo n ds es ⊥ q`) is an intertwiner `IsRealStandardIntertwiner n
(realStandardRep n es) (realStandardLie n es) ds q`.

`isRealStandardIntertwiner_of_tendsto` (**limits of intertwiners**). Data and hypotheses:
* fixed lists `ds` and `es`;
* a nontrivial filter `L ≤ 𝓝 0` on `ℂ`;
* linear maps `S z : KF n ds →ₗ[ℂ] KF n es` for `z : ℂ`;
* `hS`, weak continuity at `0` along `L`: for every `f` and every linear functional `ℓ` on
  `KF n es`, `ℓ (S z f) → ℓ (S 0 f)` along `L`;
* `hev`: for `z` eventually in `L`, `z ≠ 0`, `IsExponentShift n ds (ds' z) a z` and
  `IsExponentShift n es (es' z) b z` hold. Also there is an intertwiner `T` from `KF n (ds' z)`
  to the standard module of `es' z`, such that `T f'` agrees with `S z f` on `O(n)` whenever
  `f'` agrees with `f` on `O(n)`.

Conclusion: `S 0` is an intertwiner from the standard module of `ds` to that of `es`
(`IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds (S 0)`).

Proof. Evaluation at a point and evaluation of a right derivative at a point,
`(evalAt es g).comp (realStandardLie n es (1 ⊗ₜ X))`, are linear functionals. So `hS` gives
pointwise convergence of `S z f` and of `R(X)(S z f)`.

*Compact equivariance.* For eventual `z`, transfer `f` to `f'` in `KF n (ds' z)` by `exists_eqOn`.
Then `T` commutes with right translation by `k`, so the values of `S z (R(k) f)` and of
`R(k) (S z f)` at a point `g ∈ O(n)` are equal. Take the limit, using uniqueness of limits in
`ℂ`. Then use `ext_of_eqOn`.

*Lie equivariance.* First build a correction `P ∈ KF n ds` with
`P = diagWeight a X · f` on `O(n)`. Take one eventual `z₀ ≠ 0`, transfer `f` to `f₀` for
`ds' z₀`, and transfer `R(X) f₀` back to `g₀` for `ds`. Set `P = z₀⁻¹ (g₀ - R(X) f)`; the
exponent-shift formula shows that it works. For eventual `z`, transfer `f` to `f'`. The
exponent-shift formula then gives, on `O(n)`:
* `R(X) f' = R(X) f + z P`;
* `R(X) (T f') = R(X) (S z f) + z · diagWeight b X · S z f`.

Since `T` intertwines `R(X)`, at `g ∈ O(n)` this gives

`R(X)(S z f)(g) = S z (R(X) f)(g) + z · S z P (g) - z · diagWeight b X g · S z f (g)`.

As `z → 0` along `L`, the right side tends to `S 0 (R(X) f)(g)` and the left side tends to
`R(X)(S 0 f)(g)`. Conclude with `ext_of_eqOn`.

The weak continuity hypothesis holds, for example, when each `z ↦ S z f` is weakly analytic at
`0`.

## Block multiplier maps on `O(n)`

`blockFrobMap_eqOn`: consider two Frobenius data `IsBlockFrobData n ds es p ε σ μ` and
`IsBlockFrobData n ds' es' p ε' σ' μ` with the same position `p` and the same multiplier `μ`.
The lists, parities and signs may differ. If `f' : KF n ds'` agrees with `f : KF n ds` on
`O(n)`, then `blockFrobMap h' f'` agrees with `blockFrobMap h f` on `O(n)`. This follows from
the Library formula `blockFrobMap_apply_of_mem` (on `O(n)`, `blockFrobMap h f` is
`(2π)⁻¹ ∑ᵢ μᵢ` times the block Fourier coefficients of `f`) and
`blockFourierCoefficient_eq_of_eqOn`.

## Scope

No assertion is made about any particular family `S z`. The shifted swap maps of that route are meant
to be fed into `isRealStandardIntertwiner_of_tendsto`, with `blockFrobMap_eqOn` used to identify
them on `O(n)` with actual intertwiners at moved exponents. That identification is not part of
this module. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
