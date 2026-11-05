# Unit norm surjectivity inside a Galois ambient field

Author: Worker 1512. This is the fourth helper module of the proof of
`Langlands.ClassFieldTheory.Local.SeparableInertiaUnitNormSurjectivity` (see
`SeparableInertiaNormProof.md`). It imports `SeparableInertiaNormReduction` and
`SeparableUnramifiedArithmeticProof`, and Mathlib (infinite Galois theory, normal closures, Henselian rings, discrete
valuation rings, valuation subrings). All declarations are in
`Langlands.ClassFieldTheory.Local.SeparableInertiaNorm`.

## From ring-theoretic to valuation-theoretic hypotheses

Let `K` be a field and `v : Valuation K ℝ≥0`, with valuation subring
`v.valuationSubring`.

- The imported `Langlands.LocalGalois.Separable.mem_maximalIdeal_iff_lt`
  and `Langlands.LocalGalois.Separable.isUnit_iff_eq_one` state that an element of
  the valuation subring lies in the maximal ideal iff `v x < 1`, and is a unit
  iff `v x = 1`.
- `exists_lift`, `eval_lift`: an integral polynomial lifts to
  `v.valuationSubring[X]`, compatibly with evaluation.
- `valHensel_of_henselian`: `[HenselianLocalRing v.valuationSubring]` implies
  `ValHensel v`. The lifted polynomial is monic, its value at `a₀` lies in the
  maximal ideal, and its derivative at `a₀` is a unit, so
  `HenselianLocalRing.is_henselian` applies.
- `valResidueRoot_of_isAlgClosed`: `[IsAlgClosed (ResidueField v.valuationSubring)]`
  implies `ValResidueRoot v`. The reduction of the lifted polynomial has a
  nonzero coefficient in positive degree, so its degree is nonzero and
  `IsAlgClosed.exists_root` gives a residue root. Any lift of that root works.
- `exists_valUniformizer_of_dvr`: `[IsDiscreteValuationRing v.valuationSubring]`
  gives a `ValUniformizer`. Take an irreducible `ϖ`; every nonzero integral
  element is a unit times `ϖ ^ n` (`IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`).
- `exists_prime_natCast`: some prime `p` has `v (m : K) = 1` for every `m` with
  `p ∤ m`. If some positive integer has value `< 1`, the least such integer is
  prime (a factorization into smaller integers would have value `1`). Every `m`
  prime to it then has value `1` by division with remainder and the ultrametric
  equality. Otherwise every positive integer has value `1`, and `p = 2` works.
  There is no assumption on the residue characteristic.
- `IntPoly.mul`, `IntPoly.multiset_prod_X_sub_C`: products of integral
  polynomials, and `∏ (X - r)` over integral roots `r`, are integral.

## Conjugates

Let `K → L → Ω` be a tower with `Ω / K` normal and `w : Valuation Ω ℝ≥0`
invariant under `Gal(Ω/K)`.

- `val_eq_of_mem_aroots`: every root in `Ω` of the minimal polynomial of `y`
  has the value of `y`. Such a root is `σ y` for some `σ`
  (`minpoly.exists_algEquiv_of_root'`).
- `val_norm_eq`: for `L / K` finite and `x : L`,
  `w (N_{L/K} x) = w x ^ [L : K]`. Proof: `Algebra.norm_eq_prod_roots` writes
  the norm as the product of the roots of the minimal polynomial of `x`, raised
  to the power `[L : K(x)]`. All these roots have value `w x`, and
  `[K(x) : K] [L : K(x)] = [L : K]`.

## The ambient hypotheses

`Ω / U` is a Galois extension, possibly infinite. The structure `AmbientHyp w`
(an internal interface) for `w : Valuation Ω ℝ≥0` bundles:

- `inv`: `w (σ x) = w x` for every `σ : Gal(Ω/U)`;
- `hensel`: `ValHensel w` on `Ω`;
- `residueRoot`: `ValResidueRoot` for `w` restricted to `U`;
- `unif`: a `ValUniformizer` for `w` restricted to `U`.

Consequences:

- `inv_of`: invariance under `Gal(Ω/K)` for every intermediate `K`, by
  `AlgEquiv.restrictScalars`.
- `res`: every integral `x : Ω` is congruent to an integral `c : U`. The minimal
  polynomial `f` of `x` over `U` is integral, since its roots are conjugates of
  `x` and `f = ∏ (X - r)`. It is monic of positive degree, so root finding
  gives `b : U` with `w (f b) < 1`. Since
  `f b = ∏ (b - r) = ∏ σ_r (b - x)` and all factors have the same value
  `w (b - x) ≤ 1`, that value must be `< 1`.
- `exists_norm_eq_of_tower`: let `U → E → L → M → Ω` be a tower with `E / U` and
  `M / E` finite and `M / E` Galois. Then every unit `u` of `E` is
  `N_{L/E} x` for a unit `x` of `L`. The proof verifies `ReductionHyp` for
  `w` restricted to `M`, over `E`:
  - `inv` by extending automorphisms to `Ω` (`AlgEquiv.liftNormal_commutes`);
  - `hensel` by `valHensel_comap`, since `Ω / M` is Galois
    (`InfiniteGalois.mem_range_algebraMap_iff_fixed`);
  - `residueRoot` by `valResidueRoot_comap` from `U` and `res`;
  - `res` from `res`, through `U → E`;
  - `natCast` from `exists_prime_natCast`;
  - `disc` with `D = [M : E] [E : U]` and `q = w ϖ` for the uniformizer `ϖ`
    of `U`. For `x : M`, `w (N_{E/U} N_{M/E} x) = w x ^ D` by `val_norm_eq`
    twice, and this is a power of `w ϖ`;
  - `small` from `ϖ`.

  `ReductionHyp.exists_norm_eq` gives a unit `z : M` with `N_{M/E} z = u`.
  Then `x = N_{M/L} z` is a unit of `L`, since `w x = w z ^ [M : L] = 1` by
  `val_norm_eq`. Finally `N_{L/E} x = u` by `Algebra.norm_norm`.
- `AmbientHyp.exists_norm_eq`: for intermediate fields
  `E : IntermediateField U Ω` with `[E : U]` finite and
  `L : IntermediateField E Ω` with `[L : E]` finite, every `u : E` with
  `w u = 1` is `N_{L/E} x` for some `x : L` with `w x = 1`. Apply
  `exists_norm_eq_of_tower` with `M = IntermediateField.normalClosure E L Ω`,
  which is finite Galois over `E`. Here `Ω / E` is Galois by
  `IsGalois.tower_top_of_isGalois`.
