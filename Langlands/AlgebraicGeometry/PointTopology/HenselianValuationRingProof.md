# A non-archimedean field is henselian exactly when its valuation ring is

This module proves `Langlands.AlgebraicGeometry.PointTopology.HenselianIffValuationRingHenselianStatement`:

```lean
theorem henselianIffValuationRingHenselian : HenselianIffValuationRingHenselianStatement.{u}
```

The statement concerns a non-archimedean nontrivially normed field `K` (`IsUltrametricDist K`) and a subring `O` that is its closed unit ball (`x ∈ O ↔ ‖x‖ ≤ 1`). It says that `IsHenselianValuedField K` holds if and only if `HenselianLocalRing O`. This is the criterion that Conrad cites on printed p.14 of *Weil and Grothendieck approaches to adelic points* (December 31, 2011), from Berkovich [Ber, 2.4.3].

## Ingredients

The module uses these results from the Library:

* `ValHensel v` (module `ClassFieldTheory.Local.SeparableInertiaNormHensel`): simple-root Hensel lifting for a real valuation `v`, stated in field terms. A monic integral polynomial `f` and an integral `a₀` with `v (f a₀) < 1` and `v (f' a₀) = 1` give a root `a` with `v (a - a₀) < 1`.
* `exists_root_one_add_of_hensel` (same module): Newton's form of Hensel lifting for equations `a₀ + y + ∑_{k ≥ 2} c_k y^k = 0` with `v a₀ < 1` and integral `c_k`.
* `valHensel_of_henselian` (module `SeparableInertiaNormAmbient`): a henselian valuation ring satisfies `ValHensel`.
* `valHensel_comap` (module `SeparableInertiaNormReduction`): Galois descent of `ValHensel`.
* `Langlands.LocalGalois.Separable.sepClosed_henselian`: every valuation ring of a separably closed field is henselian.
* `HenselianIffSeparablyClosed.isHenselianValuedField_of_separableClosure_eq_bot` and `HenselianIffSeparablyClosed.pullback` (module `HenselianIffSeparablyClosedProof`).

The norm valuation is Mathlib's `NormedField.valuation`, `x ↦ ‖x‖₊`. The lemmas `val_lt_one_iff`, `val_le_one_iff` and `val_eq_one_iff` translate its conditions into conditions on the norm.

## Proof

### The unit ball

The unit criterion is the existing `HenselianUnitBall.isUnit_iff_norm_eq_one`
from [HenselianIntegralPointsCompactProof](../AlgebraicSpace/HenselianIntegralPointsCompactProof.md):
an element of `O` is a unit exactly when its norm is `1`. The module reuses it
to prove the following facts in the namespace `HenselianValuationRing`:

* `nonunit_iff`: an element of `O` is a nonunit exactly when its norm is `< 1`.
* `isLocalRing`: `O` is a local ring, since nonunits are closed under addition by the ultrametric inequality.
* `valHensel_of_henselianLocalRing`: if `O` is a henselian local ring, then `ValHensel` holds for the norm valuation. Lift the polynomial to `O[X]` and apply `HenselianLocalRing.is_henselian`.
* `henselianLocalRing_of_valHensel`: conversely, `ValHensel` for the norm valuation makes `O` a henselian local ring. Map the polynomial to `K[X]`. The root that `ValHensel` provides lies in `O` by the ultrametric inequality.

### Henselian `O` implies henselian `K`

* `exists_root_of_newton` is Newton's lemma. Take `g ∈ K[X]` and `a, s ∈ K`, and put `D = g'(a) s`. Suppose `‖g(a)‖ < ‖D‖`, and suppose `‖t_k s^k‖ ≤ ‖D‖` for all `k ≥ 2`, where the `t_k` are the Taylor coefficients of `g` at `a`. Then `g` has a root in `K`. Indeed, `g(a + s y) = D · (g(a)/D + y + ∑_{k ≥ 2} (t_k s^k / D) y^k)`, and `exists_root_one_add_of_hensel` solves the bracket.
* `separableClosure_eq_bot`: `ValHensel` for the norm valuation implies that `K` is separably closed in its completion `K̂`.
  * Let `x ∈ K̂` be separable over `K`, with minimal polynomial `g`. Then `g'(x) ≠ 0`. Put `δ = ‖g'(x)‖ / 2`, and let `C ≥ 1` bound `‖t_k(x)‖ + 1` for `k ≤ deg g`. Choose `s ∈ K` with `0 < ‖s‖ < min 1 (δ / C)`.
  * The set of `y ∈ K̂` with `‖g'(y)‖ > δ`, `‖g(y)‖ < δ ‖s‖`, and `‖t_k(y)‖ < ‖t_k(x)‖ + 1` for `k ≤ deg g` is open, by continuity of polynomial evaluation. It contains `x`. Since `K` is dense in `K̂`, it contains some `a ∈ K`.
  * For this `a`, the hypotheses of Newton's lemma hold, because `‖s‖^k ≤ ‖s‖²` for `k ≥ 2` and `t_k = 0` for `k > deg g`. So `g` has a root in `K`. Since `g` is irreducible, it has degree `1`, and `x ∈ K` (`minpoly.natDegree_eq_one_iff`).
* Combining this with `isHenselianValuedField_of_separableClosure_eq_bot` shows that `K` is henselian.

### Henselian `K` implies henselian `O`

`valHensel_of_isHenselianValuedField` proves that `ValHensel` holds for the norm valuation when `K` is henselian.

* Let `Ω` be the separable closure of `K`, and let `w` be the unique absolute value on `Ω` extending the norm of `K`.
* For `σ ∈ Gal(Ω/K)`, the absolute value `w ∘ σ` also extends the norm, so `w ∘ σ = w`.
* `w` is ultrametric. The norm of `WithAbs w` takes natural numbers to their norms in `K`, which are at most `1` (`isUltrametricDist_of_forall_norm_natCast_le_one`). So `x ↦ w x` is a valuation `ω : Valuation Ω ℝ≥0`.
* Its valuation ring is henselian (`sepClosed_henselian`), so `ValHensel ω` holds. Galois-fixed elements of `Ω` lie in `K` (`InfiniteGalois.mem_bot_iff_fixed`). By `valHensel_comap`, `ValHensel` holds for `ω.comap (algebraMap K Ω)`, which is the norm valuation of `K`.

The entry theorem combines `henselianLocalRing_of_valHensel` with this result for one direction. For the other direction, it combines `valHensel_of_henselianLocalRing`, `separableClosure_eq_bot` and `isHenselianValuedField_of_separableClosure_eq_bot`.
