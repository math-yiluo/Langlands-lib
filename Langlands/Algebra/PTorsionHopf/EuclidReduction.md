# Reducing primitive generating tuples along additive relations

Author: Worker 1519, as internal infrastructure for the proof of
`Langlands.GroupScheme.RelativeRoot.SmoothCommutativePTorsionVectorStatement`.

Provenance: internal. This is the Euclidean algorithm for the twisted polynomial ring of
`p`-polynomials, carried out directly on generating tuples of a bialgebra; the formulation and
proof are the author's own, and no source statement is translated.

Throughout `k : Type u` is a field and `A : Type u` a commutative `k`-bialgebra.

- `IsPrimitiveGenerating y` for `y : Fin s → A`: every `y i` is primitive and the `y i`
  generate `A` as a `k`-algebra.
- `isPrimitiveElem_pow_char_pow p hx n`: in characteristic `p`, `x ^ p ^ n` is primitive when
  `x` is (the comultiplication is an algebra map and Frobenius powers are additive in
  `A ⊗ A`).
- `eq_zero_of_aeval_eq_zero hx hf h` (for `IsDomain A`): a primitive element annihilated by a
  nonzero polynomial is `0`. It would be integral over `k`, hence a unit of the domain, while
  its counit is `0`.
- `relTerm g`: `0` for `g = 0`, and `natDegree g + 1` otherwise; `relTerm_of_ne_zero`,
  `relTerm_zero`.

## Euclid reduction

`exists_isPrimitiveGenerating_of_relation p N y f hy hf hne hrel hN`: assume `IsDomain A`,
`p` prime, `CharP k p` and `PerfectRing k p`. Let `y : Fin (s + 1) → A` be primitive
generating, `f : Fin (s + 1) → k[X]` additive polynomials not all zero, with
`∑ i, aeval (y i) (f i) = 0` and `∑ i, relTerm (f i) ≤ N`. Then there is a primitive
generating tuple of length `s`.

Proof as implemented, by induction on `N`.

- If exactly one `f a` is nonzero, then `aeval (y a) (f a) = 0`, so `y a = 0`, and the tuple
  without the index `a` (`Fin.succAbove`) still generates.
- Otherwise choose `a` with `f a ≠ 0` of minimal degree and `b ≠ a` with `f b ≠ 0`. By
  `IsAdditivePoly.natDegree_eq_pow` the degrees are `p ^ ea ≤ p ^ eb`. Put
  `q = p ^ (eb - ea)` and choose `c` with `c ^ p ^ ea = lc(f b) / lc(f a)`
  (`iterateFrobeniusEquiv`). Replace `y a` by `y a + c • (y b) ^ q` (still primitive, and
  the old tuple is recovered from the new one) and `f b` by `f b - (f a).comp (C c * X ^ q)`
  (still additive). By additivity of `f a` the relation is preserved. The composite has the
  same degree and leading coefficient as `f b`, so the new `f b` has smaller `relTerm`, and
  the induction hypothesis applies.
