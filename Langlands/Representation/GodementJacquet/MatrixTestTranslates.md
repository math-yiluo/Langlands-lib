# Two-sided translates of full-matrix test functions

Module `Langlands.Representation.GodementJacquet.MatrixTestTranslates`.
Author: Worker 1112.

Over a commutative topological ring `R` (Hausdorff where Schwartz–Bruhat
restriction is used), for `Φ ∈ SchwartzBruhat (Matrix (Fin n) (Fin n) R)`:

- `matrixTranslate Φ u u'` (definition) is the Schwartz–Bruhat function
  `X ↦ Φ (u X u')` for `u, u' ∈ GL_n(R)` (`matrixTranslate_apply`). It is built
  with `SchwartzBruhat.compLeftInverse`, the left inverse being
  `X ↦ u⁻¹ X u'⁻¹`.
- `eventually_matrixTranslate_eq`: for `(u, u')` in a neighbourhood of `(1, 1)` in
  `GL_n × GL_n`, `Φ (u Y u') = Φ Y` for all `Y`. Proof: on the compact support
  `tsupport Φ`, local constancy of `Φ` and continuity of
  `((u, u'), Y) ↦ u Y u'` give a uniform neighbourhood
  (`IsCompact.eventually_forall_of_forall_eventually`); the same holds for
  `(u⁻¹, u'⁻¹)` by continuity of inversion, and the two facts together handle
  points outside the support, where both values vanish.
- `isLocallyConstant_matrixTranslate`: for continuous `a, b : K → GL_n`, the
  function-valued map `k ↦ (X ↦ Φ (a k X b k))` is locally constant (apply the
  previous result to `(a k' (a k)⁻¹, (b k)⁻¹ b k')`).
- `exists_matrixTranslate_expansion`: if moreover `K` is compact, there are finitely
  many Schwartz–Bruhat `χ l` on `K` and points `r l` with
  `Φ (a k X b k) = ∑ l, χ l k * Φ (a (r l) X b (r l))` for all `k, X`, by the
  Library's `exists_finite_schwartz_expansion`.

In the two-block analytic induction these are applied with `K × K` for a compact
open subgroup `K` and `(k, k') ↦ (k⁻¹, k')`: the test `Φ (k⁻¹ X k')` is a finite
Schwartz–Bruhat combination, in `(k, k')`, of the explicit translates
`matrixTranslate Φ (r l).1⁻¹ (r l).2`. This is the finiteness in the compact
variables used in Godement–Jacquet 1972, Theorem 3.4 (printed 40–41); it is an
internal elementary consequence of local constancy and compact support.
