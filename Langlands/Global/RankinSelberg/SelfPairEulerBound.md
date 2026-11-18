# Bounds on finite Euler products from partial Whittaker integrals

Module `Langlands.Global.RankinSelberg.SelfPairEulerBound`, namespace
`Langlands.Global.RankinSelbergGlobal.SelfPairEulerBound`.

This internal helper belongs to the positivity proof of Jacquet–Shalika I, Lemma (5.2)
(Task 6821). It contains no `Prop`-valued statement definitions.

For a finite set `A` of finite places, let `Ψ_A(s)` be the integral of the equal-rank global
Whittaker integrand `W(g) W'(g) Φ(e_n g) |det g|^s` over the classes
`unipotentIntegralClasses F n A`. These are the classes whose representative is in
`N_n(F_v) GL_n(𝒪_v)` at every finite `v ∉ A`. The Library's one-place Euler step
`EqualEulerReduction.setIntegral_insert` gives

`Ψ_(A ∪ {v})(s) = L(s, Π_v × Π'_v) Ψ_A(s)`,

but only for `Re s > localRadius r C C'`, far to the right of `Re s = 1`. This module
continues these identities to `Re s > 1` and turns them into bounds on finite Euler products
at real points.

## Provenance

The finite Euler identities are JS I's comparison of partial integrals with local
`L`-factors (JS I, §4, (4.5)–(4.6), pp. 550–551), as formalized in the Library through
`setIntegral_insert`. Bounding the finite products by `Ψ(σ)/Ψ_(S₁)(σ)` is the positivity
argument of the self-pair route. It parallels the use of positivity in the proof of JS I,
(4.8), p. 553, and replaces the local nonvanishing used in JS I's proof of Lemma (5.2),
p. 555. Every hypothesis is stated explicitly.

## Main results

**Abstract continuation** (any index type `Idx` with decidable equality):

* `eq_prod_of_insert`: if `Ψ (insert v E) s = L v s * Ψ E s` for `v ∉ E` and `R < Re s`, then
  `Ψ E s = (∏_(v ∈ E) L v s) * Ψ ∅ s` there. The proof is induction on `E`.
* `eq_prod_of_insert_of_differentiableOn`: suppose moreover every `Ψ E` and every `L v` is
  holomorphic on `σ₀ < Re s`. Then the finite product identity holds on `σ₀ < Re s`.
  The proof uses the identity theorem on a half-plane, `LandauMellin.eqOn_halfPlane`.
* `norm_prod_le`: suppose `Ψ_E(σ) = (∏ L_v(σ)) Ψ_∅(σ)`, where `Ψ_E(σ)` is a real number in
  `[0, B]` and `Ψ_∅(σ)` is a positive real number. Then `‖∏ L_v(σ)‖ ≤ B / Ψ_∅(σ)`.

**Local factors:**

* `eval_ne_zero`: suppose all Satake parameters at `v` have norm at most `q_v ^ (1/2)`.
  Then the pair Euler polynomial does not vanish at `q_v ^ (-s)` for `Re s > 1`, because
  every `‖α β q_v ^ (-s)‖ ≤ q_v ^ (1 - Re s) < 1`.
* `differentiableOn_partialEulerFactor`: under the same bounds outside `S`, every local
  factor `partialEulerFactor P P' hP hP' v` is holomorphic on `Re s > 1`. The bounds hold
  for unitary cuspidal presentations by JS I, Corollary (2.5).

**The Whittaker integrals:**

* `placeEmb`, `union_insert_eq_cons`, `not_mem_union_map`: bookkeeping that identifies
  `S₁ ∪ (insert v E)` with `Finset.cons v (S₁ ∪ E)` for finite sets `E` of places outside
  `S₁`.
* **`prod_bound`**: its hypotheses are
  * those of `setIntegral_insert` at the set `S₁`: the character `ψ`, the presentations
    `P`, `P'` with exceptional sets in `S₁`, `FiniteAdditiveSupport ψ S₁`,
    `HasSatakeBound`, spherical vectors outside `S₁`, and `Φ` standard outside `S₁`;
  * the bounds `q_v ^ (1/2)` for both spectra outside `S₁`;
  * a nonnegative Mellin weight `f` of the integrand (`SelfPairLandau.IsMellin`);
  * integrability of the integrand on `Re s > 1`;
  * positivity of `∫_(classes integral outside S₁) f e^{σ logDet}` at every real `σ > 1`.

  For every real `σ > 1` it gives an `M` with
  `‖∏_(v ∈ E) partialEulerFactor P P' hP hP' v σ‖ ≤ M` for every finite set `E` of places
  outside `S₁`. Explicitly, `M = Ψ(σ) / Ψ_(S₁)(σ)`, where `Ψ` is the full integral.
* **`prod_bound_of_re_pos`**: the same conclusion when the last hypothesis of
  `prod_bound` is replaced by positivity at one point: there is a real `σ₀ > 1` with
  `Re (partialEqualWhittakerIntegral F S₁ W W' Φ σ₀) > 0`, where `W`, `W'` are the two
  cuspidal Whittaker functions. `SelfPairLandau.setIntegral_real_pos_of_re_pos` turns this
  into the positivity at every real `σ > 1` that `prod_bound` requires. Integrability at
  `σ₀` and `σ` comes from the integrability hypothesis on `Re s > 1`.

## Proof outline of `prod_bound`

Index the partial integrals by finite sets `E` of places outside `S₁`:
`Ψ E s = ∫_(classes integral outside S₁ ∪ E) G s`.

1. *One-place identities.* For `v ∉ E` and `Re s > max (localRadius r C C') 1`,
   `setIntegral_insert` gives `Ψ (insert v E) s = L_v(s) Ψ E s`. Its arguments are the
   Library proofs `UnramifiedWhittaker.unramifiedWhittakerFactorization` and
   `whittakerCellDecomposition`, together with integrability at `s`.
2. *Holomorphy.* Each `Ψ E` is holomorphic on `Re s > 1`, by
   `SelfPairLandau.IsMellin.differentiableOn_setIntegral` applied to the integrability on
   `Re s > 1`. Each `L_v` is holomorphic there, by `differentiableOn_partialEulerFactor`.
3. *Continuation.* `eq_prod_of_insert_of_differentiableOn` gives
   `Ψ E σ = (∏_(v ∈ E) L_v(σ)) Ψ ∅ σ` at every real `σ > 1`.
4. *Positivity.* `SelfPairLandau.IsMellin.setIntegral_real` shows that `Ψ E σ` and
   `Ψ ∅ σ` are the real integrals of `f e^{σ logDet}`. These are nonnegative
   (`setIntegral_real_nonneg`), and `Ψ ∅ σ > 0` by hypothesis.
   `setIntegral_real_mono` bounds `Ψ E σ` by the full integral `Ψ(σ)`.
   `norm_prod_le` concludes.
