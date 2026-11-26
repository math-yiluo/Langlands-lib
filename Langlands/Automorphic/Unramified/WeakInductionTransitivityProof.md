# Transitivity of arithmetic weak induction in towers: proof

Module `Langlands.Automorphic.Unramified.WeakInductionTransitivityProof`.

`Langlands.Automorphic.Unramified.weakInductionTransitivity` proves exactly
`Langlands.Automorphic.Unramified.WeakInductionTransitivityStatement` at its six
independent universes `uF`, `uK`, `uE` (the three number fields) and `uV`, `uM`,
`uW` (the presentation carriers of the three classes), with no added premise.
For number fields in an algebra tower `E/K/F` with compact adelic quotients and
actual cuspidal classes `c` over `F`, `b` over `K` and `d` over `E`: if `c` is a
weak induction (`IsoClass.IsWeakInductionOf`) of `b` and `b` is a weak induction
of `d`, then `c` is a weak induction of `d`.

## Source

J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory
of the Trace Formula*, Annals of Mathematics Studies 120 (1989), Chapter III,
§6 (registered source `arthur-clozel-1989-base-change`):

- printed pp. 214–215 (PDF pp. 228–229): the unramified local data of the
  induced representation at a place `v` of `F`, unramified in `E` and with all
  places `w | v` unramified for `π_E`, in the inert case (i), the split case
  (ii) and the composite case (iii), and Definition 6.1, which defines
  automorphic induction by these Hecke eigenvalues at almost all places;
- printed p. 215 (PDF p. 229), the paragraph of the proof of Theorem 6.2
  beginning "To prove the existence": automorphic induction "satisfies the
  usual property of 'induction by stages'" for a diagram `E/E₁/F` of cyclic
  extensions, with the verification in terms of Hecke eigenvalues "left to the
  reader".

The Library relation `IsoClass.IsWeakInductionOf` records the Hecke-eigenvalue
condition of Definition 6.1 as an identity of unramified Euler polynomials,
substituting `X ^ f(w|v)` for the actual residue degree of each place `w | v`
(`SpectralSystem.inducedEulerPolynomial`). It uses no Galois or cyclicity
hypothesis, so the theorem here holds for any tower of number fields; the
cyclic diagrams of the source are a special case.

## Declarations

- `Langlands.Unramified.SpectralSystem.IsArithmeticWeakInductionOf.trans_tower`:
  for a tower `E/K/F` of number fields, if `s` over `F` is an arithmetic weak
  induction (`SpectralSystem.IsArithmeticWeakInductionOf`) of `t` over `K`, and
  `t` is one of `u` over `E`, then `s` is one of `u`.
- `Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.IsWeakInductionOf.trans_tower`:
  the same for actual cuspidal classes `c`, `b`, `d`. The two hypotheses may
  witness the middle class `b` by presentations in different universes, so this
  lemma is slightly more general than the statement, where both use `uM`.
- `Langlands.Automorphic.Unramified.weakInductionTransitivity`: the target,
  obtained by applying the class lemma.

The proof uses three lemmas of the module
`Langlands.Global.Arithmetic.HarrisProposition48PrimeInductionStagesProof`:
`Langlands.Automorphic.Unramified.WeakInduction.finitePlacesAboveTower`,
`Langlands.Automorphic.Unramified.WeakInduction.eventually_forall_finitePlacesAbove`
and
`Langlands.Automorphic.CuspidalOperatorRealization.IsoClass.HasSpectralSystem.sameEulerPolynomials`.

## Implemented proof

### Spectral systems (`IsArithmeticWeakInductionOf.trans_tower`)

1. **Ranks.** The hypotheses give `n = m · [K : F]` and `m = l · [E : K]`, so
   `n = l · ([E : K] · [K : F])`. The tower law `Module.finrank_mul_finrank`
   gives `[K : F] · [E : K] = [E : F]`, hence `n = l · [E : F]`.
2. **Cofinite set of base places.** The second hypothesis holds at all finite
   places `w` of `K` outside a finite set. By
   `eventually_forall_finitePlacesAbove` it holds, for almost all finite places
   `v` of `F`, at every place `w` of `K` above `v`. This cofinite set of `v` is
   intersected with the cofinite set of the first hypothesis. So the exceptional
   places of `t` and of `u` and all places where an `e(w|v)` or `e(z|w)` is not
   one are contracted to finitely many places of `F` and removed.
3. **Places of `E` above `v`.** Fix such a `v`. The equivalence
   `finitePlacesAboveTower v` identifies pairs `(w, z)`, with `w` a place of `K`
   above `v` and `z` a place of `E` above `w`, with the places `z` of `E` above
   `v`; its inverse sends `z` to `(z ∩ 𝓞 K, z)`. For a place `z` above `v` with
   `w = z ∩ 𝓞 K`, the second hypothesis at `w` shows that `z` is not exceptional
   for `u` and that `e(z|w) = 1`; the first gives `e(w|v) = 1`. Then
   `Ideal.ramificationIdx_tower` gives `e(z|v) = e(w|v) · e(z|w) = 1`.
4. **Euler polynomials.** The first hypothesis gives
   `P_v(s) = ∏_{w|v} P_w(t)(X ^ f(w|v))`, and the second, at each `w | v`,
   `P_w(t) = ∏_{z|w} P_z(u)(X ^ f(z|w))`. By `Polynomial.prod_comp`,
   `Polynomial.comp_assoc` and `Polynomial.X_pow_comp`, each factor
   `(P_z(u)(X ^ f(z|w)))(X ^ f(w|v))` is `P_z(u)(X ^ (f(w|v) · f(z|w)))`, and
   `Ideal.inertiaDeg_tower` gives `f(z|v) = f(w|v) · f(z|w)`. The double product
   is reindexed as the product over the places `z` of `E` above `v` by
   `Fintype.prod_sigma` and `Fintype.prod_equiv` along
   `finitePlacesAboveTower v`; this is `inducedEulerPolynomial u v`.

### Cuspidal classes (`IsoClass.IsWeakInductionOf.trans_tower`)

The first hypothesis supplies systems `s_c` of `c` and `t_b` of `b` with
`s_c` an arithmetic weak induction of `t_b`; the second supplies systems `t_b'`
of `b` and `u_d` of `d` with `t_b'` an arithmetic weak induction of `u_d`. The
two systems `t_b` and `t_b'` of the one class `b` may come from different
presentations. `HasSpectralSystem.sameEulerPolynomials` shows that they have
equal Euler polynomials outside a finite set of places of `K`
(`SpectralSystem.SameEulerPolynomials`), and
`SpectralSystem.IsArithmeticWeakInductionOf.of_sameEulerPolynomials` turns the
second relation into `t_b` being an arithmetic weak induction of `u_d`. The
spectral lemma above then makes `s_c` an arithmetic weak induction of `u_d`,
and `s_c`, `u_d` with their attachments to `c` and `d` witness the
conclusion. The attachments of the outer classes are those of the hypotheses,
in the universes `uV` and `uW`.

No spectral rigidity or strong multiplicity one is used: the comparison of the
two systems of `b` uses only that presentations attached to one cuspidal class
have the same Euler polynomials wherever both systems are defined.
