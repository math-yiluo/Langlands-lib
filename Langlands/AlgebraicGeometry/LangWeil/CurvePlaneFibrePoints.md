# Rational points of a fibre and of its hypersurface model

Lean module: `Langlands.AlgebraicGeometry.LangWeil.CurvePlaneFibrePoints`, namespace
`Langlands.AlgebraicGeometry.LangWeil.CurvePlane`.

This module is a helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.FamilyCurvePlaneComparisonStatement` (Task 5581).
Provenance: internal. It specializes the uniform hypersurface model of the Library
(`Langlands.Algebra.GenericIrreducibilitySpreading.exists_hypersurfaceModel_uniform_of_separablyClosed_range`)
to a finite field and compares rational points, as in the reduction of the curve case of
Lang–Weil to plane curves (Tao, *The Lang–Weil bound*, Section 2; registered source
`tao-2012-lang-weil-bound`). The exact statements below are not in the literature.

## Statements

- `exists_pow_eq_pow_of_expChar`: if `A` is a domain of exponential characteristic `q` and
  `κ` is a field over `A` of exponential characteristic `p`, then `q ^ e = p ^ n` for some
  `n`. *Proof.* If `q = 1` take `n = 0`. If `q` is prime, `κ` has characteristic `q`
  (`CharP.of_ringHom_of_ne_zero`), so `p = q` and `n = e`.

- `card_algHom_good_eq`: the hypotheses are the data of a hypersurface model of an
  `A`-algebra `C` over a domain `A`, as produced by the Library lemma above:
  algebraically independent `z : Fin d → C`, `w : C`, a monic
  `F ∈ (MvPolynomial (Fin d) A)[W]` with `F(z, w) = 0`, a nonzero-in-`κ` element `r` such
  that every `r ^ n • c` is integral over `A[z]`, and `g ∈ MvPolynomial (Fin d) A` such that
  every `(g(z) ^ m c) ^ q ^ e` lies in `A[z, w]`, where `q` is the exponential characteristic
  of `A`. Let `κ` be a finite field over `A` in which `F` stays irreducible. Then the number of
  `A`-algebra maps `ψ : C → κ` with `ψ (g(z)) ≠ 0` equals the number of `κ`-algebra maps
  `χ : AdjoinRoot F_κ → κ` with `χ(g_κ) ≠ 0`, where `F_κ` and `g_κ` are the images of `F`
  and `g` over `κ`.

## Proof of `card_algHom_good_eq`

Let `T = κ ⊗[A] C` and `t : C → T` the inclusion `c ↦ 1 ⊗ c`. The Library lemma
`tensor_aeval_injective_of_integral_after_away` shows that
`ψ = aeval (t ∘ z) : κ[X_1, …, X_d] → T` is injective. `F_κ` is monic and prime (irreducible
over the UFD `κ[X]`) and has the root `t w` over `ψ`, so `adjoinRoot_lift_injective_of_monic`
(Library) makes the lift `j : AdjoinRoot F_κ → T` injective. The image of `j` contains `t`
of `A[z, w]` (induction over `Algebra.adjoin`), and
`tensor_uniform_power_containment` (Library) turns the radicial property of `C` over
`A[z, w]` into: every `x : T` satisfies `(t(g(z)) ^ m x) ^ q ^ e ∈ range j`. Since
`q ^ e = p ^ n` for the exponential characteristic `p` of `κ`
(`exists_pow_eq_pow_of_expChar`) and finite fields are perfect,
`bijective_comp_of_radicial` (module `CurvePlaneRadicialPoints`) applied to `j` and
`s = g_κ ∈ AdjoinRoot F_κ` (with `j s = t(g(z))`) gives a bijection between the
`κ`-points of `T` not killing `t(g(z))` and those of `AdjoinRoot F_κ` not killing `s`.
Finally `AlgHom.liftEquiv` identifies `A`-algebra maps `C → κ` with `κ`-algebra maps
`T → κ`, compatibly with evaluation at `g(z)`.
