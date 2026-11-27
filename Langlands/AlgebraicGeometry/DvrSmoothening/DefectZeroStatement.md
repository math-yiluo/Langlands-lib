# Points of defect zero lie in the smooth locus

The module `Langlands.AlgebraicGeometry.DvrSmoothening.DefectZeroStatement` contains one
proposition, `DefectZeroSmoothAtStatement`, and proves nothing.

## The proposition

`DefectZeroSmoothAtStatement` quantifies over a universe `u`, a discrete valuation ring `R`, an
`R`-algebra `A` of finite type and a discrete valuation ring `R'` with a local homomorphism
`R → R'` satisfying `Langlands.AlgebraicGeometry.IsRamificationIndexOne R R'` (the maximal ideal
of `R` generates that of `R'` and the residue field extension is geometrically reduced), and an
irreducible element `ϖ` of `R` (a uniformizer). Its hypotheses are

1. `Algebra.Smooth R (Localization.Away (algebraMap R A ϖ))`: the generic fibre `A[1/ϖ]` of
   `Spec A` is smooth (over `R`, equivalently over the fraction field of `R`, of which `A[1/ϖ]`
   is an algebra);
2. `φ : A →ₐ[R] R'` has `pointDefect φ = 0`.

Its conclusion is that the prime ideal `φ⁻¹(𝔪_{R'})`, the image of the closed point of
`Spec R'`, lies in `Algebra.smoothLocus R A`, i.e. `A` is smooth over `R` at it.

## Source

Bosch, Lütkebohmert and Raynaud, *Néron Models* (1990), literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models` (SHA-256
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`; printed page `p` is PDF
page `p + 7`):

- §3.3, Lemma 1, printed p. 65: an `R^{sh}`-valued point `a` of an `R`-scheme `X` of finite
  type with smooth generic fibre factors through the smooth locus of `X` if and only if
  `δ(a) = 0`. The proposition is the "if" direction for an affine `X = Spec A`. The proof given
  there uses no flatness of `X` (it compares `X` near `a_k` with a smooth subscheme of affine
  space cut out by equations with independent differentials).
- §3.6, printed p. 79: "Without changes, the proof of 3.3/1 shows that `δ(a) = 0` if and only if
  `a` factors through the smooth locus of `X`" for `R'`-valued points with `R'` of ramification
  index 1 over `R` whose generic fibre lies in the smooth locus of `X_K` (BLR 3.6, Definition 1,
  printed p. 78, defines ramification index 1).

The Stacks Project, Section 16.4 (literature ID
`stacks-neron-desingularization-16-4-2026-11-26`, folder SHA-256
`5c2e7a6b992fb9221ca40b290827d82058a63822d0ca513fceb788a575fb13b2`, file `0BJ1.html`),
Lemma 16.4.4 (tag 0BJ5), proves the same conclusion for flat `A`, in terms of the cokernel of
`I/I² ⊗ Λ → Ω_{B/R} ⊗ Λ` for a presentation `B → A`, which is `Λ ⊗_A Ω_{A/R}`.

The factorization of `a` through the smooth locus is expressed at the closed point only; the
generic point of `Spec R'` maps into the generic fibre, which is smooth by hypothesis 1.
