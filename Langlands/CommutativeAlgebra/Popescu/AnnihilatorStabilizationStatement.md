# Ogoma's lemma on annihilators after localization

`Langlands.CommutativeAlgebra.Popescu.AnnihilatorStabilizationStatement` (universe `u`).

**Hypotheses.**
- `A : Type u` is a Noetherian commutative ring.
- `M : Type u` is a finitely generated `A`-module.
- `S` is a submonoid of `A`, and `π ∈ A`.
- For every `m ∈ M`: if `(s π²) • m = 0` for some `s ∈ S`, then `(s' π) • m = 0` for some
  `s' ∈ S`.

**Conclusion.** There is `s ∈ S` such that for every `t ∈ S` and every `m ∈ M`,
`(t s π)² • m = 0` implies `(t s π) • m = 0`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 10.1 (Ogoma, Tag 07FC, printed
p. 24):

> Let A be a Noetherian ring and let M be a finite A-module. Let S ⊂ A be a
> multiplicative set. If π ∈ A and Ker(π : S⁻¹M → S⁻¹M) = Ker(π² : S⁻¹M → S⁻¹M) then
> there exists an s ∈ S such that for any n > 0 we have
> Ker(sⁿπ : M → M) = Ker((sⁿπ)² : M → M).

Proof in the source: "Let K = Ker(π : M → M) and K′ = {m ∈ M | π²m = 0 in S⁻¹M} and
Q = K′/K. Note that S⁻¹Q = 0 by assumption. Since A is Noetherian we see that Q is a
finite A-module. Hence we can find an s ∈ S such that s annihilates Q. Then s works."

## Encoding and scope

- **Kernels as implications.** `Ker(x) ⊆ Ker(x²)` always holds, so each kernel equality is
  the implication `x² • m = 0 → x • m = 0`.
- **The hypothesis.** Every element of `S⁻¹M` is `m/s` with `s ∈ S` a unit there, so
  `Ker(π) = Ker(π²)` on `S⁻¹M` amounts to: for `m ∈ M`, if `π² m` vanishes in `S⁻¹M` then
  so does `π m`. An element of `M` vanishes in `S⁻¹M` exactly when some element of `S`
  kills it. The Lean hypothesis states this directly, without forming `S⁻¹M`.
- **All `t ∈ S`.** The source conclusion is for the multipliers `sⁿ = sⁿ⁻¹ · s`. The Lean
  conclusion is for every `t s` with `t ∈ S`, and `t = sⁿ⁻¹` gives the source case. The
  source proof gives this form: if `(t s π)² m = 0` then `m ∈ K′` (since `t² s² ∈ S`), so
  `s π m = 0`, hence `t s π m = 0`. The proof of Lemma 11.4 (step (13), printed p. 30)
  applies the lemma with multipliers `(s′)^q s`, `q` chosen afterwards, which this form
  covers.
- **Universe.** `A` and `M` are in one universe `u`.
