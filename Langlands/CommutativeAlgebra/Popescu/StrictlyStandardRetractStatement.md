# Retracts in which smooth elements become strictly standard

`Langlands.CommutativeAlgebra.Popescu.StrictlyStandardRetractStatement` (universe `u`).
Let `R` be a Noetherian commutative ring and `B` a finitely presented `R`-algebra (in
`Type u`). Then there are

- an `R`-algebra `C : Type u`, finitely presented over `R`;
- `R`-algebra maps `g : B → C` and `r : C → B` with `r ∘ g = id_B`,

such that for every `a ∈ B` with `Localization.Away a` smooth over `R`, some power
`(g a)^c` is strictly standard in `C` over `R` (`IsStrictlyStandard`).

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`):

- Lemma 3.1 (Tag 07CE, printed pp. 4-5): "Let R be a ring and let A be a finitely
  presented R-algebra. There exists finite type R-algebra map A → C which has a
  retraction with the following two properties (1) … (2) for each a ∈ A such that A_a
  is smooth over R the module Ω_{C_a/R} is free over C_a." The text before the lemma
  adds: "if R is Noetherian, then C is of finite presentation over R". In the proof,
  `C = Sym*_A(I/I²)` and `C_a` is smooth over `A_a` when `A_a` is smooth over `R`.
- Lemma 3.7 (Tag 07EZ, printed pp. 8-9), part (e): if `A_a` is smooth over `R` and
  `Ω_{A_a/R}` is stably free, then the elements `aᵉ`, `e ≥ e₀`, are strictly standard in
  `A` over `R`.

## Encoding

- The combination: for `a ∈ B` with `B_a` smooth, `C_a` (the localization at `g a`) is
  smooth over `R` with free `Ω_{C_a/R}` by Lemma 3.1, so Lemma 3.7(e) applied to `C`
  gives a strictly standard power of `g a`. The statement keeps only the existence of
  one such power.
- The retraction is an `R`-algebra map `r` with `r ∘ g = id`. Part (1) of Lemma 3.1
  (local complete intersections) is not used and is omitted.
- `R` is assumed Noetherian so that `C` is finitely presented, as in the source remark.
- "Strictly standard" is `IsStrictlyStandard` (Definition 2.3, Tag 07C7); see
  `Langlands/CommutativeAlgebra/Popescu/Basic.md`. All rings are in one universe `u`.
