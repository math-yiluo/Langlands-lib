# Proof of Stacks Lemmas 3.1 and 3.7(e): smooth elements become strictly standard

`strictlyStandardRetract : StrictlyStandardRetractStatement.{u}` is a complete proof of the
Library statement. It combines Stacks Project, *Smoothing ring maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 3.1 (tag 07CE, printed pp. 4-5) with
Lemma 3.7(e) (tag 07EZ, printed pp. 8-9), and takes no hypotheses.

Statement: let `R` be Noetherian and `B` a finitely presented `R`-algebra. Then there are a
finitely presented `R`-algebra `C` and `R`-algebra maps `g : B → C`, `r : C → B` with
`r ∘ g = id`, such that for every `a ∈ B` with `B_a` smooth over `R`, some power of `g a` is
strictly standard in `C` over `R`.

## The algebra `C` and the retraction

1. Choose a presentation `φ : R[x_1, …, x_n] → B` with kernel `I = (f_1, …, f_m)`.
2. Take `C = SymAlg I F = R[x, y]/J`, where `J = symIdeal I F` is the ideal of `Sym_B(I/I²)`
   (module `SymRetractAlgebra`). This is the algebra of Stacks Lemma 3.1. `C` is finitely
   presented because `R[x, y]` is Noetherian, so `J` is finitely generated.
3. `g : B → C` is induced by `x_i ↦ x_i`. It is well defined because `ιx(I) ⊆ J`.
4. `r : C → B` is induced by `x_i ↦ φ(x_i)` and `y_j ↦ 0`. This kills `ιx(I)` and every
   `Σ_j κ_j y_j`.
5. `r ∘ g = id` is checked on the generators `φ(x_i)` of `B`.

## Strictly standard powers

Let `a = φ(h)` with `B_a` smooth.

1. `exists_conormal_section` (module `ConormalSection`) gives `t` and `P` with
   `u f_k − Σ_l E_kl f_l ∈ I²`, where `u = h^t` and `E = D P`. Only formal smoothness of
   `B_a` is used here (the instance supplied by `Algebra.Smooth`).
2. Choose `Θ` with `E u − E² = Θ f`, using `Et_sq_sub` and the fact that the `f`'s generate
   `I`.
3. Choose generators `G_1, …, G_M` of `J`.
4. Apply `isStrictlyStandard_of_conormal` (module `StrictlyStandardCriterion`) to the quotient
   map `R[x, y] → C`, the generators `G`, and the relations `H_1, …, H_m` (module
   `SymRetractData`). These lie in `J` by `Hk_mem`. Its hypotheses hold with:
   - `s = u⁸`, since `u⁸ G_j ∈ (H) + J²` by `u8_mem` (module `SymRetractConormal`);
   - `Ψ = ΨC` and `t = u⁵`, since `Jac(H) · Ψ = u⁵ • 1` by `JC_mul_ΨC` (module
     `SymRetractJacobian`).
5. The conclusion is that `u⁸ · (u⁵)^m` is strictly standard. In `C`, `u = g(a)^t`, so this
   element is `g(a)^(8t + 5tm)`.

## Relation to the source

Stacks proves Lemma 3.7(e) through freeness of `(J/J²)_a` and an abstract left inverse of the
conormal map. Here both are replaced by explicit polynomial relations `H_k` and an explicit
right inverse `Ψ`. The minor condition comes from the Cauchy–Binet inclusion (module
`MaximalMinors`). Stacks Lemma 3.1 shows that `Ω_{C_a/R}` is free; the proof here does not
use Kähler differentials.

## Status

The proof modules import the Library modules `Basic` and `StrictlyStandardRetractStatement`,
together with Mathlib:

- `MaximalMinors`
- `StrictlyStandardCriterion`
- `ConormalSection`
- `SymRetractAlgebra`
- `SymRetractData`
- `SymRetractJacobian`
- `SymRetractConormal`

The theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
