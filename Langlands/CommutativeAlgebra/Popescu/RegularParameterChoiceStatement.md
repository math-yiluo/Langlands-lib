# Choosing regular parameters with annihilator conditions

`Langlands.CommutativeAlgebra.Popescu.RegularParameterChoiceStatement` (universe `u`).

**Hypotheses.**
- `Λ : Type u` is a Noetherian commutative ring.
- `I` is an ideal and `q` a prime ideal of `Λ` with `I ≤ q`.
- `n : ℕ` satisfies `qⁿΛ_q ⊆ IΛ_q`. In Lean this is
  `(q ^ n).map (algebraMap Λ Λ_q) ≤ I.map (algebraMap Λ Λ_q)`, where
  `Λ_q = Localization.AtPrime q`.
- `Λ_q` is a regular local ring.

**Conclusion.** Write `d = (maximalIdeal Λ_q).spanFinrank`. For every `e > 0` there is
`π : Fin d → Λ` such that:

1. the images of `π₁, …, π_d` in `Λ_q` generate its maximal ideal;
2. these images form a weakly regular sequence on `Λ_q`;
3. `πᵢⁿ ∈ I` for all `i`;
4. for all `i` and `x ∈ Λ`, if `πᵢ² x ∈ (π_j^e : j < i)` then `πᵢ x ∈ (π_j^e : j < i)`.

## Source

Stacks Project, *Smoothing Ring Maps* (`smoothing.pdf` in
`stacks-artin-axioms-approximation-2026-11-06`), Lemma 10.2 (Tag 07FD, printed p. 24):

> Let Λ be a Noetherian ring. Let I ⊂ Λ be an ideal. Let I ⊂ q be a prime. Let n, e be
> positive integers. Assume that qⁿΛ_q ⊂ IΛ_q and that Λ_q is a regular local ring of
> dimension d. Then there exists an n > 0 and π₁, …, π_d ∈ Λ such that
> (1) (π₁, …, π_d)Λ_q = qΛ_q, (2) π₁ⁿ, …, π_dⁿ ∈ I, and (3) for i = 1, …, d we have
> Ann_{Λ/(π₁ᵉ, …, πᵢ₋₁ᵉ)Λ}(πᵢ) = Ann_{Λ/(π₁ᵉ, …, πᵢ₋₁ᵉ)Λ}(πᵢ²).

## Encoding and scope

- **The exponent `n`.** The source statement says "there exists an n > 0", but the `n`
  in (2) is the given `n` with `qⁿΛ_q ⊂ IΛ_q`. The proof keeps it: "By assumption
  πᵢⁿ ∈ IΛ_q. Thus we can find s₁, …, s_d ∈ S such that sᵢπᵢⁿ ∈ I. Replacing πᵢ by sᵢπᵢ we
  get (2)." Lemma 10.3 (Tag 07FE) also applies the lemma "where n = n, e = 8c" with the
  `n` it has already fixed. So the statement takes `n` as given and uses it in condition
  3. The requirement `n > 0` is dropped: it follows from `I ≤ q`, since `q⁰Λ_q = Λ_q`
  is not contained in `IΛ_q ⊆ qΛ_q`.
- **The dimension `d`.** `d` is the minimal number of generators of the maximal ideal of
  `Λ_q`. For a regular local ring this equals `dim Λ_q`.
- **Conditions 1 and 4.** (1) is condition 1, since `qΛ_q` is the maximal ideal of
  `Λ_q`. (3) is condition 4. The inclusion `Ann(πᵢ) ⊆ Ann(πᵢ²)` always holds, so the
  equality amounts to the implication `πᵢ² x ∈ J → πᵢ x ∈ J`, where
  `J = (π_j^e : j < i)`. Indices are zero-based.
- **Condition 2.** Condition 2 is not part of the source statement, but the source proof
  establishes it: "Note that π₁, …, π_d is a regular sequence in S⁻¹Λ, see Algebra,
  Lemma 106.3". The proof of Lemma 10.3 uses it: "since x₁, …, x_d map to a regular
  sequence in Λ_q".
- **Universe.** All rings are in one universe `u`.
