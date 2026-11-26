# The inductive assembly of the trace Paley–Wiener theorem

The module `Langlands.BaseChange.PaleyWienerAssembly` proves the linear
algebra of the induction over Levi subgroups in the proof of the trace
Paley–Wiener theorem. It contains no representation theory: every input of
that proof enters as a hypothesis on abstract linear data.

## Origin

Bernstein, Deligne and Kazhdan prove their trace Paley–Wiener theorem in
§4.3 of *Trace Paley–Wiener theorem for reductive p-adic groups* (J. Analyse
Math. 47 (1986), printed p. 185) from three results of §3 and from
Proposition 4.2. After localizing a good form `f` at one connected component
of the Bernstein variety, they subtract a trace form that agrees with `f` on
the span `R_disc` of the irreducible representations with a discrete
infinitesimal character (Propositions 3.1 and 4.2), and show that what is
left is a sum of Jacquet lifts of trace forms on proper Levi subgroups, using
the induction hypothesis on those Levi subgroups. `exists_eq_eval_of_good`
states and proves this step for abstract data; its hypotheses are modeled on
the results quoted in §4.3.

Rogawski's twisted version, Proposition 11.2 of *Trace Paley–Wiener theorem
in the twisted case* (Trans. Amer. Math. Soc. 309 (1988), printed
pp. 228–229), uses Proposition 7.1 (Jacquet lifts of trace forms),
Proposition 9.1 (the discrete projection) and Proposition 10.1 (finiteness of
discrete supports up to unramified twist), after localizing at one stable
component. Its interpolation on `R(Θ_disc)` (printed p. 229, first
paragraph) is stated only for the discrete good forms `F ∈ F_disc(G)`, the
good forms that vanish on the properly induced part. The two other theorems
of this module follow that organization: `exists_eq_eval_of_discrete` treats
discrete good forms at one index and uses interpolation only for the good
forms it is applied to, and `exists_eq_eval_of_good_of_discrete` runs the
induction with the discrete case as a hypothesis.

## Data

- An index type `ι` with a well-founded relation `r`; in the application
  `i : ι` runs over a group and its standard Levi subgroups, and `r j i`
  means that `j` is a proper Levi subgroup of `i`.
- For each `i`, a type `Lev i` of Levi subgroups with indices `tgt i l`
  satisfying `r (tgt i l) i`.
- For each `i`, a complex vector space `S i` (test functions); distributions
  are its algebraic dual `Module.Dual ℂ (S i)`.
- `Irr i`, a set of distributions (the twisted characters of the irreducible
  representations), and `Good i`, a set of linear functionals on
  distributions (the good forms).
- Linear maps `CT i l : S i → S (tgt i l)` and `L i l : S (tgt i l) → S i`.
  In the application the transpose of `CT` sends the character of a
  representation of the Levi subgroup to the character of its parabolic
  induction, and the transpose of `L` sends the character of a
  representation to the character of its Jacquet module (Rogawski,
  Proposition 7.1).
- Finitely supported coefficients `c i : Lev i →₀ ℂ` and a subspace `Disc i`
  of distributions (the span of the characters with discrete infinitesimal
  character).

`inducedSpan tgt Irr CT i` is the span of the distributions `θ' ∘ CT i l`
for `θ' ∈ Irr (tgt i l)`, the characters of the properly induced
representations. `descent tgt CT L i l` is the operator
`x ↦ x ∘ L i l ∘ CT i l` on distributions, the operator `i_M ∘ r_M` of
the papers.

## Statement

`exists_eq_eval_of_good` assumes:

1. `hA1`: every element of `Irr i` lies in `Disc i ⊔ inducedSpan i`. In the
   papers, `R(G) = R_disc + R^1`.
2. `hA2`: every `descent l` maps `Disc i` into itself. In the papers the
   operators `i_M ∘ r_M` preserve infinitesimal characters.
3. `hA3`: for `x ∈ inducedSpan i`, `x = ∑ₗ c l • descent l x`. This is the
   combinatorial lemma of Bernstein–Deligne–Kazhdan §3.3 and Rogawski,
   Lemma 8.2 and Proposition 9.1, applied to properly induced elements.
4. `hA4`: every good form agrees on `Disc i` with evaluation at a test
   function. This is the interpolation step of Bernstein–Deligne–Kazhdan §4.3,
   from Propositions 3.1 and 4.2, applied to each of the finitely many
   components that a good form meets. Rogawski's twisted interpolation (proof
   of Proposition 11.2, printed p. 229, with Proposition 10.1) is stated only
   for discrete good forms; the section on the discrete case below explains
   how that narrower input is used.
5. `hA5`: composing a good form with `Module.Dual.transpose (CT i l)`
   gives a good form on `tgt i l` (Bernstein–Deligne–Kazhdan Proposition
   3.2(i); Rogawski, Lemma 11.1(b)).
6. `hA6`: for `θ ∈ Irr i`, `θ ∘ L i l` lies in the span of `Irr (tgt i l)`.
   In the application, the Jacquet module of an irreducible representation
   has finite length.

The conclusion is that every `Φ ∈ Good i` is a trace form on `Irr i`: there
is `s : S i` with `Φ θ = θ s` for every `θ ∈ Irr i`.

`PaleyWienerAssemblyStatement.{u₁, u₂, u₃}` is the same assertion as a
proposition, quantified over the index type in `Type u₁`, the Levi types in
`Type u₂` and the test spaces in `Type u₃`, with the hypotheses in the order
`hA1`–`hA6`. The theorem `paleyWienerAssembly` proves it from
`exists_eq_eval_of_good`.

## Proof

Well-founded induction on `i`. Fix `Φ ∈ Good i`. By `hA4` choose `s₁` with
`Φ = eval s₁` on `Disc i`, and put `Φ' = Φ - eval s₁`, which vanishes on
`Disc i`. For each Levi `l`, `hA5` and the induction hypothesis give `s_l`
with `Φ (θ' ∘ CT i l) = θ' (s_l)` for `θ' ∈ Irr (tgt i l)`. Two linear
functionals that agree on a set agree on its span
(`LinearMap.eqOn_span`), so
`Φ' (y ∘ CT i l) = y (s_l - CT i l s₁)` for every `y` in the span of
`Irr (tgt i l)`.

Let `θ ∈ Irr i` and write `θ = d + x` with `d ∈ Disc i` and
`x ∈ inducedSpan i` (`hA1`). Then `Φ' θ = Φ' x`, and by `hA3`,
`Φ' x = ∑ₗ c l * Φ' (descent l x)`. Since `descent l d ∈ Disc i` (`hA2`),
`Φ' (descent l x) = Φ' (descent l θ)`. Finally `descent l θ` is
`(θ ∘ L i l) ∘ CT i l`, and `θ ∘ L i l` lies in the span of
`Irr (tgt i l)` (`hA6`), so
`Φ' (descent l θ) = θ (L i l (s_l - CT i l s₁))`. Hence `Φ θ = θ s` for

```text
s = s₁ + ∑ₗ c l • L i l (s_l - CT i l s₁).
```

Compared with the papers, the Lean proof does not subtract a trace form from
the restricted forms on the Levi subgroups. It applies the induction
hypothesis to `Φ ∘ CT^t` itself and corrects by `CT i l s₁`, so it needs no
closure property of the good forms.

## Two auxiliary lemmas

`comp_mem_span_of_mem_span` says that if `θ ↦ θ ∘ L` sends a set `Irr i` into
the span of `Irr j`, it sends the span of `Irr i` into the span of `Irr j`.
`transpose_mem_inducedSpan` says that `y ∘ CT i l` lies in `inducedSpan i`
for `y` in the span of `Irr (tgt i l)`. Both are `Submodule.span_le` applied
to a preimage submodule.

## The discrete case without induction

`exists_eq_eval_of_discrete` treats a good form `Φ` that vanishes on
`inducedSpan i`, at a single index `i`. It assumes `hA1`, `hA2`, `hA3`,
`hA4`, `hA6` at `i` and `hA9 : Disc i ≤ span (Irr i)`. It requires no
Paley–Wiener realization on the Levi subgroups of `i`, but it still assumes
the Levi span condition `hA6` and uses the test-function maps `CT i l` and
`L i l`. If `h` interpolates `Φ` on `Disc i` (`hA4`), then `Φ` agrees on
`Irr i` with evaluation at

```text
h - ∑ₗ c l • L i l (CT i l h),
```

the test-function form of the discrete projection of Bernstein–Deligne–Kazhdan
§3.3 and Rogawski Proposition 9.1. Proof: write `θ = d + x` as in `hA1`.
Then `Φ θ = d h`. For each `l`, `descent l d` lies in `Disc i` (`hA2`) and,
by `hA9`, `hA6` and `transpose_mem_inducedSpan`, in `inducedSpan i`; hence
`(descent l d) h = Φ (descent l d) = 0`. Evaluating `hA3` at `h` gives
`x h = ∑ₗ c l * (descent l x) h`. Since `(d + x) (L i l (CT i l h))` is
`(descent l d) h + (descent l x) h`, the value of `d + x` at the displayed
test is `d h`.

The parameter `Good` of `exists_eq_eval_of_discrete` is arbitrary, and `hA4`
is only used for the form `Φ` itself. To use Rogawski's narrower
interpolation input, take for `Good` the set of good forms that vanish on
`inducedSpan i`: then `hA4` asks for interpolation on `Disc i` only for these
discrete good forms, as on printed p. 229, and the conclusion is the
hypothesis `hD` of `exists_eq_eval_of_good_of_discrete` for the original good
forms.

## Induction from the discrete case

`exists_eq_eval_of_good_of_discrete` derives the conclusion of
`exists_eq_eval_of_good` from the discrete case taken as a hypothesis:

- `hD`: at every index, a good form vanishing on `inducedSpan i` agrees with
  an evaluation on `Irr i`;
- `hA3`, `hA5` and `hA6` as above;
- `hA7`: `inducedSpan i ≤ span (Irr i)` (induced representations have finite
  length);
- `hA8`: `Φ - eval s` is good whenever `Φ` is good (trace forms are good,
  Bernstein–Deligne–Kazhdan §1.2 and Rogawski Lemma 11.1(a), and good forms
  form a subspace).

The proof is a well-founded induction on `i`. The induction hypothesis
applied to `Φ ∘ CT^t` (good by `hA5`) gives `s_l` with
`Φ (y ∘ CT i l) = y (s_l)` for `y` in the span of `Irr (tgt i l)`. For
`x ∈ inducedSpan i`, `hA7` and `hA6` put `x ∘ L i l` in that span, so
`Φ (descent l x) = x (L i l s_l)`, and `hA3` gives
`Φ x = x s'` with `s' = ∑ₗ c l • L i l s_l`. Thus `Φ - eval s'`, good by `hA8`,
vanishes on `inducedSpan i`, and `hD` gives `s_d` with `Φ θ = θ (s_d + s')`
on `Irr i`. In Rogawski's notation, `Φ - eval s'` is the form
`F_d = F - ∑ c_M r*_{MG} i*_{GM}(F)` of Proposition 9.1 once each
`i*_{GM}(F)` is realized by the induction hypothesis: it is good and
discrete, and the discrete case realizes it.
