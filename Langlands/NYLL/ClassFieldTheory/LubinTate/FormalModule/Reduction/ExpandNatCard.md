# NYLL M349.001: proof of multivariable finite-field Frobenius expansion

This module proves the published proposition target
`Langlands.NYLL.LubinTate.SameUniformizer.mvPowerSeries_expand_natCardStatement`
(module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.ExpandNatCardStatement`).
The theorem is

```lean
theorem mvPowerSeries_expand_natCard
    {k : Type u} [Field k] [Finite k]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ k) :
    mvPowerSeries_expand_natCardStatement f
```

in namespace `Langlands.NYLL.LubinTate.SameUniformizer`, with universe
parameters `u w`. Its binders are the target's binders, in the same order and
with the same binder kinds. Its type is exactly the target applied to `f`. No
hypothesis is added.

## Statement proved

Let `k` be a finite field with `q = Nat.card k` elements, `σ` a finite type of
variables and `f ∈ k⟦X_i : i ∈ σ⟧`. Then

`MvPowerSeries.expand q (Nat.ne_of_gt Nat.card_pos) f = f ^ q`,

that is, substituting `X_i ↦ X_i ^ q` for every variable gives `f ^ q`. The
hypothesis `[Finite σ]` is part of the target, as in the source. The proof does
not use it.

## Implemented proof

The proof is the source proof (source lines 39–55) with one added first line,
`show _ = _`. The target is a reducible `abbrev`, and `show _ = _` unfolds it to
its equation so that the final `simpa` sees an equation goal. The remaining
steps are the source's, unchanged:

1. `let : Fintype k := Fintype.ofFinite k` chooses a `Fintype` instance, which
   the Mathlib finite-field lemmas need.
2. `CharP.exists k` gives a characteristic `p` with `CharP k p`.
   `FiniteField.card k p` then gives `n : ℕ+`, the primality of `p` and
   `Fintype.card k = p ^ (n : ℕ)`. A `Fact p.Prime` instance is introduced.
3. `hncard : Fintype.card k = p ^ n` is obtained from that equation by
   `simpa`, and `hn' : Nat.card k = p ^ n` follows from it by
   `Nat.card_eq_fintype_card`.
4. `hpow : MvPowerSeries.expand (p ^ n) _ f = f ^ (p ^ n)`. The proof rewrites
   `f ^ (p ^ n)` backwards with `MvPowerSeries.map_iterateFrobenius_expand`,
   which says that applying the `n`-fold Frobenius `iterateFrobenius k p n`
   coefficientwise to `expand (p ^ n) f` gives `f ^ p ^ n`. Then
   `iterateFrobenius_eq_pow` turns the `n`-fold Frobenius into
   `frobenius k p ^ n`, and `FiniteField.frobenius_pow hncard` shows that this
   is `1`, because every element of `k` satisfies `a ^ (p ^ n) = a`.
   `RingHom.one_def` and `MvPowerSeries.map_id` remove the identity coefficient
   map. The remaining goal closes by `rfl`. The side goal `p ≠ 0` required by
   `map_iterateFrobenius_expand` is `hpprime.ne_zero`.
5. `simpa only [hn'] using hpow` rewrites `Nat.card k` to `p ^ n` in the goal
   and closes it with `hpow`. The nonzero-exponent proof arguments of `expand`
   on the two sides agree by proof irrelevance.

The `lean_check` inspection of the declaration reports level parameters
`u, w`, no errors or warnings, and only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Dependencies

- The target module
  `Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.ExpandNatCardStatement`,
  which imports `Mathlib.SetTheory.Cardinal.Finite` and
  `Mathlib.RingTheory.MvPowerSeries.Expand`. It is imported unchanged.
- `Mathlib.FieldTheory.Finite.Basic`, imported explicitly as in the source, for
  `FiniteField.card` and `FiniteField.frobenius_pow`.
- Mathlib declarations used: `Fintype.ofFinite`, `CharP.exists`,
  `FiniteField.card`, `Nat.card_eq_fintype_card`,
  `MvPowerSeries.map_iterateFrobenius_expand`, `iterateFrobenius_eq_pow`,
  `FiniteField.frobenius_pow`, `RingHom.one_def`, `MvPowerSeries.map_id`.

No NYLL declaration other than the target statement is used. Mathlib's
`FiniteField.MvPowerSeries.expand_card` (stated with `Fintype.card`) is not
used; the source route is kept for source correspondence.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`, theorem
`LubinTate.SameUniformizer.mvPowerSeries_expand_natCard`, lines 32–55
(docstring 32–33, statement 34–38, proof 39–55). The source-file SHA-256 is
`b9a7d469a06616be19f5841ca96c26f22887650ccf4d83336a84ab89b2ccb2ad`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21` and
`nyll-classfieldtheory-fbd320cd-supplement`.

| Source unit | Original theorem and lines | Adapted theorem |
| --- | --- | --- |
| M349.001 | `LubinTate.SameUniformizer.mvPowerSeries_expand_natCard`, 32–55 | `Langlands.NYLL.LubinTate.SameUniformizer.mvPowerSeries_expand_natCard` |

## Modification record

The complete adaptations of the source theorem are:

1. the namespaces `LubinTate` and `SameUniformizer` are prefixed with
   `Langlands.NYLL`;
2. the theorem's type is written as the published target
   `mvPowerSeries_expand_natCardStatement f`, whose body is the source
   conclusion verbatim, instead of the source equation itself;
3. the proof gains a leading `show _ = _`; the rest of the source proof is
   unchanged;
4. only the universes `u w` used by the theorem are declared; the source's
   `universe u v w`, `open LocalFieldTheory.DiscreteValuationField`, the
   section variables, the later source declarations and the
   `noncomputable section` are omitted;
5. the imports are the target module and `Mathlib.FieldTheory.Finite.Basic`;
   the source imports of `Nyll.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation`
   and `.Intertwiner`, needed only by later source declarations, are omitted;
   the source's `Mathlib.SetTheory.Cardinal.Finite` and
   `Mathlib.RingTheory.MvPowerSeries.Expand` come through the target module;
6. the header has a modified-file notice, there is a new module docstring, and
   the declaration docstring names the source unit.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. The Library's `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

## Use

Because the target is a reducible `abbrev`, `rw [mvPowerSeries_expand_natCard]`
and `simp only [mvPowerSeries_expand_natCard]` rewrite the equation
`MvPowerSeries.expand (Nat.card k) (Nat.ne_of_gt Nat.card_pos) f = …` with this
theorem, as the source proof of M349.005 does. A private `lean_check` probe
confirmed both rewrites against this module.
