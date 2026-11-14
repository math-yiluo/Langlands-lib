# NYLL M349.001: multivariable finite-field Frobenius expansion target

This module states, as a Prop-valued target, exactly the first theorem of the
source module `Nyll.ClassFieldTheory.LubinTate.FormalModule.Reduction`. Over a
finite field `k` with `q = Nat.card k` elements, substituting `X_i ↦ X_i ^ q`
in a multivariable power series `f` gives the power series `f ^ q`. Nothing is
proved here. The target is to be proved later by a theorem of the same name
without the `Statement` suffix.

## Original source

Naganori Yamaguchi,
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean),
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`, lines 32–55
(docstring 32–33, statement 34–38, proof 39–55). The source-file SHA-256 is
`b9a7d469a06616be19f5841ca96c26f22887650ccf4d83336a84ab89b2ccb2ad`.
The readable original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/LubinTate/FormalModule/Reduction.lean`.
The registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and the
attribution supplement `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).
No applicable NYLL entry was found in `notes/errata/`.

The source theorem is

```lean
theorem mvPowerSeries_expand_natCard
    {k : Type u} [Field k] [Finite k]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ k) :
    MvPowerSeries.expand (Nat.card k) (Nat.ne_of_gt Nat.card_pos) f =
      f ^ Nat.card k
```

in namespace `LubinTate.SameUniformizer`, with `universe u v w` declared at
source line 25. It comes before the source's section variables (lines 57–59),
so none of those variables are in scope for it.

## Source correspondence

| Source unit | Original theorem and lines | Adapted target |
| --- | --- | --- |
| M349.001 | `LubinTate.SameUniformizer.mvPowerSeries_expand_natCard`, 34–38 | `Langlands.NYLL.LubinTate.SameUniformizer.mvPowerSeries_expand_natCardStatement` |

The target is an `abbrev` with the source theorem's binders, in source order
and with the same binder kinds, and with the source conclusion as its body:

```lean
abbrev mvPowerSeries_expand_natCardStatement
    {k : Type u} [Field k] [Finite k]
    {σ : Type w} [Finite σ] (f : MvPowerSeries σ k) : Prop :=
  MvPowerSeries.expand (Nat.card k) (Nat.ne_of_gt Nat.card_pos) f =
    f ^ Nat.card k
```

The `lean_check` inspection of the declaration reports level parameters
`u, w`, `statement_returns_prop: true` and only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`. A private `#check` gives the
telescope

`{k : Type u} → [Field k] → [Finite k] → {σ : Type w} → [Finite σ] → MvPowerSeries σ k → Prop`.

The universes of `k` and `σ` are independent, as in the source. The source
hypothesis `[Finite σ]` is kept even though the statement does not need it,
and no other hypothesis is added. In particular there is no `Fintype`,
characteristic or uniformizer hypothesis. The source docstring is kept and
the targeted source unit is named in it.

## Mathematical meaning

Let `k` be a finite field, `q = Nat.card k` its number of elements, `σ` a
finite type of variables and `f ∈ k⟦X_i : i ∈ σ⟧`.

- `Nat.card_pos : 0 < Nat.card k` holds because `k` is finite and nonempty, so
  `Nat.ne_of_gt Nat.card_pos : Nat.card k ≠ 0` is the nonzero-exponent proof
  that `MvPowerSeries.expand` requires. The statement depends on this proof
  argument only through its type, by proof irrelevance.
- Mathlib defines `MvPowerSeries.expand q hq` as the `k`-algebra map
  `substAlgHom (HasSubst.X_pow hq)`, which substitutes `X_i ↦ X_i ^ q` for
  every variable. It sends `∑ a_d X^d` to `∑ a_d X^(q • d)`.
- The target says `f(X_i ^ q) = f ^ q`. This is the multivariable Frobenius
  identity over a finite field: if `k` has characteristic `p` and
  `q = p ^ n`, the `p`-th power map is additive on `k⟦X⟧`, so raising to
  the power `q` raises each coefficient to the `q`th power and each monomial
  `X^d` to `X^(q • d)`, and `a ^ q = a` for every `a ∈ k`.

## Provability

The source proof (lines 39–55) reduces to Mathlib's
`MvPowerSeries.map_iterateFrobenius_expand` and `FiniteField.frobenius_pow`.
In a private probe, a theorem
`mvPowerSeries_expand_natCard … : mvPowerSeries_expand_natCardStatement f`
compiled with that proof unchanged after a leading `show _ = _`. Mathlib also
has `FiniteField.MvPowerSeries.expand_card` for `[Fintype K]` and
`Fintype.card`. It is a possible shortcut for the proof. It does not replace the
target, whose statement uses `Nat.card`, `[Finite k]` and the source
nonzero-exponent proof.

## Using the later proof

The target is an `abbrev`. The probe confirmed that a proof of it rewrites the
source equation with `rw [mvPowerSeries_expand_natCard]` and with
`simp only [mvPowerSeries_expand_natCard]`, as the source theorem does in the
source proof of M349.005. A proof that uses `simpa` or rewriting must first
expose the equation with `show _ = _` or `unfold`. That is the only change to
the source proof body.

## Dependencies and modification record

The imports are the two Mathlib modules that provide the statement's
constants: `Mathlib.SetTheory.Cardinal.Finite` (`Nat.card`, `Nat.card_pos`)
and `Mathlib.RingTheory.MvPowerSeries.Expand` (`MvPowerSeries.expand`). The
statement uses no NYLL declaration. The source also imports
`Mathlib.FieldTheory.Finite.Basic`, which only the source proof needs, and
`Nyll.ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation` and
`.Intertwiner`, which only the later source declarations need. These imports
are omitted here.

The complete adaptations are:

1. the source theorem is replaced by a Prop-valued `abbrev` named
   `mvPowerSeries_expand_natCardStatement`, whose binders are the source
   theorem's binders and whose body is the source theorem's conclusion
   verbatim; the source proof is omitted;
2. the namespaces `LubinTate` and `SameUniformizer` are prefixed with
   `Langlands.NYLL`;
3. only the universes `u w` used by the statement are declared; the source's
   `universe u v w`, `open LocalFieldTheory.DiscreteValuationField`, the
   section variables and the `noncomputable section` are omitted, since none
   of them is used by this statement;
4. the imports are reduced as described above;
5. the header has a modified-file notice, and there are a new module docstring
   and an extended declaration docstring naming the targeted source unit.

The remaining source units M349.002–M349.006 of the same source module are
not part of this module. They are submitted as a separate candidate, planned
as the sibling module
`Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.Reduction.Statements`.

The original 2026 copyright, Apache-2.0 release line and author header are
preserved. Existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are
unchanged, with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. The
NOTICE has no entry specific to this source file. The supplement's
`files/Nyll/ClassFieldTheory/ANTHROPIC_FLT_SOURCE.md` list of
Anthropic-derived files does not include it.
