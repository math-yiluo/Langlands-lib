# Normal closures of separable fraction-field extensions are Galois: statement target

`Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparableStatement`
concerns a finite, torsion-free extension of integral domains `R → S` whose
fraction-field extension `Frac S / Frac R` is separable. The proposition says
that the fraction field of Mathlib's ring-theoretic normal closure
`Ring.NormalClosure R S` is Galois over `Frac R`. In Lean:

```lean
attribute [local instance] FractionRing.liftAlgebra

def ringNormalClosure_isGalois_of_isSeparableStatement
    (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] : Prop :=
  IsGalois (FractionRing R)
    (FractionRing (Ring.NormalClosure R S))
```

This is the statement of source unit M162.011. Defining the proposition does not
prove it.

## Parameters and meaning

The declaration has universe parameters `u` and `v`, as in the source
(`R : Type u`, `S : Type v`). The parameters are:

| Binder | Kind | Meaning |
| --- | --- | --- |
| `R`, `S` | explicit, `Type u`, `Type v` | Base and extension rings |
| `[CommRing R]`, `[IsDomain R]`, `[CommRing S]`, `[IsDomain S]` | instance-implicit | Both rings are integral domains |
| `[Algebra R S]` | instance-implicit | The extension `R → S` |
| `[Module.Finite R S]` | instance-implicit | `S` is a finitely generated `R`-module |
| `[Module.IsTorsionFree R S]` | instance-implicit | `S` is torsion-free over `R`; in particular `R → S` is injective |
| `[Algebra.IsSeparable (FractionRing R) (FractionRing S)]` | instance-implicit | `Frac S / Frac R` is a separable algebraic extension |

`[Module.Finite R S]` does not occur in the conclusion. It is kept because it
belongs to the source section telescope and Lean includes every instance-implicit
section variable whose variables are included in a theorem, so the source theorem
takes it as a hypothesis.

The two algebra structures `Frac R → Frac S` and `Frac R → Frac T`, where
`T = Ring.NormalClosure R S`, are not hypotheses. They come from Mathlib's
`FractionRing.liftAlgebra` (`Mathlib/RingTheory/Localization/FractionRing.lean`,
line 769). Given a field `K` with `[Algebra R K]` and `[FaithfulSMul R K]`, it is
the algebra structure `Algebra (FractionRing R) K` whose map is the unique
extension of `algebraMap R K` to the fraction field. The statement registers it
as a local instance. It is then used with `K = FractionRing S` in the
separability hypothesis and with `K = FractionRing T` in the conclusion. In both
cases `R` acts faithfully: for `S` this follows from torsion-freeness, and for
`T` Mathlib supplies the needed instances in
`Mathlib/RingTheory/NormalClosure.lean`.

`Ring.NormalClosure R S` (`Mathlib/RingTheory/NormalClosure.lean`, line 63) is
the integral closure of `S` in the normal closure `E` of `Frac S / Frac R` inside
an algebraic closure of `Frac S`. Mathlib builds `E` with the same
`FractionRing.liftAlgebra` structure (line 45). Mathlib's own
`IsGalois (FractionRing R) (FractionRing T)` instance (line 119) assumes that
`FractionRing R` is a perfect field. This statement asks for the same conclusion
under the weaker hypothesis that `Frac S / Frac R` is separable.

So the proposition asserts: if `R → S` is a finite, torsion-free extension of
domains and `Frac S / Frac R` is separable, then
`Frac(Ring.NormalClosure R S) / Frac R` is a Galois extension. No Dedekind,
valuation, topology or local-field hypothesis is assumed.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
SHA-256 `b54bcd01a217ffc5fb905d410fe9ef64ebf87e5d7192509332cad827fc22c90e`.
The relevant lines are:

- `section SeparableIdealNormGalois` at line 240 and its `variable` telescope at
  lines 242–244;
- the anonymous local instance at lines 246–247 (inventory M162.010);
- the docstring at lines 249–252;
- the theorem's statement at lines 253–256 and its proof at lines 256–263.

The file opens `namespace LocalClassFieldTheory` (line 23) and
`noncomputable section` (line 29) and declares `universe u v w` (line 31). The
source lines that make up the statement are:

```lean
variable (R : Type u) (S : Type v)
  [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]

local instance : Algebra (FractionRing R) (FractionRing S) :=
  FractionRing.liftAlgebra R (FractionRing S)

theorem ringNormalClosure_isGalois_of_isSeparable
    [Algebra.IsSeparable (FractionRing R) (FractionRing S)] :
    IsGalois (FractionRing R)
      (FractionRing (Ring.NormalClosure R S)) := by
```

The retained original is in the project literature folder
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
It is registered as `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The attribution supplement is registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable` (M162.011) | `Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparableStatement` |
| anonymous local instance (M162.010) | replaced by `attribute [local instance] FractionRing.liftAlgebra` (see below) |

Row M162.011 of the published partition
[`notes/reuse/nyll-public-port/m145-m168.md`](../../../../../../../notes/reuse/nyll-public-port/m145-m168.md)
reserves `Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable`
for the later proof. Section 3 of
[`notes/reuse/nyll-public-port-plan.md`](../../../../../../../notes/reuse/nyll-public-port-plan.md)
gives the `Statement` suffix for the target. The partition's predecessors
M162.001–M162.010 are private lemmas and local instances used only by source
proofs. The only one the statement needs is the local instance M162.010, which
this target reproduces through `FractionRing.liftAlgebra`. No NYLL erratum for
this module was found in the current Library's `notes/`.

### The replaced local instance

Source unit M162.010 is a section-local definition. It takes the section
variables its body uses (`R`, `S`, their ring and domain structures,
`Algebra R S` and torsion-freeness), and its body is exactly
`FractionRing.liftAlgebra R (FractionRing S)`. In the source statement it
supplies both algebra structures. For the conclusion, Lean instantiates it with
`Ring.NormalClosure R S` in place of `S`. Each use therefore unfolds by
definition to `FractionRing.liftAlgebra R (FractionRing S)` or
`FractionRing.liftAlgebra R (FractionRing (Ring.NormalClosure R S))`. The
adaptation registers `FractionRing.liftAlgebra` itself as a local instance, and
instance synthesis produces these two terms directly. The adapted proposition is
the source proposition with the auxiliary local instance unfolded. The next
source section (line 274) uses the same attribute.

## Imports and modification record

The direct imports are the source's two Mathlib imports,
`Mathlib.FieldTheory.SeparableClosure` and `Mathlib.RingTheory.Ideal.Norm.RelNorm`.
Through them they supply `IsGalois`, `Algebra.IsSeparable`, `FractionRing`,
`FractionRing.liftAlgebra` and `Ring.NormalClosure`. Every transitive import lies
in the approved Mathlib environment. The source's four NYLL imports are not
needed by this statement and are dropped.

The adaptation makes these changes:

- it moves the section telescope and the theorem's binder and conclusion into
  the Prop-valued definition above. Binder order, binder kinds, binder names,
  universes and the conclusion are unchanged;
- it replaces the anonymous local instance M162.010 by the local instance
  attribute on `FractionRing.liftAlgebra`, as explained above;
- it omits the source proof and every other declaration of the module;
- it puts the definition in the namespace `Langlands.NYLL.LocalClassFieldTheory`
  and keeps the source's `noncomputable section`.

The source docstring is retained. The Lean header records these changes with
Worker 85's dated modification note.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports a definition
whose type ends in `Prop` (`statement_returns_prop: true`), with level
parameters `u`, `v` and only the standard axioms `propext`, `Classical.choice`
and `Quot.sound`. This development check is not independent acceptance.

## Boundary and license

This file defines the proposition only. The theorem
`Langlands.NYLL.LocalClassFieldTheory.ringNormalClosure_isGalois_of_isSeparable`
and its proof need a separate proof task once this target is in the Library.
The source proof (lines 256–263) transports Galoisness from the intermediate
normal closure of `Frac S / Frac R` in `AlgebraicClosure (FractionRing S)`. It
uses the private source lemmas M162.003 (that intermediate normal closure is
Galois when `Frac S / Frac R` is separable) and M162.006 (transport to
`FractionRing (Ring.NormalClosure R S)`). A proof may follow that route or
another.

The Lean file keeps the original copyright and author header unchanged:
Copyright (c) 2026 Naganori Yamaguchi; Authors: Naganori Yamaguchi (assisted
by OpenAI Codex). It remains under Apache-2.0. The already-published
[LICENSE](../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE) are reused unchanged and
included through `repository_paths`. Their SHA-256 hashes are
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`. Worker 85
adapted this unit directly from the pinned original; no other project worker
supplied code.
