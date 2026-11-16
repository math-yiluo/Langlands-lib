# Surjectivity of the local residue degree map: statement

This module defines one closed proposition in
`Langlands.NYLL.LocalClassFieldTheory`. It is the statement phase of source
row M249.023:

- `localResidueDegree_surjectiveStatement`, for the source theorem
  `localResidueDegree_surjective`.

It is a `def` returning `Prop` that packages the complete source theorem
signature. It has no proof here. A later proof will prove it under the name
`Langlands.NYLL.LocalClassFieldTheory.localResidueDegree_surjective`.

## The proposition

```lean
def localResidueDegree_surjectiveStatement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Function.Surjective (localResidueDegree K)
```

The definition has no universe parameters. As in the source, `K` is a field
in `Type` with Mathlib's `ValuativeRel` and `TopologicalSpace` structures,
and `IsNonarchimedeanLocalField K` says that `K` is a nonarchimedean local
field. These are the source section variables (lines 45–46). They become the
leading universal binders, in source order and with the source binder kinds.

`localResidueDegree K` is the definition published from source row M249.022
(module
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U022.Definitions`).
It is a continuous monoid homomorphism (Mathlib's `→ₜ*`)

```lean
Gal(SeparableClosure K / K) →ₜ* ZHatMul
```

Here:

- `Gal(SeparableClosure K / K)` is Mathlib's notation for the absolute
  Galois group `SeparableClosure K ≃ₐ[K] SeparableClosure K` of `K`, with
  the Krull topology;
- `ZHatMul` (`Langlands.NYLL.ClassFormation.ZHatMul`, M010.001, module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`)
  is `Multiplicative ZHat`, the profinite integers written multiplicatively.

The map `localResidueDegree K` is the composite of two continuous
homomorphisms. The first is the residue action
`localSeparableResidueAlgAction K : Gal(K^sep / K) →ₜ* (Ω ≃ₐ[κ] Ω)`
(M249.020). Here `Ω` is the residue field `selectedResidueField A` (M243.004)
of the valuation ring `A = localSeparableValuationSubring K` (M249.006) of
`SeparableClosure K` chosen by finite local reciprocity, and `κ` is the base
residue field `decompositionResidueField K A` (M243.003). The second is the
Frobenius degree `residueAbsoluteDegreeIn κ Ω : (Ω ≃ₐ[κ] Ω) →ₜ* ZHatMul`
(M236.017). It sends an automorphism to the unique profinite integer `z` such
that the automorphism is the `z`-th power of arithmetic Frobenius.

In the statement, `Function.Surjective (localResidueDegree K)` applies
`Function.Surjective` to the function underlying the continuous monoid
homomorphism, through Mathlib's coercion to functions. The proposition says
that every profinite integer is the residue degree of some element of the
absolute Galois group of `K`. This is the source docstring: the local
residue-degree map onto the profinite integers is surjective.

### Binders

The source theorem has no explicit binders and the source has no `omit`
line before it. Its signature mentions `K` and, through `localResidueDegree K`,
all four instance variables. So the source theorem takes exactly the section
variables of lines 45–46, and the proposition binds exactly these. A private
probe confirms it: a theorem with the source signature, declared under the
same section variables, has type
`∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K], ... → Function.Surjective ⇑(localResidueDegree K)`
by `#check`.

The source file also declares two local instances (lines 47–53), the algebra
`SeparableClosure K → AlgebraicClosure K` and a scalar tower. The statement
does not mention `AlgebraicClosure K`, so they are not used and are omitted.

## Expected proof

The source proof (lines 420–434) takes `z`, lifts it along the surjective
degree map of the residue datum
`residueDatumIn κ Ω` (M238.001, its field `degree_surjective`) to an
automorphism `τ` of `Ω` over `κ`, lifts `τ` along the residue action by the
M249.021 theorem `localSeparableResidueAlgAction_surjective` to some `σ`, and
concludes by unfolding the composite.

The source proof finds the instance arguments `[Algebra.IsAlgebraic κ Ω]`
and `[IsAlgClosed Ω]` of `residueDatumIn` and `residueAbsoluteDegreeIn` by
instance search. They are the source instances M243.030 and M249.016, which
are not global instances in the Library. The published M249.022 definition
proves them inside its own body (see its Markdown). So a proof here cannot
copy the source text verbatim: a private probe showed that the source's first
step then fails with "failed to synthesize `Algebra.IsAlgebraic κ Ω`".

A private probe replays the source proof in a form that works. Given the
published M249.021 target
`Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction_surjectiveStatement`
(module `...LocalReciprocity.LocalResidueDatum.U021.Statements`) as a
hypothesis `h021`, it first proves, for arbitrary proofs of
`Algebra.IsAlgebraic κ Ω` and `IsAlgClosed Ω`, that the composite
`(residueAbsoluteDegreeIn κ Ω).comp (localSeparableResidueAlgAction K)` is
surjective, by the source proof lines with `h021 K` in place of the M249.021
theorem. It then closes the goal by `exact h023 _ _`: unification picks the
two proofs that `localResidueDegree K` uses. This probe compiled with no
errors or warnings. It is development evidence only. The proof is a separate
unit and is not part of this module.

## Reused Library declarations

| Source unit and original declaration | Library declaration used |
| --- | --- |
| M249.022, `LocalClassFieldTheory.localResidueDegree` | `Langlands.NYLL.LocalClassFieldTheory.localResidueDegree` (module `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U022.Definitions`) |

The other declarations named above occur only through the type or the body
of `localResidueDegree`. They are imported through the M249.022 module:
`ZHatMul` (M010.001), `localSeparableResidueAlgAction` (M249.020, module
`...LocalReciprocity.LocalResidueDatum.U020.Definitions`),
`localSeparableValuationSubring` (M249.006), `residueAbsoluteDegreeIn`
(M236.017, module
`...LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions`), and
`selectedResidueField`, `decompositionResidueField` with their field and
algebra instances (M243.003, M243.004, M243.020, M243.021, namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`).
`SeparableClosure`, `AlgEquiv`, `ContinuousMonoidHom`, `ValuativeRel`,
`IsNonarchimedeanLocalField` and `Function.Surjective` are Mathlib
declarations.

## Relation to other Library and Mathlib declarations

Row M249.023 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the theorem name
`Langlands.NYLL.LocalClassFieldTheory.localResidueDegree_surjective` and the
module stem `...LocalReciprocity.LocalResidueDatum`.

The whole Library at commit `210249ebac6bad5d2928923e3aaa6ea517d31490` was
searched for `localResidueDegree` and for `DegreeData` values on a Galois
group, and the staging area for `localResidueDegree_surjectiveStatement`
and `localResidueDatum`. In the `Langlands.NYLL` port, at that commit,
`localResidueDegree` is the published M249.022 definition that this module
imports. No NYLL declaration states its surjectivity.

The Library has a theorem with the same short name,
`Langlands.Weil.Local.localResidueDegree_surjective` (module
`Langlands.Weil.Local.Assembly`). It is about a different map, so it is not
a duplicate. It states surjectivity of `Langlands.Weil.Local.localResidueDegree F`.
That map is defined for a `PadicField p` structure `F`. Its domain is
`Field.absoluteGaloisGroup F.Carrier` (built from `AlgebraicClosure`) and
its codomain is `Langlands.Weil.ProfiniteIntegers`. It is normalized by
geometric Frobenius and built from the Library's `absoluteResidueHom`. The
NYLL map is instead defined for every nonarchimedean local field `K` with the
`ValuativeRel` and `IsNonarchimedeanLocalField` instances, on
`Gal(SeparableClosure K / K)`, with values in `ZHatMul`, and through the
arithmetic-Frobenius degree on the residue field of the NYLL valuation ring.
Many other Library modules use the Weil map and its surjectivity. None of
them mentions the NYLL map.

The NYLL residue datum `residueDatumIn` (M238.001) has a surjectivity field
for `residueAbsoluteDegreeIn k Omega` alone, on `Omega ≃ₐ[k] Omega`. The
M249.021 target is surjectivity of the residue action. The present
proposition is about their composite, so neither of them states it.

## Original source

The original source is Naganori Yamaguchi (assisted by OpenAI Codex),
*ClassFieldTheory (NYLL)*, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean).
The complete file was read and its SHA-256 verified as
`be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`.
The M249.023 docstring is line 417 and the signature lines 418–419; the
proof is lines 420–434. The header occupies lines 1–5, the namespace line
31, the `open` lines 33, 35 and 41–43, the `noncomputable section` line 39,
the section variables lines 45–46, the local instances lines 47–53, and the
closing `end` lines 443–444.

| Source unit and original declaration | Adapted declaration and phase |
| --- | --- |
| M249.023, `LocalClassFieldTheory.localResidueDegree_surjective` | `Langlands.NYLL.LocalClassFieldTheory.localResidueDegree_surjectiveStatement`, closed Prop target |
| Same source theorem, later proof phase | `Langlands.NYLL.LocalClassFieldTheory.localResidueDegree_surjective`, reserved for the proof |

The readable original is in the registered source collection
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
under `n-yamaguchi-0729--ClassFieldTheory/source/`, with supplement
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

## Modifications and attribution

Worker 57 made these changes to the source theorem on 15 November 2026:

- The theorem becomes a Prop-valued definition with the `Statement`
  suffix. The section variable `K` and its four instance binders become the
  leading universal binders, in source order and with the source binder
  kinds. The conclusion is the source text. The proof is omitted for the
  separate proof phase.
- The namespace `LocalClassFieldTheory` is prefixed with `Langlands.NYLL`.
- The source imports are replaced by the Library module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.LocalResidueDatum.U022.Definitions`.
  Every transitive import lies in the approved Mathlib environment or the
  Library.
- The `noncomputable section`, all `open` lines (the statement names only
  declarations of its own namespace and Mathlib), the two local instances
  and all other declarations of the source file are omitted. The module
  docstring is a new short description of this unit. The declaration
  docstring is the source docstring.

The module compiled with zero errors and zero warnings in approved
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), against Library commit
`210249ebac6bad5d2928923e3aaa6ea517d31490`, which contains the M249.022
module. Inspection reports `localResidueDegree_surjectiveStatement` as a
definition returning `Prop`, without level parameters, depending only on
the standard axioms `propext`, `Classical.choice` and `Quot.sound`. These
development checks are not independent acceptance.

The Lean header keeps the original 2026 Naganori Yamaguchi copyright,
the authorship line including OpenAI Codex assistance, and the Apache-2.0
notice. It also records these modifications. The existing
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../licenses/NYLL/NOTICE) match the pinned
upstream files. Their SHA-256 hashes are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
Worker 57 adapted this unit directly from the pinned original; no other
project worker supplied code.

This unit contains only the M249.023 statement target. Its proof, the datum
`localResidueDatum` (M249.024) and the other rows of the source file are not
part of this unit.
