# The local residue degree datum (M249.024)

Let `K` be a nonarchimedean local field (a field with `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances). The NYLL
abstract class-formation theory takes as input a *degree datum* on a
topological group `G`: a continuous homomorphism `G →ₜ* ZHatMul` to the
profinite integers, together with a proof that it is surjective. For local
class field theory the group is the absolute Galois group
`Gal(K^sep / K)`, and the degree is the local residue degree map
`localResidueDegree K` (M249.022): the residue action on the residue field
`Ω` of the chosen valuation ring of `K^sep`, followed by the
arithmetic-Frobenius degree of `Ω` over the finite base residue field `κ`.

This module defines
`Langlands.NYLL.LocalClassFieldTheory.localResidueDatum K` (source unit
M249.024), this degree datum. In Lean, with `variable (K : Type) [Field K]
[ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`:

```lean
/-- **Finite local reciprocity.**  The actual abstract class-formation datum
`d : G_K -> ZHat` furnished by the residue action of a local field. -/
noncomputable def Langlands.NYLL.LocalClassFieldTheory.localResidueDatum :
    DegreeData (Gal(SeparableClosure K / K)) where
  degree := localResidueDegree K
  degree_surjective := by
    ...  -- the proof described below
```

The docstring, the type and the field `degree` are the source text. The
field `degree_surjective` is a proposition, so its proof does not change the
datum: the data of `localResidueDatum K` is the map `localResidueDegree K`.

## The objects involved

Unless another namespace is given, `decompositionResidueField`,
`selectedResidueField`, `decompositionGroup`, `decompositionFixedMaximalIdeal`,
`decompositionGroupToMaximalIdealStabilizer` and
`decompositionGroupResidueAction` are in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
and the local reciprocity names are in `Langlands.NYLL.LocalClassFieldTheory`.

- `DegreeData G` (`Langlands.NYLL.ClassFormation.DegreeData`, module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`)
  is the structure with fields `degree : G →ₜ* ZHatMul` and
  `degree_surjective : Function.Surjective degree`, for a group `G` with a
  topology. `ZHatMul` (M010.001, same module) is `Multiplicative ZHat`.
- `Gal(SeparableClosure K / K)` is Mathlib's notation for
  `SeparableClosure K ≃ₐ[K] SeparableClosure K`, with Mathlib's group
  structure and Krull topology.
- `localResidueDegree K : Gal(SeparableClosure K / K) →ₜ* ZHatMul`
  (M249.022, module
  `...LocalReciprocity.LocalResidueDatum.U022.Definitions`) is the composite
  of the continuous residue action
  `localSeparableResidueAlgAction K : Gal(K^sep / K) →ₜ* (Ω ≃ₐ[κ] Ω)`
  (M249.020) and the Frobenius degree
  `residueAbsoluteDegreeIn κ Ω : (Ω ≃ₐ[κ] Ω) →ₜ* ZHatMul` (M236.017). Here
  `A = localSeparableValuationSubring K` (M249.006), `Ω = selectedResidueField A`
  (M243.004) and `κ = decompositionResidueField K A` (M243.003). Inside its
  body, M249.022 proves the two Prop-valued instance arguments
  `Algebra.IsAlgebraic κ Ω` (from normality, M243.030) and `IsAlgClosed Ω`
  (M249.016) of `residueAbsoluteDegreeIn` as local `haveI` facts. The third,
  `Fintype κ`, is the published instance `localDecompositionResidueFintype`
  (M249.015).

## The field `degree_surjective`

The source field is `localResidueDegree_surjective K`, the source theorem
M249.023. Its target is staged separately as
`localResidueDegree_surjectiveStatement`, but no proof of it is published.
Its source proof uses the M249.021 theorem
`localSeparableResidueAlgAction_surjective`, which uses the M244.004 theorem
`residueAlgActionOfEqTop_surjective`, which uses the M243.029 theorem
`decompositionGroupResidueAction_surjective`. The Library publishes the
targets of M249.021 and M244.004 (modules
`...LocalReciprocity.LocalResidueDatum.U021.Statements` and
`...LocalReciprocity.ResidueActionIndex.U004.Statements`), but none of these
proofs. M243.029 has no published target. However, every declaration their
source proofs use is published. So the field is proved in place by the
source proofs of the whole chain, in three steps, each a local `have`.

1. **`h029` (M243.029, inlined).** The residue action
   `decompositionGroupResidueAction K A` of the decomposition group on
   `Ω` over `κ` (M243.024, module
   `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueAction`)
   is surjective. This is the source proof of
   `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`,
   lines 356–392, for `L = SeparableClosure K` and `A`. It gives `A` the
   discrete topology, proves that the decomposition group is compact and
   acts continuously on `A`, and then applies Mathlib's
   `Ideal.Quotient.stabilizerHom_surjective_of_profinite`
   (`Mathlib.RingTheory.Invariant.Profinite`) with
   `G := decompositionGroup K A`, `P := decompositionFixedMaximalIdeal K A`
   and `Q := IsLocalRing.maximalIdeal A`. The source cites four private
   helpers. Their source proofs are inlined, exactly as in the M249.022 body
   (see its Markdown):
   - compactness, M243.010 (`decompositionGroup_compactSpace`, lines
     139–144), from the published theorem `decompositionGroup_isClosed`
     (module
     `Langlands.NYLL.ValuedFieldTheory.Ramification.ClosedSubgroups.DecompositionGroupIsClosedProof`);
   - continuity of the action, M243.009 (`decompositionGroup_continuousSMul`,
     lines 128–137), through local constancy of the orbit maps, M243.008
     (`decompositionGroup_action_locallyConstant`, lines 102–126);
   - the facts M243.011 and M243.012 (`decompositionFixedSubring_smulCommClass`
     and `decompositionFixedSubring_isInvariant`, lines 146–163) are found by
     instance search. They are Mathlib's `SMulCommClass` instance for
     `FixedPoints.subring` (`decompositionFixedSubring K A` abbreviates
     `FixedPoints.subring A (decompositionGroup K A)`) and the published
     instance `decompositionFixedSubring.instIsInvariant` (M243.014).

   The source then identifies the stabilizer element with the image of the
   decomposition-group element under
   `decompositionGroupToMaximalIdealStabilizer` (M243.023), by `Subtype.ext`
   and `rfl`, and concludes. These lines are the source text.
2. **`h021` (M244.004 and M249.021, inlined).** The residue action
   `localSeparableResidueAlgAction K` is surjective. The source proof of
   M249.021 (lines 393–398) applies M244.004 to `A` and
   `hA := localSeparableDecompositionGroup_eq_top K` (M249.010, published
   theorem, module `...LocalReciprocity.LocalResidueDatum.U010.Proofs`).
   Here `change` unfolds the goal to surjectivity of
   `residueAlgActionOfEqTop K A hA` (M244.003), which is the underlying
   monoid homomorphism of `localSeparableResidueAlgAction K`. Then the source
   proof of M244.004
   (`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`,
   lines 72–85) follows, with `h029` in place of the M243.029 theorem: lift
   `τ` to a decomposition-group element `σ`, note that
   `toDecompositionGroupOfEqTop K A hA σ = σ` (M244.001), and conclude by
   `simpa`.
3. **`h023` (M249.023, inlined).** This is the source proof of M249.023
   (lines 420–434), with `h021` in place of the M249.021 theorem. Given `z`,
   lift it along the surjective degree of the residue datum
   `residueDatumIn κ Ω` (M238.001, module
   `...LocalReciprocity.ResidueDatum.Initial.Definitions`) to `τ`, lift `τ`
   by `h021` to `σ`, and unfold the composite. The source proof finds the
   arguments `[Algebra.IsAlgebraic κ Ω]` and `[IsAlgClosed Ω]` of
   `residueDatumIn` and `residueAbsoluteDegreeIn` by instance search. Here
   they are not global instances. So `h023` states the conclusion for
   arbitrary proofs of these two propositions, which the proof introduces as
   anonymous local instances:

   ```lean
   have h023 : ∀ (_ : Algebra.IsAlgebraic κ Ω) (_ : IsAlgClosed Ω),
       Function.Surjective
         ((residueAbsoluteDegreeIn κ Ω).comp (localSeparableResidueAlgAction K))
   ```

   (with `κ` and `Ω` written out in Lean). The goal
   `Function.Surjective (localResidueDegree K)` is then closed by
   `exact h023 _ _`. Unification of the composite with `localResidueDegree K`
   fills the two holes with the proofs that the M249.022 body uses.

The type of the field is `Function.Surjective (localResidueDegree K)`. This
is the M249.023 proposition `localResidueDegree_surjectiveStatement` at `K`.
When a proof of M249.023 is published, it is equal to this field by proof
irrelevance, so the datum is the source datum.

## Binders and universes

The definition takes the explicit field `(K : Type)` and the instance binders
`[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]` of the source section variables (lines
45–46). `K` lives in `Type`, as in the source. The definition has no universe
parameters. The source local instances (lines 47–53) are not used.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`:

- file
  [`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean),
  SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`:
  namespace, opens and section variables at lines 31–46; M249.021 at lines
  393–398 (proof inlined); M249.023 at lines 417–434 (proof inlined);
  M249.024: docstring at lines 436–437, definition at lines 438–441;
- file
  [`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/ResidueActionIndex.lean),
  SHA-256 `985bdcfc1cc21860cc65bbb96dc92b1a0ec09dc05eadd6d4f46b4b0a551f4581`:
  M244.004 at lines 72–85 (proof inlined);
- file
  [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean),
  SHA-256 `cf543e2e441798c17d1b7b07167e0508d629b6ed143c66b624c04889f0b5927e`:
  section variables at lines 39–40; M243.008–M243.010 at lines 102–144
  (inlined); M243.011–M243.012 at lines 146–163 (supplied by instance
  search); M243.029 at lines 356–392 (proof inlined).

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.localResidueDatum` (M249.024) | `Langlands.NYLL.LocalClassFieldTheory.localResidueDatum` (this module) |
| `ClassFormation.DegreeData` (used) | `Langlands.NYLL.ClassFormation.DegreeData` (published) |
| `LocalClassFieldTheory.localResidueDegree` (M249.022, used) | the same name under `Langlands.NYLL.` (published) |
| `LocalClassFieldTheory.localResidueDegree_surjective` (M249.023, used) | local fact `h023` with the source proof; target `localResidueDegree_surjectiveStatement` staged separately |
| `LocalClassFieldTheory.localSeparableResidueAlgAction_surjective` (M249.021, used) | local fact `h021` with the source proof; target `localSeparableResidueAlgAction_surjectiveStatement` published |
| `LocalClassFieldTheory.residueAlgActionOfEqTop_surjective` (M244.004, used) | inlined in `h021` with the source proof; target `residueAlgActionOfEqTop_surjectiveStatement` published |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction_surjective` (M243.029, used) | local fact `h029` with the source proof |
| `...decompositionGroup_action_locallyConstant`, `...decompositionGroup_continuousSMul`, `...decompositionGroup_compactSpace` (M243.008–M243.010, private, used) | local facts in the `h029` proof, with their source proofs |
| `...decompositionFixedSubring_smulCommClass`, `...decompositionFixedSubring_isInvariant` (M243.011, M243.012, private, used) | found by instance search: Mathlib's `FixedPoints.subring` instance; published `decompositionFixedSubring.instIsInvariant` |
| `LocalClassFieldTheory.residueDatumIn` (M238.001, used) | the same name under `Langlands.NYLL.` (published) |
| `LocalClassFieldTheory.localSeparableResidueAlgAction` (M249.020), `residueAbsoluteDegreeIn` (M236.017), `localSeparableValuationSubring` (M249.006), `localSeparableDecompositionGroup_eq_top` (M249.010), `residueAlgActionOfEqTop` (M244.003), `toDecompositionGroupOfEqTop` (M244.001) (used) | the same names under `Langlands.NYLL.` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction`, `decompositionGroupToMaximalIdealStabilizer` (M243.024, M243.023), `decompositionGroup_isClosed`, `decompositionFixedMaximalIdeal`, `decompositionResidueField`, `selectedResidueField` (M243.003, M243.004) (used) | the same names under `Langlands.NYLL.` (published) |

## Relation to existing declarations

Row M249.024 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the adapted name and the module stem
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum`.

The whole Library at commit `210249ebac6bad5d2928923e3aaa6ea517d31490` and
the staging area were searched for `localResidueDatum`, for definitions whose
type is a `DegreeData` value, and for `localResidueDegree`. The name
`localResidueDatum` does not occur in the Library, in staging or in Mathlib.
The only Library definition with a `DegreeData` type is the M238.001
residue datum `residueDatumIn k Omega : DegreeData (Omega ≃ₐ[k] Omega)`. It is
a datum on the automorphism group of an algebraic closure of a finite field,
not on the absolute Galois group of a local field. This module uses it in
the proof of `degree_surjective`. The many other `DegreeData` occurrences
in the `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory` modules
take an arbitrary datum `D : DegreeData G` as a parameter.

The Library's local Weil construction has a related map,
`Langlands.Weil.Local.localResidueDegree F` with the theorem
`Langlands.Weil.Local.localResidueDegree_surjective` (module
`Langlands.Weil.Local.Assembly`). It is not a `DegreeData` value and not a
duplicate. It is defined for a `PadicField p` structure `F` on
`Field.absoluteGaloisGroup F.Carrier`, with values in
`Langlands.Weil.ProfiniteIntegers`, and it is normalized by geometric
Frobenius. The NYLL datum is defined for every nonarchimedean local field `K`
with the `ValuativeRel` and `IsNonarchimedeanLocalField` instances, on
`Gal(SeparableClosure K / K)`, with values in `ZHatMul`, and through the
arithmetic-Frobenius degree.

## Imports and modification record

The direct imports are:

- `...LocalReciprocity.LocalResidueDatum.U022.Definitions` (M249.022). Through
  its imports it brings M249.020, M249.015, M249.010, M249.006, M244.003,
  M244.001, M243.023–M243.024, M236.017, `decompositionGroup_isClosed`,
  `decompositionFixedSubring.instIsInvariant`, `DegreeData` and `ZHatMul`;
- `...LocalReciprocity.ResidueDatum.Initial.Definitions` (M238.001);
- `Mathlib.RingTheory.Invariant.Profinite`
  (`Ideal.Quotient.stabilizerHom_surjective_of_profinite`).

They replace the source's four imports (`ResidueActionIndex`,
`FiniteIntegralClosure`, `FiniteExtensionCorrespondence` and
`FiniteExtensionCompleteDVF`), which serve the other declarations of the
source file. Every transitive import lies in the approved Mathlib environment
or the published Library.

Worker 57 extracted this source definition on 15 November 2026. The Lean
header records the change. The changes are:

- the definition is in the namespace `Langlands.NYLL.LocalClassFieldTheory`.
  Its docstring, type and the field `degree` are the source text, and the
  structure is written with `where`, as in the source;
- the field `degree_surjective` is the tactic proof described above in place
  of the source term `localResidueDegree_surjective K`. Compared line by line
  with the inlined source proofs, the differences are: `L` and `A` are
  specialized to `SeparableClosure K` and `localSeparableValuationSubring K`,
  and `hA` to `localSeparableDecompositionGroup_eq_top K`; the private
  helpers M243.008–M243.010 are inlined at their use; the `let`s of
  M243.011–M243.012 are omitted because instance search finds the published
  instances; the cited theorems M243.029, M249.021 are replaced by the local
  facts `h029`, `h021`; the M249.021 proof becomes a `change` to the
  M244.004 goal followed by the M244.004 proof; the M249.023 proof is
  quantified over the two instance proofs and applied by `exact h023 _ _`;
  and fully qualified Library names replace the source names;
- the imports are replaced as described above;
- the source opens are replaced by `open Langlands.NYLL.ClassFormation`
  (for `DegreeData`, `ZHatMul`), the open of
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  and `open scoped Pointwise` (for the coset `σ • E.fixingSubgroup` in the
  M243.008 proof). The other source opens provide nothing this definition
  uses and are omitted.

Every other source declaration is omitted. In particular the theorem
M249.023 itself is not part of this module. No theorem, instance, notation or
alias is introduced: the inlined facts are local to the proof of the field.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), against Library commit
`210249ebac6bad5d2928923e3aaa6ea517d31490`, which contains the M249.022
module. Inspection reports `localResidueDatum` as a definition without level
parameters, depending only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. These development checks are not
independent acceptance.

## Use downstream

In the source, `localResidueDatum K` is the degree datum on which the finite
local reciprocity construction applies the abstract class-formation theory.
Many later source files use it, among them the files under
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldIntrinsicReciprocity/`
(for example `NormRestriction.lean`), the files under
`.../LocalReciprocity/Filtered/` and the files under
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/`.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. Worker 57 adapted this unit directly from the
pinned original; no other project worker supplied code.
