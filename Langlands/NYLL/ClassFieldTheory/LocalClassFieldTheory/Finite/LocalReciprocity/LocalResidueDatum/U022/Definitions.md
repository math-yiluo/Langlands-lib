# The local residue degree map (M249.022)

Let `K` be a nonarchimedean local field (a field with `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances). Finite local
reciprocity fixes a valuation ring `A = localSeparableValuationSubring K` of
the separable closure `K^sep = SeparableClosure K`. Let `Ω` be the residue
field of `A` and `κ` the base residue field of the residue-action exact
sequence. Every `K`-automorphism of `K^sep` acts on `Ω` over `κ`
(M249.020). The field `κ` is finite and `Ω` is an algebraic closure of `κ`.
So every automorphism of `Ω` over `κ` has a well-defined degree in the
profinite integers: the unique `z` such that the automorphism is the `z`-th
power of arithmetic Frobenius (M236.017).

This module defines
`Langlands.NYLL.LocalClassFieldTheory.localResidueDegree K` (source unit
M249.022). It is the composite of these two continuous homomorphisms:

```
Gal(K^sep / K) --(residue action)--> Aut_κ(Ω) --(Frobenius degree)--> ZHatMul
```

In Lean, with `variable (K : Type) [Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`:

```lean
noncomputable def Langlands.NYLL.LocalClassFieldTheory.localResidueDegree :
    Gal(SeparableClosure K / K) →ₜ* ZHatMul :=
  haveI hNormal : Normal
      (decompositionResidueField K (localSeparableValuationSubring K))
      (selectedResidueField (localSeparableValuationSubring K)) := by
    ...  -- the source proof of M243.030, described below
  haveI : IsAlgClosed (selectedResidueField
      (localSeparableValuationSubring K)) := by
    ...  -- the source proof of M249.016, described below
  { toMonoidHom :=
      (residueAbsoluteDegreeIn
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField (localSeparableValuationSubring K))).toMonoidHom.comp
          (localSeparableResidueAlgAction K).toMonoidHom
    continuous_toFun :=
      (residueAbsoluteDegreeIn
        (decompositionResidueField K (localSeparableValuationSubring K))
        (selectedResidueField
          (localSeparableValuationSubring K))).continuous_toFun.comp
        (localSeparableResidueAlgAction K).continuous_toFun }
```

The two fields are the source text. The two `haveI` facts are propositions,
so their proofs do not change the map: `toMonoidHom` is the composite of the
two monoid homomorphisms, and `continuous_toFun` is the composite of their
continuity proofs.

## The objects involved

Unless another namespace is given, `decompositionResidueField`,
`selectedResidueField`, `decompositionGroup`, `decompositionFixedSubring`
and `decompositionFixedMaximalIdeal` are in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
and the local reciprocity names are in
`Langlands.NYLL.LocalClassFieldTheory`.

- `Gal(SeparableClosure K / K)` is Mathlib's notation for
  `SeparableClosure K ≃ₐ[K] SeparableClosure K`, with Mathlib's Krull
  topology.
- `ZHatMul` (`Langlands.NYLL.ClassFormation.ZHatMul`, M010.001, module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`)
  is `Multiplicative ZHat`, the profinite integers written multiplicatively.
- `localSeparableValuationSubring K` is the chosen valuation ring `A`
  (M249.006, module `...LocalReciprocity.LocalResidueDatum.U006.Definitions`).
- `selectedResidueField A` is the residue field `Ω` of `A` (M243.004).
  `decompositionResidueField K A` is the base residue field `κ` (M243.003). It
  is the quotient of the subring `decompositionFixedSubring K A` of `A` fixed
  by the decomposition group by `decompositionFixedMaximalIdeal K A`, the
  contraction of the maximal ideal of `A`. Its `Field` instance (M243.020) and
  the `κ`-algebra structure on `Ω` (M243.021) are published in
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`.
- `localSeparableResidueAlgAction K : Gal(K^sep / K) →ₜ* (Ω ≃ₐ[κ] Ω)` is the
  continuous residue action (M249.020, module
  `...LocalReciprocity.LocalResidueDatum.U020.Definitions`).
- `residueAbsoluteDegreeIn k Omega : (Omega ≃ₐ[k] Omega) →ₜ* ZHatMul`
  (M236.017, module
  `...LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions`) is
  the inverse of the arithmetic-Frobenius isomorphism
  `ZHatMul ≃ₜ* (Omega ≃ₐ[k] Omega)`, viewed as a continuous homomorphism. It
  takes the instance arguments `[Fintype k]`, `[Algebra.IsAlgebraic k Omega]`
  and `[IsAlgClosed Omega]`.
- `→ₜ*` is Mathlib's `ContinuousMonoidHom`. `ContinuousMonoidHom` has fields
  `toMonoidHom` and `continuous_toFun`.

## The three instance arguments

For `k = κ` and `Omega = Ω`, the source finds the three instance arguments of
`residueAbsoluteDegreeIn` by instance search:

- `Fintype κ` is the source instance `localDecompositionResidueFintype`
  (M249.015). It is published under the same name (module
  `...LocalReciprocity.LocalResidueDatum.U015.Definitions`), and instance
  search finds it here too.
- `Algebra.IsAlgebraic κ Ω` comes from the source instance
  `decompositionResidueExtension_normal` (M243.030): `Normal κ Ω`, through
  Mathlib's `Normal.toIsAlgebraic`.
- `IsAlgClosed Ω` is the source instance `localSelectedResidueIsAlgClosed`
  (M249.016).

M243.030 and M249.016 are propositions whose proofs are not in the Library.
The target of M249.016 is published as
`localSelectedResidueIsAlgClosedStatement` (module
`...LocalReciprocity.LocalResidueDatum.U014.Statements`), but not its proof.
M243.030 has no published target. However, every declaration their source
proofs use is published. The body therefore proves both facts in place with
their source proofs, as the two `haveI` facts. After that, instance search
finds all three arguments. When proofs of M243.030 and M249.016 are
published, they are equal to these local proofs by proof irrelevance, so the
definition is the source definition.

### Normality of `Ω / κ` (M243.030, inlined)

The source instance has the proof of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`,
lines 394–413, for a Galois extension `L / K` and a valuation ring `A` of
`L`. Here `L = SeparableClosure K` and `A = localSeparableValuationSubring K`.
The proof is:

1. Give `A` the discrete topology (`⊥`, with `DiscreteTopology A`).
2. **Compactness (M243.010, inlined).** The private source theorem
   `decompositionGroup_compactSpace` (lines 139–144) is proved here by its
   source proof. The published theorem `decompositionGroup_isClosed`
   (M241.002, module
   `Langlands.NYLL.ValuedFieldTheory.Ramification.ClosedSubgroups.DecompositionGroupIsClosedProof`)
   says the decomposition group is closed in the Galois group. The Krull
   topology is compact, so the group is compact (`IsClosed.isCompact`,
   `isCompact_iff_compactSpace`).
3. **Continuity of the action (M243.009 and M243.008, inlined).** The private
   source theorem `decompositionGroup_continuousSMul` (lines 128–137) is
   proved here by its source proof. By Mathlib's
   `continuous_prod_of_discrete_right`, it suffices that each orbit map
   `g ↦ g • a` is continuous. This holds because the map is locally constant.
   That is the private source theorem
   `decompositionGroup_action_locallyConstant` (lines 102–126), also proved
   here by its source proof. Given `σ`, let `E = K(a)`, finite dimensional
   over `K` (`IntermediateField.adjoin.finiteDimensional`). The coset of the
   open fixing subgroup of `E` through `σ` (`fixingSubgroup_isOpen`) is an
   open neighbourhood of `σ`. Every `τ = σ g` in it, with `g` fixing `a`,
   satisfies `τ • a = σ • a`.
4. **Invariants.** The source introduces the private facts
   `decompositionFixedSubring_smulCommClass` and
   `decompositionFixedSubring_isInvariant` (M243.011, M243.012, lines
   146–163). Here instance search finds them. The first is Mathlib's instance
   `SMulCommClass G (FixedPoints.subring B G) B`
   (`Mathlib.Algebra.Algebra.Subalgebra.Operations`), since
   `decompositionFixedSubring K A` is the abbreviation
   `FixedPoints.subring A (decompositionGroup K A)`. The second is the
   published instance `decompositionFixedSubring.instIsInvariant` (M243.014,
   module `...HilbertRamification.ResidueExactSequence.IsInvariantProof`).
5. **Conclusion.** Apply the published theorem
   `Langlands.NYLL.RamificationTheory.Ideal.Quotient.normal_of_profinite`
   (M242.001, module
   `Langlands.NYLL.ValuedFieldTheory.Ramification.ProfiniteInvariant.NormalProof`)
   with `G := decompositionGroup K A`, `P := decompositionFixedMaximalIdeal K A`
   and `Q := IsLocalRing.maximalIdeal A`. It says: if a compact totally
   disconnected group acts continuously on a discrete ring with invariant
   ring `R`, then the residue field extensions at maximal ideals `Q` over `P`
   are normal. Its remaining instance arguments are found by instance search,
   as in the source. Among them are the published instances
   `decompositionFixedMaximalIdeal.instIsMaximal` (M243.016) and
   `selectedMaximalIdeal.instLiesOver` (M243.019), which the
   `ResidueFields` module imports. The quotients are `κ` and `Ω` by
   definition.

### Algebraic closedness of `Ω` (M249.016, inlined)

The source proof is at lines 268–303 of `LocalResidueDatum.lean`. Let `A'` be
the valuation ring of the algebraic closure `AlgebraicClosure K` chosen in
the construction. It is the private source definition
`localAbsoluteValuationSubring` (M249.003), published as
`Langlands.NYLL.PortInternal.M249.d003 K` (module
`...LocalResidueDatum.U006.Definitions`). By definition, `A` is the pullback
of `A'` along the inclusion `K^sep → AlgebraicClosure K`. That inclusion is
the source local instance `localSeparableClosureAlgebra` (M249.001), the
published `Langlands.NYLL.PortInternal.M249.d001`. This module activates it
locally with `attribute [local instance]`, as the published M249.006 module
does. The proof:

1. Let `barI : Ω → Ω'` be the residue map of the pullback, where `Ω'` is the
   residue field of `A'` (`valuationSubringComapResidueMap`, M237.004, module
   `...LocalReciprocity.ResidueAlgebraicallyClosed.U004.Definitions`). It
   makes `Ω'` an `Ω`-algebra.
2. `AlgebraicClosure K` is purely inseparable over `K^sep` (Mathlib's
   `separableClosure.isPurelyInseparable`). By the published theorem
   `valuationSubring_comap_residueField_isPurelyInseparable` (M237.006,
   module `...ResidueAlgebraicallyClosed.U006.Proofs`), `Ω'` is purely
   inseparable over `Ω`.
3. `κ` is finite, hence perfect (Mathlib's `PerfectField.ofFinite`, found by
   instance search). `Ω` is algebraic over `κ` because it is normal
   (`hNormal.toIsAlgebraic`; in the source,
   `(decompositionResidueExtension_normal B).toIsAlgebraic`). So `Ω` is perfect
   (`Algebra.IsAlgebraic.perfectField`), and `Ω'` is separable over `Ω`
   (instance search).
4. An extension that is both purely inseparable and separable is trivial, so
   `barI` is surjective (`IsPurelyInseparable.surjective_algebraMap_of_isSeparable`).
   It is injective, as a ring homomorphism of fields. So it is a ring
   isomorphism `e : Ω ≃+* Ω'` (`RingEquiv.ofBijective`).
5. `Ω'` is algebraically closed. This is the source theorem
   `valuationSubring_residueField_isAlgClosed` (M237.001): the residue field
   of a valuation ring of an algebraically closed field is algebraically
   closed. As recorded in the published M237 statement module
   (`...ResidueAlgebraicallyClosed.Initial.Statements`), M237.001 is the
   existing Library theorem `Langlands.LocalGalois.residue_isAlgClosed`
   (module `Langlands.Galois.Local.SpectralProof`), which is used here.
6. Transfer along `e.symm` (`IsAlgClosed.of_ringEquiv`).

## Binders and universes

The definition takes the explicit field `(K : Type)` and the instance binders
`[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]` of the source section variables. `K` lives in
`Type`, as in the source. The definition has no universe parameters.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`:

- file
  [`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean),
  SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`:
  namespace, opens and section variables at lines 31–46; local instance
  M249.001 at lines 48–50; M249.015 at lines 262–266; M249.016 at lines
  268–302 (proof inlined); M249.022: docstring at lines 400–402, definition
  at lines 403–415;
- file
  [`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ValuedFieldTheory/Ramification/HilbertRamification/ResidueExactSequence.lean),
  SHA-256 `cf543e2e441798c17d1b7b07167e0508d629b6ed143c66b624c04889f0b5927e`:
  section variables at lines 39–40; M243.008–M243.010 at lines 102–144
  (inlined); M243.011–M243.012 at lines 146–163 (supplied by instance
  search); M243.030 at lines 394–413 (proof inlined).

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.localResidueDegree` (M249.022) | `Langlands.NYLL.LocalClassFieldTheory.localResidueDegree` (this module) |
| `LocalClassFieldTheory.localSeparableResidueAlgAction` (M249.020, used) | the same name under `Langlands.NYLL.` (published) |
| `LocalClassFieldTheory.residueAbsoluteDegreeIn` (M236.017, used) | the same name under `Langlands.NYLL.` (published) |
| `LocalClassFieldTheory.localDecompositionResidueFintype` (M249.015, used by instance search) | the same name under `Langlands.NYLL.` (published instance) |
| `LocalClassFieldTheory.localSelectedResidueIsAlgClosed` (M249.016, used by instance search) | local `haveI` fact with the source proof; target `localSelectedResidueIsAlgClosedStatement` published |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueExtension_normal` (M243.030, used by instance search) | local `haveI` fact `hNormal` with the source proof |
| `...decompositionGroup_action_locallyConstant`, `...decompositionGroup_continuousSMul`, `...decompositionGroup_compactSpace` (M243.008–M243.010, private, used) | local facts in the `hNormal` proof, with their source proofs |
| `...decompositionFixedSubring_smulCommClass`, `...decompositionFixedSubring_isInvariant` (M243.011, M243.012, private, used) | found by instance search: Mathlib's `FixedPoints.subring` instance; published `decompositionFixedSubring.instIsInvariant` |
| `RamificationTheory.Ideal.Quotient.normal_of_profinite` (M242.001, used) | the same name under `Langlands.NYLL.` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup_isClosed` (used) | the same name under `Langlands.NYLL.` (published) |
| `LocalClassFieldTheory.localAbsoluteValuationSubring` (M249.003, private, used) | `Langlands.NYLL.PortInternal.M249.d003` (published) |
| `LocalClassFieldTheory.localSeparableClosureAlgebra` (M249.001, local instance, used) | `Langlands.NYLL.PortInternal.M249.d001` (published), activated locally |
| `LocalClassFieldTheory.valuationSubringComapResidueMap` (M237.004, used) | the same name under `Langlands.NYLL.` (published) |
| `LocalClassFieldTheory.valuationSubring_comap_residueField_isPurelyInseparable` (M237.006, used) | the same name under `Langlands.NYLL.` (published) |
| `LocalClassFieldTheory.valuationSubring_residueField_isAlgClosed` (M237.001, used) | `Langlands.LocalGalois.residue_isAlgClosed` (published, reused) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField`, `selectedResidueField` (M243.003, M243.004, used) and their instances (M243.020, M243.021) | the same names under `Langlands.NYLL.` (published) |

## Relation to existing declarations

Row M249.022 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the adapted name and the module stem
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum`.
The name does not exist in the current Library (commit
`72480b70c88adff84a438bd7029d64ee3977469c`) or in Mathlib.

The Library has a declaration with the same short name,
`Langlands.Weil.Local.localResidueDegree F` (module
`Langlands.Weil.Local.Assembly`). It is a different object, not a duplicate:

- it is defined for a `PadicField p` structure `F`, not for an arbitrary
  nonarchimedean local field `K` with the `ValuativeRel` and
  `IsNonarchimedeanLocalField` instances used by the NYLL port;
- its domain is `Field.absoluteGaloisGroup F.Carrier` and its codomain is
  `Langlands.Weil.ProfiniteIntegers`, not `Gal(SeparableClosure K / K)` and
  `ZHatMul`;
- it is normalized by geometric Frobenius (its docstring) and built from the
  Library's `absoluteResidueHom` and `Galois.FiniteField.toProfiniteIntegers`,
  while M249.022 uses the arithmetic-Frobenius degree `residueAbsoluteDegreeIn`
  on the residue field of the NYLL valuation ring.

In the Library, `residueAbsoluteDegreeIn` otherwise occurs only in the M236
modules under `ResidueAlgebraicClosureDegree`, the M238.001 datum
`residueDatumIn` and the M244.005 statement. None of these is a composite with a Galois action of a local field.
No Library module states `Normal` for `decompositionResidueField` over
`selectedResidueField`, and `IsAlgClosed (selectedResidueField ...)` occurs
only in the M249.016 target.

## Imports and modification record

The direct imports are the published modules:

- `...LocalReciprocity.LocalResidueDatum.U020.Definitions` (M249.020; it also
  brings `localSeparableValuationSubring`, `d001` and `d003`);
- `...LocalReciprocity.LocalResidueDatum.U015.Definitions` (the instance
  M249.015);
- `...LocalReciprocity.ResidueAlgebraicClosureDegree.Equiv.Definitions`
  (M236.017);
- `...LocalReciprocity.ResidueAlgebraicallyClosed.U006.Proofs` (M237.006, and
  through it M237.004);
- `Langlands.NYLL.ValuedFieldTheory.Ramification.ClosedSubgroups.DecompositionGroupIsClosedProof`;
- `Langlands.NYLL.ValuedFieldTheory.Ramification.ProfiniteInvariant.NormalProof`
  (M242.001);
- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.IsInvariantProof`
  (M243.014);
- `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`
  (M243.020, M243.021, and through its imports M243.016 and M243.019);
- `Langlands.Galois.Local.SpectralProof` (`residue_isAlgClosed`).

They replace the source's four imports (`ResidueActionIndex`,
`FiniteIntegralClosure`, `FiniteExtensionCorrespondence` and
`FiniteExtensionCompleteDVF`), which serve the other declarations of the
source file. Every transitive import lies in the approved Mathlib environment
or the published Library.

Worker 57 extracted this source definition on 15 November 2026. The Lean
header records the change. The changes are:

- the definition is in the namespace `Langlands.NYLL.LocalClassFieldTheory`.
  Its docstring, type and both structure fields are the source text;
- the source writes the structure with `where`. Here the body is two `haveI`
  facts followed by the same structure as a structure instance;
- the two `haveI` facts are the source instances M243.030 and M249.016,
  proved by their source proofs. Compared line by line, the differences are:
  `L` and `A` are specialized to `SeparableClosure K` and
  `localSeparableValuationSubring K`; the private helpers M243.008–M243.010
  are inlined at their use; the `let`s of M243.011–M243.012 are omitted
  because instance search finds the published instances; M249.016 uses
  `hNormal` and `Langlands.LocalGalois.residue_isAlgClosed` in place of the
  source names; and fully qualified Library names replace the source names;
- the imports are replaced as described above;
- the source opens are replaced by `open Langlands.NYLL.ClassFormation` (for
  `ZHatMul`), the open of
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`,
  and `open scoped Pointwise` (for the coset `σ • E.fixingSubgroup` in the
  M243.008 proof). The other source opens provide nothing this definition
  uses and are omitted. The local instance M249.001 is activated by
  `attribute [local instance]`; M249.002 is not needed.

Every other source declaration is omitted. In particular the surjectivity
theorem `localResidueDegree_surjective` (M249.023) and the datum
`localResidueDatum` (M249.024) are not part of this module. No theorem,
instance, notation or alias is introduced: the inlined facts are local to the
definition body.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`), against Library commit
`72480b70c88adff84a438bd7029d64ee3977469c`. Inspection reports the
declaration as a definition without level parameters, depending only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. A
development probe (not part of this candidate) confirmed by `#synth` that
instance search finds `localDecompositionResidueFintype K`, Mathlib's
`FixedPoints.subring` `SMulCommClass` instance,
`decompositionFixedSubring.instIsInvariant` and `PerfectField.ofFinite` at
the points described above. These development checks are not independent
acceptance.

## Use downstream

In the source, `localResidueDegree` is used by the surjectivity theorem
M249.023 (lines 417–436) and by the class-formation datum `localResidueDatum`
(M249.024, lines 438–442), whose `degree` field it is.

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
