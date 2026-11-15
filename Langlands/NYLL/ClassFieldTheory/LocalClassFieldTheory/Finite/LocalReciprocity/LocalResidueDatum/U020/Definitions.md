# The continuous local residue action (M249.020)

Let `K` be a nonarchimedean local field (a field with `ValuativeRel`,
`TopologicalSpace` and `IsNonarchimedeanLocalField` instances). Finite local
reciprocity fixes a valuation ring `A = localSeparableValuationSubring K` of
the separable closure `K^sep = SeparableClosure K`. Its decomposition group
over `K` is the whole Galois group. Every `K`-automorphism `σ` of `K^sep`
therefore maps `A` onto itself and acts on the residue field `Ω` of `A`. This
gives a group homomorphism from `Gal(K^sep / K)` to the group of
automorphisms of `Ω` over the base residue field `κ`.

This module defines
`Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction K`
(source unit M249.020). It is that homomorphism, bundled as a continuous
monoid homomorphism for the Krull topologies on both Galois groups.

In Lean, with `variable (K : Type) [Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`:

```lean
noncomputable def Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction :
    Gal(SeparableClosure K / K) →ₜ*
      (selectedResidueField (localSeparableValuationSubring K) ≃ₐ[
        decompositionResidueField K (localSeparableValuationSubring K)]
          selectedResidueField (localSeparableValuationSubring K)) where
  toMonoidHom :=
    residueAlgActionOfEqTop K
      (localSeparableValuationSubring K)
      (localSeparableDecompositionGroup_eq_top K)
  continuous_toFun := by
    have h019 : Langlands.NYLL.PortInternal.M249.d019Statement := by
      ...  -- the source proof of M249.019, described below
    exact h019 K
```

The field `toMonoidHom` carries all the data. The field `continuous_toFun` is
a proposition, so its proof does not change the map.

## The objects involved

The names below are in the namespace
`Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`
unless another namespace is given.

- `Gal(SeparableClosure K / K)` is Mathlib's notation for
  `SeparableClosure K ≃ₐ[K] SeparableClosure K`, the absolute Galois group
  of `K` built from Mathlib's separable closure.
- `localSeparableValuationSubring K : ValuationSubring (SeparableClosure K)`
  is the chosen valuation ring `A` (M249.006, module
  `...LocalReciprocity.LocalResidueDatum.U006.Definitions`, namespace
  `Langlands.NYLL.LocalClassFieldTheory`).
- `localSeparableDecompositionGroup_eq_top K` is the published theorem
  `decompositionGroup K (localSeparableValuationSubring K) = ⊤` (M249.010,
  module `...LocalResidueDatum.U010.Proofs`, namespace
  `Langlands.NYLL.LocalClassFieldTheory`).
- `selectedResidueField A` is the residue field `Ω` of `A` (M243.004).
  `decompositionResidueField K A` is the base residue field `κ` of the
  residue-action exact sequence (M243.003). It is the quotient of the subring
  of `A` fixed by the decomposition group by the contraction of the maximal
  ideal of `A`. Its `Field` instance (M243.020) and the `κ`-algebra structure
  on `Ω` (M243.021) are published in
  `Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`.
- `residueAlgActionOfEqTop K A hA` (M244.003, module
  `...LocalReciprocity.ResidueActionIndex.U003.Definitions`, namespace
  `Langlands.NYLL.LocalClassFieldTheory`) is the monoid homomorphism
  `(L ≃ₐ[K] L) →* (Ω ≃ₐ[κ] Ω)` for a Galois extension `L / K` whose
  decomposition group of `A` is everything (`hA`). It is the published
  residue action of the decomposition group, `decompositionGroupResidueAction`,
  composed with `toDecompositionGroupOfEqTop K A hA` (M244.001), the
  isomorphism from the whole group onto the decomposition group. Here
  `L = SeparableClosure K`, which is Galois over `K` by a Mathlib instance.
- The topology on the domain is Mathlib's Krull topology on
  `Gal(SeparableClosure K / K)`. The topology on the codomain is Mathlib's
  Krull topology on `Ω ≃ₐ[κ] Ω`. A set is a neighbourhood of `1` in such a
  group exactly when it contains the fixing subgroup of some
  finite-dimensional intermediate field (Mathlib's
  `krullTopology_mem_nhds_one_iff`).
- `→ₜ*` is Mathlib's `ContinuousMonoidHom`: a monoid homomorphism
  (`toMonoidHom`) together with a proof that its function is continuous
  (`continuous_toFun`).

## Why the continuity proof is in this body

In the source, `continuous_toFun` is the private theorem
`localSeparableResidueAlgAction_continuous K` (M249.019, lines 323–379). The
port publishes its type as the closed target
`Langlands.NYLL.PortInternal.M249.d019Statement` (module
`...LocalResidueDatum.U019.Statements`):

```lean
def Langlands.NYLL.PortInternal.M249.d019Statement : Prop :=
  ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K],
    Continuous
      (residueAlgActionOfEqTop K
        (localSeparableValuationSubring K)
        (localSeparableDecompositionGroup_eq_top K))
```

The proof of that target is not yet in the Library (proof Task 7028). So the
body proves `d019Statement` in place, with the source proof, and applies it
to `K`. The result has exactly the type of the source field. Only the proof
of a proposition differs from the source, so the map and the structure are
the source's. When the proof `PortInternal.M249.d019` is published, the two
proofs are equal by proof irrelevance.

## The implemented continuity proof

The body introduces a fresh `K` with its four instances and proves
`Continuous (residueAlgActionOfEqTop K A hA)` as follows. The steps are the
source lines 328–379, with three private source units inlined.

1. **Finite base residue field (M249.014, inlined).** The source instance
   `localDecompositionResidueFinite` (lines 252–260) is a local fact with its
   source proof. The residue field `(localCompleteDVF K).residueField` is
   finite: `change` turns it into Mathlib's `𝓀[K]`, and Mathlib's instance
   `Finite 𝓀[K]` for nonarchimedean local fields applies
   (`Mathlib.NumberTheory.LocalField.Basic`). Then `Finite.of_equiv`
   transfers finiteness along the published ring equivalence
   `localBaseResidueEquivDecompositionResidue K` (M249.012, module
   `...LocalResidueDatum.U011.Definitions`) to `κ`. The closed target of
   M249.014 is published (`localDecompositionResidueFiniteStatement`), but
   its proof (Task 6979) is not, so the proof is repeated here.
2. **Names.** The proof sets `A`, `k := κ`, `Omega := Ω`,
   `hA := localSeparableDecompositionGroup_eq_top K` and
   `rho := residueAlgActionOfEqTop K A hA`, as in source lines 329–333.
3. **Lifts of residue classes (M249.017, M249.018, inlined).** The private
   source definition `localSelectedResidueLift` (lines 306–310) picks, for
   each `x : Ω`, an element of `A` with residue class `x`, by
   `Classical.choose (IsLocalRing.residue_surjective x)`. Here it is the local
   function `lift`. The private source lemma
   `localSelectedResidueLift_residue` (lines 312–317) states
   `IsLocalRing.residue A (lift x) = x`, by `Classical.choose_spec`. Here it
   is the local fact `lift_residue`. Both are used only inside this proof.
4. **Reduction to the identity.** Mathlib's
   `continuous_of_continuousAt_one` reduces continuity of the monoid
   homomorphism `rho` to continuity at `1`. After unfolding `ContinuousAt`,
   using `rho 1 = 1` and unfolding `Filter.Tendsto`, it remains to show: for
   every neighbourhood `s` of `1` in `Ω ≃ₐ[κ] Ω`, the preimage `rho ⁻¹' s` is
   a neighbourhood of `1` in `Gal(K^sep / K)`.
5. **A finite residue subextension.** By `krullTopology_mem_nhds_one_iff`
   for `κ` and `Ω`, there is an intermediate field `E` of `Ω / κ`, finite
   dimensional over `κ`, whose fixing subgroup lies in `s`. Since `κ` is
   finite (step 1), `E` is finite (`Module.finite_of_finite`) and gets a
   `Fintype` structure (`Fintype.ofFinite`).
6. **A finite extension of `K`.** Let `lifts` be the finite set of the values
   in `K^sep` of `lift y`, for `y` in `E`. Let `F` be the intermediate field
   of `K^sep / K` generated over `K` by `lifts`. It is finite dimensional
   over `K` by `IntermediateField.finiteDimensional_adjoin`, since every
   element of `K^sep` is integral over `K` (`Algebra.IsIntegral.isIntegral`).
7. **The fixing subgroup of `F` maps into `s`.** By
   `krullTopology_mem_nhds_one_iff` for `K` and `K^sep`, it suffices that the
   fixing subgroup of `F` lies in `rho ⁻¹' s`. Let `σ` fix `F` pointwise. It
   suffices that `rho σ` fixes `E` pointwise, since the fixing subgroup of `E`
   lies in `s`. Let `x ∈ E`, `y = ⟨x, _⟩ : E` and `a = lift y`. Then `a`
   lies in `lifts` (`Finset.mem_image`), hence in `F`
   (`IntermediateField.subset_adjoin`), so `σ a = a`
   (`IntermediateField.mem_fixingSubgroup_iff`). Rewrite `y` as the residue
   class of `a` (by `lift_residue`). By definition of `rho`, `rho σ` sends
   this class to the residue class of
   `toDecompositionGroupOfEqTop K A hA σ • a`. That element of `A` has value
   `σ a = a` in `K^sep`, so it equals `a` (`Subtype.ext`), and `rho σ` fixes
   `y`.

After this proof, the body concludes with `exact h019 K`.

## Binders and universes

The definition takes the explicit field `(K : Type)` and the instance binders
`[Field K] [ValuativeRel K] [TopologicalSpace K]
[IsNonarchimedeanLocalField K]` of the source section variables. `K` lives in
`Type`, as in the source. The definition has no universe parameters.

## Original source and declaration map

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean),
SHA-256 `be13bf4f92820faee2f89e127b56f6bbf23a8f5a4fe93fd2e5e58745ca7d4396`.
The relevant lines are:

- the namespace, opens and section variables, lines 31–46:
  `namespace LocalClassFieldTheory`, `open ClassFormation`,
  `open ValuationTheory RamificationTheory LocalFieldTheory`,
  `noncomputable section`, `open scoped Pointwise ValuativeRel`,
  `open HilbertRamification.ValuationSubring`,
  `open Field.absoluteGaloisGroup`, and the `variable` line for `K`;
- M249.014, instance `localDecompositionResidueFinite`, lines 252–260
  (inlined);
- M249.017, private definition `localSelectedResidueLift`, lines 306–310
  (inlined);
- M249.018, private lemma `localSelectedResidueLift_residue`, lines 312–317
  (inlined);
- M249.019, private theorem `localSeparableResidueAlgAction_continuous`:
  docstring and type at lines 319–327, proof at lines 328–379 (proof
  inlined);
- M249.020: docstring at line 381, definition at lines 382–391.

The readable original is in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/`. Attribution is also registered
as `nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The Library's `notes/errata/` has no NYLL entry.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.localSeparableResidueAlgAction` (M249.020) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableResidueAlgAction` (this module) |
| `LocalClassFieldTheory.localSeparableResidueAlgAction_continuous` (M249.019, private, used) | closed target `Langlands.NYLL.PortInternal.M249.d019Statement` (published), proved in this body |
| `LocalClassFieldTheory.localDecompositionResidueFinite` (M249.014, used) | local fact in this body; closed target `localDecompositionResidueFiniteStatement` published |
| `LocalClassFieldTheory.localSelectedResidueLift` (M249.017, private, used) | local function `lift` in this body |
| `LocalClassFieldTheory.localSelectedResidueLift_residue` (M249.018, private, used) | local fact `lift_residue` in this body |
| `LocalClassFieldTheory.residueAlgActionOfEqTop` (M244.003, used) | `Langlands.NYLL.LocalClassFieldTheory.residueAlgActionOfEqTop` (published) |
| `LocalClassFieldTheory.toDecompositionGroupOfEqTop` (M244.001, used) | `Langlands.NYLL.LocalClassFieldTheory.toDecompositionGroupOfEqTop` (published) |
| `LocalClassFieldTheory.localSeparableValuationSubring` (M249.006, used) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableValuationSubring` (published) |
| `LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (M249.010, used) | `Langlands.NYLL.LocalClassFieldTheory.localSeparableDecompositionGroup_eq_top` (published) |
| `LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue` (M249.012, used) | `Langlands.NYLL.LocalClassFieldTheory.localBaseResidueEquivDecompositionResidue` (published) |
| `RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField`, `selectedResidueField` (M243.003, M243.004, used) and their instances (M243.020, M243.021) | the same names under `Langlands.NYLL.` (published) |

Row M249.020 of the published partition
[`notes/reuse/nyll-public-port/m241-m258.md`](../../../../../../../../notes/reuse/nyll-public-port/m241-m258.md)
reserves the adapted name and the module stem
`Langlands/NYLL/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum`.
The name does not exist in the current Library or Mathlib. The Library has
no other declaration with this body: in the Library, `residueAlgActionOfEqTop`
occurs only in the M244.003 module and the M249.019 target. The Library's
`Langlands.Weil.Local.localResidueMap` (module `Langlands.Weil.Local.Assembly`)
is a different object: a continuous map between the absolute Galois groups
of a `PadicField` and of its residue field, built from other constructions.
Mathlib's analogous residue action `Ideal.Quotient.stabilizerHom`
(`Mathlib.RingTheory.Ideal.Over`) is a monoid homomorphism on a stabilizer
subgroup, and no Mathlib declaration bundles it as a continuous homomorphism.

## Imports and modification record

The direct imports are the published modules
`...LocalReciprocity.LocalResidueDatum.U019.Statements` (the M249.019 target;
it imports the definition of `residueAlgActionOfEqTop` and the M249.010
proof), `...LocalReciprocity.LocalResidueDatum.U011.Definitions` (M249.012,
which also brings `localCompleteDVF` and its projections) and
`Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence.ResidueFields`
(the instances M243.020 and M243.021; also imported transitively through the
first module). They replace the source's four imports (`ResidueActionIndex`,
`FiniteIntegralClosure`, `FiniteExtensionCorrespondence` and
`FiniteExtensionCompleteDVF`), which serve the other declarations of the
source file. Every transitive import lies in the approved Mathlib environment
or the published Library.

Worker 85 extracted this source definition on 15 November 2026. The Lean
header records the change. The changes are:

- the definition is in the namespace `Langlands.NYLL.LocalClassFieldTheory`.
  Its docstring, type and `toMonoidHom` field are the source text;
- the field `continuous_toFun` is not the source term
  `localSeparableResidueAlgAction_continuous K`. It is a tactic proof of the
  published target `PortInternal.M249.d019Statement`, applied to `K`. That
  proof is the source proof of lines 328–379, compared line by line, with
  three changes: it starts with `intro K _ _ _ _`, it proves the M249.014
  finiteness fact first, and it uses the local `lift` and `lift_residue` in
  place of `localSelectedResidueLift K` and `localSelectedResidueLift_residue K`;
- the imports are replaced as described above;
- the source opens are replaced by `open scoped ValuativeRel` (for the
  notation `𝓀[K]` in the M249.014 proof) and the fully qualified opens of
  `Langlands.NYLL.LocalFieldTheory` (for `localCompleteDVF`) and
  `Langlands.NYLL.RamificationTheory.HilbertRamification.ValuationSubring`.
  The opens of `ClassFormation`, `ValuationTheory`,
  `Field.absoluteGaloisGroup` and the scoped `Pointwise` notation provide
  nothing this definition uses, and are omitted.

The source's two local instances (M249.001, M249.002) are not needed by this
definition and are not activated. Every other source declaration is omitted.
In particular the surjectivity theorem
`localSeparableResidueAlgAction_surjective` (M249.021) and the degree map
`localResidueDegree` (M249.022) are not part of this module. No theorem,
instance, notation or alias is introduced: the M249.014, M249.017 and M249.018
inlines are local to one proof.

The module compiled with zero errors and zero warnings in approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`). Inspection reports the
declaration as a definition without level parameters, depending only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. A
development probe (not part of this candidate) checked by `rfl` that
`(localSeparableResidueAlgAction K).toMonoidHom` is
`residueAlgActionOfEqTop K (localSeparableValuationSubring K)
(localSeparableDecompositionGroup_eq_top K)`. This development check is not
independent acceptance.

## Use downstream

In the source, `localSeparableResidueAlgAction` is used by the surjectivity
theorem M249.021 (source lines 393–398) and by the local degree map
`localResidueDegree` (M249.022, from line 400). That map composes this
action with the intrinsic finite-field degree map.

## Attribution

The original copyright and author header is retained verbatim: copyright
2026 Naganori Yamaguchi, all rights reserved; authors Naganori Yamaguchi
(assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../../licenses/NYLL/LICENSE) (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and [NOTICE](../../../../../../../../licenses/NYLL/NOTICE) (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
remain in `licenses/NYLL/`. Worker 85 adapted this unit directly from the
pinned original; no other project worker supplied code.
