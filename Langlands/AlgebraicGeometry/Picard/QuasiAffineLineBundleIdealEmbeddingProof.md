# Embedding a line bundle into the structure module on a quasi-affine scheme

`Langlands.AlgebraicGeometry.Picard.quasiAffineLineBundleIdealEmbedding`
proves exactly the published proposition
`Langlands.AlgebraicGeometry.Picard.QuasiAffineLineBundleIdealEmbeddingStatement.{u}`.
Its type has no outer hypotheses and is polymorphic in the arbitrary universe
`u`. The proposition and all its imports are unchanged.

Thus, for every locally Noetherian quasi-affine scheme `X` and every actual
line bundle `D : LineBundle X`, the proof constructs a morphism of module
sheaves

```text
s : D.obj ⟶ SheafOfModules.unit X.ringCatSheaf
```

and proves `Mono s`. No reducedness, integrality, connectedness, factoriality,
nonemptiness or field hypothesis is added. Empty schemes are included.

## The implemented proof

1. Mathlib's quasi-affine convention supplies `CompactSpace X`. The published
   theorem `IsLocallyFreeRankOne.exists_finite_mono_detector`, applied to
   `D.property`, gives a finite set `E` and `IsMonoDetector D.obj E`. This
   condition says that an actual map `D.obj → O_X` is a monomorphism if its
   underlying additive stalk maps are isomorphisms at every point of `E`.
   The set is chosen before the map. Its construction uses associated primes
   on a finite affine trivializing cover, so no scheme-level associated-point
   interface is needed.
2. The published theorem `quasiAffineLineBundleFiniteSection` applied to the
   actual dual line bundle `D.dual` gives a global section `t` of that bundle
   with `E ⊆ trivializationOpen D.dual.obj t`. This is a section of the dual
   itself; no tensor power is substituted.
3. Take `s := D.evalSection t`, the actual composite

   ```text
   D --right unitor inverse--> D ⊗ O_X
     --identity ⊗ sectionHom(t)--> D ⊗ D^∨
     --dualTensorEval--> O_X.
   ```

   The published helper `D.isIso_stalk_evalSection_of_mem t` makes its
   underlying additive stalk map an isomorphism at each point where `t`
   generates. In particular, it is an isomorphism at every point of `E`.
4. Apply the detector to this morphism and these stalk isomorphisms. This
   proves `Mono (D.evalSection t)` and supplies the required existential pair.

The proof imports the statement and the published modules
`QuasiAffineLineBundleFiniteSectionProof`, `LineBundleFiniteMonoDetector` and
`LineBundleDualSectionEvaluation`. It uses none of the open-immersion
line-bundle-extension or valuative conclusions excluded by the task.

## Provenance

The target is the quasi-affine case of Stacks Project Lemma 31.16.12,
tag [0AYM](https://stacks.math.columbia.edu/tag/0AYM), applied to the dual line
bundle as explained in the statement's Markdown. The registered retained
source is `stacks-open-line-bundle-extension-0bd9-2026-11-01`, directory SHA256
`e04f95facf97c45df0e888af89a8d92fd61988dcb397e6354110b6e4d184380d`.
The construction follows its regular-section argument, with finite
associated-prime tests on affine charts in place of an intrinsic global
associated-point set. Finite-point generation is supplied by the published
proof based on Stacks tag 0F20; that proof's Markdown describes its local
extension and finite-induction steps.

Worker 311 authored the finite detector and this assembly. Worker 421
authored the dual-section evaluation construction, with Worker 311's
contribution acknowledged in that helper. Worker 1161 authored the
finite-section proof used here. All three prerequisite modules are imported
from the published Library.
