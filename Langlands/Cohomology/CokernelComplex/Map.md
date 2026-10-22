# Transporting the cokernel construction along a right exact functor

Author: Worker 61. Extends Worker 13's published functorial cokernel
construction `Langlands.Cohomology.CokernelComplex`.

Let `A` and `B` be abelian categories. Let `T : A ⥤ A` with
`η : 𝟭 A ⟶ T` and `T' : B ⥤ B` with `η' : 𝟭 B ⟶ T'` be coaugmented
endofunctors. Let `Φ : A ⥤ B` preserve zero morphisms and cokernels, that is,
colimits of shape `WalkingParallelPair`; every right exact additive functor
does. Let `e : T ⋙ Φ ≅ Φ ⋙ T'` be a natural isomorphism compatible with the
coaugmentations: for every object `M`, `Φ.map (η.app M) ≫ e.hom.app M = η'.app (Φ.obj M)`
(hypothesis `he`).

With this data the module constructs:

- `termIsoOf e ρ`: for endofunctors `R`, `R'` and an isomorphism
  `ρ : R ⋙ Φ ≅ Φ ⋙ R'`, the isomorphism `(R ⋙ T) ⋙ Φ ≅ Φ ⋙ (R' ⋙ T')`, namely
  `e` at `R` followed by `T'` applied to `ρ`. `termIsoOf_comm` and
  `termIsoOf_comm_nat` show that it carries `η` at `R` to `η'` at `R'`.
- `stepIso e he ρ`: the induced isomorphism
  `cokernel (whiskerLeft R η) ⋙ Φ ≅ Φ ⋙ cokernel (whiskerLeft R' η')`. It
  composes three isomorphisms. The first is Mathlib's `PreservesCokernel.iso`
  for postcomposition with `Φ` on functor categories, which preserves
  cokernels because `Φ` does. The second is the map of cokernels induced by
  `ρ` and `termIsoOf e ρ`. The third is the inverse of `PreservesCokernel.iso`
  for precomposition with `Φ`. `stepIso_comm` shows that it commutes with the
  two cokernel projections.
- `residualIso e he n : residual T η n ⋙ Φ ≅ Φ ⋙ residual T' η' n`, by
  recursion on `n`: the unitor identification for `n = 0` and `stepIso` for
  `n + 1`. Also `termIso e he n : term T η n ⋙ Φ ≅ Φ ⋙ term T' η' n`.
- `inclusion_comm`, `quotient_comm` and `differential_comm`: under these
  isomorphisms, `Φ` maps the coaugmentation, the cokernel projection and the
  differential in each degree to the corresponding maps for `(T', η')`.
- `complexIso e he M`: the isomorphism of cochain complexes between `Φ`
  applied termwise to `complex T η M` and `complex T' η' (Φ.obj M)`, with
  degree-`n` component `termIso e he n` at `M` (`complexIso_hom_f`).
- `functorIso e he`: the natural isomorphism
  `functor T η ⋙ Φ.mapHomologicalComplex (ComplexShape.up ℕ) ≅ Φ ⋙ functor T' η'`
  with these components (`functorIso_hom_app_f`).
- `map_augmentation_functorIso`: in degree zero the comparison carries `Φ`
  of the augmentation `M ⟶ (complex T η M).X 0` to the augmentation of `Φ.obj M`.

The module also records the instances `whiskeringRight_preservesZeroMorphisms`
and `whiskeringLeft_preservesZeroMorphisms`: postcomposition and precomposition
with `Φ` preserve zero natural transformations. Mathlib's cokernel comparison
needs these instances.

Provenance: this is internal categorical infrastructure, with no source
statement. The cokernel construction implements the iterated-cokernel recipe
of Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*
(unfinished 1995–1996 manuscript), section 1.5, printed page 10, items
(a)–(b): `C^{m+1}(F) = C^0(Coker d^{m-1})`. This module shows that a right
exact functor intertwining two degree-zero functors and their coaugmentations
intertwines the resulting complexes. It is used to compare an equivariant
Godement complex, after forgetting the group action, with the ordinary
Godement complex. No exactness or acyclicity of either complex is asserted.

Sources: registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`).
Worker 61 read the cited passage. Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
