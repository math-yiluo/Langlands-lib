# Tensor products of global module-sheaf sections

For every scheme `X : Scheme.{u}` and arbitrary actual module sheaves
`M N : X.Modules`, this module constructs

```lean
Langlands.SchemeModule.tensorSection
  (M N : X.Modules) (s : GlobalSections M) (t : GlobalSections N) :
  GlobalSections (Langlands.Scheme.Modules.tensorObj M N)
```

All new declarations are in `Langlands.SchemeModule`. The tensor object,
tensor maps and left unit isomorphism are the published constructions in
`Langlands.Scheme.Modules`. No affine, separated, noetherian, quasicoherent,
flatness, invertibility, residue-field, or monoidal-preservation premise occurs.

## Construction and characterization

`sectionHomEquiv M` is the equivalence

```lean
GlobalSections M ≃ (structureModule X ⟶ M).
```

Its forward map is the existing `sectionHom M`. Its inverse evaluates
Mathlib's compatible family `M.unitHomEquiv f` at the top open. A compatible
family is determined by that value: compatibility with the morphism from the
top open to each open recovers its other values. Conversely, restricting a
global section to the top open gives that section. These observations prove
both inverse identities. `sectionHom_injective M` exposes the resulting
injectivity. `sectionHom_app_one M s U` proves that the section morphism takes
one on `U` to the restriction of `s`.

`structureModule_eq_structureSheaf X` is proved by reflexivity. Both existing
definitions are exactly `SheafOfModules.unit X.ringCatSheaf`; no transport
isomorphism or extra choice is needed between them.

`tensorSection M N s t` is the inverse of `sectionHomEquiv (tensorObj M N)`
applied to the actual composite

```lean
(tensorLeftUnitor (structureSheaf X)).inv ≫
  tensorMap (sectionHom M s) (sectionHom N t).
```

The inverse left unit isomorphism has source the structure sheaf and target
its tensor square. Tensoring the two section morphisms then gives a morphism
to `tensorObj M N`. This defines a particular section through an explicit
equivalence, with no choice of an arbitrary section or asserted geometric
property. `sectionHom_tensorSection M N s t` proves exactly

```lean
sectionHom (tensorObj M N) (tensorSection M N s t) =
  (tensorLeftUnitor (structureSheaf X)).inv ≫
    tensorMap (sectionHom M s) (sectionHom N t).
```

This is the unit-morphism characterization of the usual product section.
The imported tensor is sheafification of the sectionwise tensor, its map
sheafifies the tensor of the two maps, and its left unitor sheafifies the
sectionwise left unitor and composes with the sheafification counit.
Thus the composite above is the categorical construction of the product of
the two actual sections.

## Naturality and evaluation

`sectionHom_naturality f s` states

```lean
sectionHom N (f.app ⊤ s) = sectionHom M s ≫ f
```

for every `f : M ⟶ N`. Its proof uses naturality of the underlying presheaf
map and the compatible-family equivalence.

`tensorSection_naturality f g s t` states, for arbitrary
`f : M ⟶ M'` and `g : N ⟶ N'`,

```lean
(tensorMap f g).app ⊤ (tensorSection M N s t) =
  tensorSection M' N' (f.app ⊤ s) (g.app ⊤ t).
```

The proof applies injectivity of `sectionHom`, uses the characterization and
section morphism naturality, and finishes with composition preservation by
the tensor bifunctor. The proof explicitly types the section morphisms with
source `structureSheaf X`, and supplies the three object pairs to
`Functor.map_comp`, avoiding expensive inference through sheafification.

`tensorSection_restrict M N s t U` gives an evaluation formula on every open
`U`: the restriction of the product is the value of
`tensorMap (sectionHom M s) (sectionHom N t)` at `U` on the image of one
under the inverse left unitor of the structure sheaf. Its proof evaluates
`sectionHom_tensorSection` at one and uses `sectionHom_app_one`.
This formula uses the existing sheaf tensor maps and unitor; the module does
not introduce a separate element-level notation for the sheafification unit.

## Source, provenance and scope

This is derived internal categorical infrastructure for the product section
in the opening paragraph of the Stacks Project, Section 28.27
([tag 01PR](https://stacks.math.columbia.edu/tag/01PR)), and for the
product used in the proof of Lemma 28.27.5. The registered source is
`stacks-ampleness-tensor-isomorphism-2026-10-24`, retained file
`Stacks Project - Ampleness tensor and isomorphism transport (HTML snapshot 2026-10-24)/01PR.html`,
directory SHA256
`23bfc9d1d2b4467556c7308dd203f22596c80d2f5276f1d5f9829673427e2f2d`.
The opening paragraph denotes the product of global sections of invertible
sheaves by their tensor. Lemma 28.27.5 uses products of positive powers in
the proof of ampleness. The present arbitrary-module construction and its
categorical lemmas are internal packaging, rather than literal declarations
of that source.

The registered current source/comment snapshot
`stacks-01pr-current-errata-check-2026-10-26` was also checked: its opening
product passage and Lemma 28.27.5 agree, and its five comments concern
ampleness on disjoint open subschemes rather than a correction to this product.
No source-specific errata note was found in the current public notes.

The construction imports the published `SectionLocus` and `Tensor` modules
and uses Mathlib's `SheafOfModules.unitHomEquiv` and presheaf naturality.
The pinned environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`:
Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.
Worker 694 supplied a useful elaboration observation concerning
`unitHomEquiv` when applying its injectivity.

The module constructs no section powers, power rearrangement isomorphisms,
residue comparison, rank-one comparison, pullback comparison or ampleness
transport. The equality of the whole maximal trivialization open of this
product with the intersection of the two individual opens for line bundles
remains a separate statement and proof obligation.

The shared formula `Langlands.SchemeModule.LineBundleDescent.sectionHom_app`
sends `a ∈ Γ(X, U)` to `a • s|_U`. Its unchanged declaration is extracted
from `Picard/LineBundleDescent` and follows from `sectionHom_app_one` and
linearity. It applies to every module sheaf and global section.
