# Tensor evaluation for the internal Hom and dual of scheme modules

For an arbitrary `AlgebraicGeometry.Scheme.{u}` X and actual Mathlib module sheaves
M, N in `X.Modules`, this module constructs the evaluation morphism of module
sheaves

```
internalHomTensorEval M N : tensorObj (internalHom M N) M ⟶ N
```

and its specialization to the dual, `dual M = internalHom M 𝒪_X`, with the
factors swapped:

```
dualTensorEval M : tensorObj M (dual M) ⟶ structureSheaf X.
```

It also gives the corresponding maps for the monoidal structure on `X.Modules`:

```
internalHomMonoidalEval M N : internalHom M N ⊗ M ⟶ N
dualMonoidalEval M : M ⊗ dual M ⟶ 𝟙_ X.Modules
```

All names are in `Langlands.Scheme.Modules`. The module uses no finiteness,
quasicoherence or local-freeness hypothesis. It does not claim that any of these
maps is an isomorphism.

The module reuses the published constructions and does not rebuild any of them:

- internal Hom, dual and the sectionwise pairings `internalHomEval` and `dualEval`
  from `Langlands.AlgebraicGeometry.ModuleDual`;
- the sheafified tensor `tensorObj`, `tensorHomEquiv`, `tensorComm` and
  `structureSheaf` from `Langlands.AlgebraicGeometry.Modules.Tensor`;
- the sheafification unit `tensorSheafifyUnit` from
  `Langlands.AlgebraicGeometry.Modules.PullbackTensor`;
- the monoidal instance on `X.Modules` and `localizedTensorIso` from
  `Langlands.AlgebraicGeometry.Modules.TensorMonoidal`;
- the braiding comparison `tensorMonoidalSymmetryComparison` from
  `Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs`.

## Source

The map is the evaluation map

```
𝓛 ⊗_{𝒪_X} Hom_{𝒪_X}(𝓛, 𝒪_X) → 𝒪_X
```

of the Stacks Project, Section 17.25,
[Invertible modules, tag 01CR](https://stacks.math.columbia.edu/tag/01CR). It appears
in the last paragraph of the proof of Lemma 17.25.2 and in the proof of
Lemma 17.25.4, where it is checked to be an isomorphism for locally free 𝓛 of rank 1.
Definition 17.25.1 there defines invertible modules, and Definition 17.14.1 in Section
17.14, [Locally free sheaves, tag 01C5](https://stacks.math.columbia.edu/tag/01C5),
defines locally free modules of rank r. This module uses neither definition. They
give the context in which Lemmas 17.25.2 and 17.25.4 use the evaluation map. The
registered source is `stacks-local-freeness-invertibility-sections-2026-10-21`, content
SHA-256 `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`, files
`01C5.html` and `01CR.html` of the HTML snapshot retrieved 2026-10-21. The comment
sections of both snapshot pages contain no comments ("Comments (0)"), so there are no
recorded errata for these passages.

Stacks gives no explicit formula for this map. It is the standard evaluation
s ⊗ φ ↦ φ(s), with 𝓛 as the left factor. `dualTensorEval` and `dualMonoidalEval`
follow this convention, with M on the left. The general map `internalHomTensorEval`
puts the internal Hom on the left because it is built from the Library pairing
`internalHomEval M N U f m = f(m)`, which takes the local morphism first.

## Sectionwise evaluation as a presheaf map

`internalHomTensorEvalPresheaf M N` is a morphism of presheaves of modules

```
(internalHom M N).val ⊗ M.val ⟶ N.val
```

for the sectionwise tensor product of presheaves of modules (Mathlib's
`PresheafOfModulesOfCommRing` monoidal structure, installed as
`presheafTensorMonoidalCategory`). On an open U its component is the O_X(U)-linear
map

```
Γ(internalHom M N, U) ⊗_{O_X(U)} Γ(M, U) → Γ(N, U),   f ⊗ m ↦ internalHomEval M N U f m,
```

obtained from the bilinear map `internalHomEval M N U` by `TensorProduct.lift`. For
naturality along an inclusion V ⊆ U it is enough to check elementary tensors
(`ModuleCat.MonoidalCategory.tensor_ext`). For f ⊗ m the sectionwise tensor restricts
to f|_V ⊗ m|_V, and the required identity

```
internalHomEval M N V (f|_V) (m|_V) = (internalHomEval M N U f m)|_V
```

is exactly the published `internalHomEval_restrict`. The simp lemma
`internalHomTensorEvalPresheaf_app_tmul` records f ⊗ m ↦ f(m) and holds by `rfl`.

## Descent to the sheaf tensor

`internalHomTensorEval M N` is defined as `(tensorHomEquiv _ _ _).symm` applied to
`internalHomTensorEvalPresheaf M N`. Here `tensorHomEquiv`, the sheafification
adjunction of the published tensor, identifies sheaf maps out of `tensorObj` with
presheaf maps out of the sectionwise tensor. The following results show that this is
the canonical evaluation and not an arbitrary map:

- `tensorHomEquiv_internalHomTensorEval`: the sectionwise tensor adjoint of
  `internalHomTensorEval M N` is `internalHomTensorEvalPresheaf M N`
  (`Equiv.apply_symm_apply`).
- `tensorHomEquiv_internalHomTensorEval_app_tmul`: that adjoint sends f ⊗ m, for
  sections f of `internalHom M N` and m of M over the same open U, to
  `internalHomEval M N U f m`.
- `internalHomTensorEval_app_tensorSheafifyUnit`: the same formula stated for the
  sheaf map itself. On U, the underlying presheaf map of `internalHomTensorEval M N`
  sends the image of f ⊗ m under the sheafification unit
  `tensorSheafifyUnit (internalHom M N) M` to `internalHomEval M N U f m`.
- `eq_internalHomTensorEval_iff`: a sheaf map
  g : tensorObj (internalHom M N) M ⟶ N equals `internalHomTensorEval M N` exactly
  when its sectionwise tensor adjoint sends every f ⊗ m to
  `internalHomEval M N U f m`. The forward direction is the previous formula. For the
  converse, injectivity of `tensorHomEquiv` reduces the claim to equality of presheaf
  maps. `PresheafOfModules.hom_ext` reduces that to equality on each open, and
  `ModuleCat.MonoidalCategory.tensor_ext` reduces it to elementary tensors.

The auxiliary lemma `tensorHomEquiv_eq_tensorSheafifyUnit_comp` holds for any three
module sheaves. It says that `tensorHomEquiv M N P g` is the sheafification unit of
the sectionwise tensor followed by the underlying presheaf map of g. It is
`Adjunction.homEquiv_unit` for the published `sheafifyAdjunction X`. It is used in
the two `_app_tensorSheafifyUnit` lemmas, where the remaining step is `rfl`.

### Relation to the sectionwise pairing

The Library's `internalHomEval M N U` and `dualEval M U` are bilinear pairings on
sections over a single open U. `internalHomTensorEvalPresheaf` is their linearization
on the sectionwise tensor product, which is the presheaf tensor product, compatible
with restriction. `internalHomTensorEval` is the unique sheaf map out of the
sheafified tensor through which it factors via the sheafification unit. A section of
the sheaf tensor is in general only locally a finite sum of images of elementary
tensors. So the module states the formula on those images, and the uniqueness lemma
determines the sheaf map from that formula.

## The dual evaluation

`dualTensorEval M` is the composite

```
tensorObj M (dual M) --(tensorComm M (dual M)).hom--> tensorObj (dual M) M
    --internalHomTensorEval M 𝒪_X--> 𝒪_X.
```

Here 𝒪_X is the published `Langlands.SchemeModule.structureModule X`, from which
`dual M` is built. The stated codomain `structureSheaf X` is the same object: both
are defined as `SheafOfModules.unit X.ringCatSheaf`. The swap `tensorComm` is the
sheafification of the sectionwise braiding.

- `tensorHomEquiv_dualTensorEval`: the sectionwise tensor adjoint of
  `dualTensorEval M` is the sectionwise braiding `(β_ M.val (dual M).val).hom`
  followed by `internalHomTensorEvalPresheaf M 𝒪_X`. Since `tensorComm` is
  sheafification applied to the braiding, this is the naturality of the
  sheafification adjunction's hom-equivalence in the source,
  `Adjunction.homEquiv_naturality_left`, combined with
  `tensorHomEquiv_internalHomTensorEval`.
- `tensorHomEquiv_dualTensorEval_app_tmul`: that adjoint sends m ⊗ φ, for sections
  m of M and φ of `dual M` over U, to `dualEval M U φ m`, which is φ(m). After
  rewriting with the previous lemma this holds by `rfl`: the ModuleCat braiding
  sends m ⊗ φ to φ ⊗ m, and `dualEval M U` is by definition
  `internalHomEval M 𝒪_X U`.
- `dualTensorEval_app_tensorSheafifyUnit`: the same formula on the image of m ⊗ φ
  under the sheafification unit `tensorSheafifyUnit M (dual M)`.
- `eq_dualTensorEval_iff`: `dualTensorEval M` is the unique sheaf map
  tensorObj M (dual M) ⟶ structureSheaf X whose sectionwise tensor adjoint sends every
  m ⊗ φ to `dualEval M U φ m`. The proof is the same extensionality argument as for
  `eq_internalHomTensorEval_iff`.

## Monoidal evaluation maps

The published monoidal structure on `X.Modules` is obtained by localization. Its
tensor `⊗` is identified with the explicit `tensorObj` by the fixed isomorphism
`localizedTensorIso X M N : M ⊗ N ≅ tensorObj M N`, and its unit `𝟙_ X.Modules` is
by construction the object `structureSheaf X`. The module defines

```
internalHomMonoidalEval M N := (localizedTensorIso X (internalHom M N) M).hom ≫ internalHomTensorEval M N
dualMonoidalEval M := (localizedTensorIso X M (dual M)).hom ≫ dualTensorEval M
```

and proves the comparisons between the chosen evaluation maps:

- `localizedTensorIso_inv_internalHomMonoidalEval`:
  `(localizedTensorIso X (internalHom M N) M).inv ≫ internalHomMonoidalEval M N =
  internalHomTensorEval M N`.
- `localizedTensorIso_inv_dualMonoidalEval`:
  `(localizedTensorIso X M (dual M)).inv ≫ dualMonoidalEval M = dualTensorEval M`.
  Both are `Iso.inv_hom_id_assoc`.
- `dualMonoidalEval_eq_braiding_comp`: `dualMonoidalEval M` equals the monoidal
  braiding `(β_ M (dual M)).hom` followed by `internalHomMonoidalEval M 𝒪_X`. The
  proof unfolds the three definitions, reassociates, and rewrites with the published
  `tensorMonoidalSymmetryComparison X M (dual M)`:

  ```
  (localizedTensorIso X M N).hom ≫ (tensorComm M N).hom =
    (β_ M N).hom ≫ (localizedTensorIso X N M).hom
  ```

  The two sides then agree up to reassociation and unfolding `dual M`.

So the explicit swap in `dualTensorEval` and the monoidal braiding in
`dualMonoidalEval_eq_braiding_comp` are compatible, and every map here is determined
by the sectionwise formula f ⊗ m ↦ f(m).

## Scope

The module only constructs the evaluation maps and identifies them. It does not
prove that they are isomorphisms locally or globally, for local rank one, or for
invertible modules. It also does not prove their naturality in M or N, a tensor and
internal-Hom adjunction, or compatibility of internal Hom with restriction. Those
belong to the parent task `45730c00-045d-4204-bf5f-1f49e61f733b` and its follow-up
tasks.

## Implementation notes

The file uses the same options as `ModuleDual`, namely
`backward.isDefEq.respectTransparency false` and
`backward.defeqAttrib.useBackward true`. It uses the default heartbeat limit.
