# Packaged residue-fibre ring and module systems

This module takes the actual fibre rings, maps and raw residue modules of
`Langlands.Algebra.LocalTowerResidueFiberRings` and packages them as values of
the existing structures `LocalAlgebraSystem` and `LocalModuleSystem`. Before
packaging, it proves that the fibre rings are local and that every fibre
structure map, transition and cocone is a local ring map. All declarations are
in `Langlands.Algebra`. The module imports `LocalTowerResidueFiberRings` and
Mathlib's `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`. It changes no
existing declaration.

## Provenance and scope

The motivating source is the Stacks Project, Lemma 10.128.8, tag **00R7**,
in the paragraph of its proof that introduces the fibre systems. The
registered source is `stacks-algebra-flatness-criteria-2026-10-22`, content
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`,
file `00R7.html` of that snapshot. No central errata file for this source was
present when checked. There the proof says that the system

```text
(S_λ / p_λ S_λ → S'_λ / p_λ S'_λ,  M_λ / p_λ M_λ)
```

"is a system as in Lemma 10.127.13 as well". It compares this system with the
fibres `S/mS → S'/mS'` and `M/mM` of the target. This module constructs that
data. It is an internal, derived packaging: the source neither states nor
proves it as a separate lemma, and the Lean API is ours. As in the imported
module, the quotient `S_λ / p_λ S_λ` is represented by the algebra-first tensor
`S_i ⊗[R_i] κ_i`. The quotient `M_λ / p_λ M_λ` is represented by the
residue-field-first tensor `κ_i ⊗[R_i] M_i`. The source's upper ring `S'` is
`T` here.

The source uses the fibre system in order to apply Lemma 10.128.3. That needs
colimit and localization properties of the system, and the proof concludes
flatness. This module asserts none of these. It states and proves no colimit
or colimit preservation, finite generation, essential finiteness, canonical
localization, base-change bijectivity, approximation or flatness property. It
adds no such hypothesis and no witness field. The packages are plain values of
the existing structures `LocalAlgebraSystem` and `LocalModuleSystem`; no new
bundled structure is introduced. The only facts proved here are locality,
the structure fields (diagram laws, commuting squares and semilinearity, all
taken from the imported module), and the equations identifying the packages
with the imported data.

## Notation

Fix a directed index preorder `ι`. Let
`D : LocalAlgebraTowerSystem ι R S T` be a synchronized local tower and
`E : LocalModuleTowerSystem D M` be a module tower with compatible ambient
`R`-, `S`- and `T`-actions on `M`. Write

| Symbol | Lean term |
| --- | --- |
| `κ_i` | `ResidueField (D.rs.base i)` |
| `κ` | `ResidueField R` |
| `F_i` | `D.rs.FiberRing i = D.rs.alg i ⊗[D.rs.base i] κ_i` |
| `G_i` | `D.UpperFiberRing i = D.top i ⊗[D.rs.base i] κ_i` |
| `N_i` | `E.rsModule.ResidueFiber i = κ_i ⊗[D.rs.base i] E.stModule.obj i` |
| `F` | `LocalAlgebraSystem.TargetFiberRing R S = S ⊗[R] κ` |
| `G` | `LocalAlgebraSystem.TargetFiberRing R T = T ⊗[R] κ` |
| `N` | `LocalModuleSystem.TargetResidueFiber R M = κ ⊗[R] M` |

The upper-ring constructions of the imported module install
`LocalAlgebraTowerSystem.composite_local R S T`. This is the proved locality of
`R → T` that follows from the scalar tower. The packages and their
projection equations are stated after the same `letI`, exactly as
`D.rt` and `E.rtModule` are.

## Generic locality of algebra-first fibres

In the namespace `ResidueFiberTensor`:

- `isLocalHom_of_comp_surjective π hπ g`: if `π : A →+* X` is surjective and
  `g.comp π` is local, then `g` is local.
- `isLocalRing_tensor R A` (instance): for a local map of local rings
  `R → A`, the fibre `A ⊗[R] ResidueField R` is a local ring. The proof
  transports Mathlib's instance for `ResidueField R ⊗[R] A` (from
  `Mathlib/RingTheory/LocalRing/ResidueField/Fiber.lean`) along
  `Algebra.TensorProduct.comm`, using `RingEquiv.isLocalRing`. Locality is
  therefore proved, not assumed.
- `includeLeft_surjective R A`: the algebra-first inclusion
  `A → A ⊗[R] ResidueField R` is surjective. This holds without locality of
  `A`, by `Algebra.TensorProduct.includeLeft_surjective` and surjectivity of
  the residue map.
- `includeLeft_isLocalHom R A` (instance): this inclusion is local, by
  `IsLocalHom.of_surjective`.
- `isLocalHom_of_tmul_one g φ hg`: a ring map
  `g : A ⊗[R] ResidueField R →+* Y` is local if `φ : A →+* Y` is local and
  `g (a ⊗ 1) = φ a` for all `a`. This is the previous two facts combined
  with `isLocalHom_of_comp_surjective`.
- `upperMap_isLocalHom R S T`: for a tower `R → S → T` with `T` local and
  `R → T`, `S → T` local, the published
  `upperMap R S (ResidueField R) T : S ⊗[R] κ →+* T ⊗[R] κ` is local.
  Its value on `s ⊗ 1` is `algebraMap S T s ⊗ 1`, which is the image of `s`
  under the local composite `T → T ⊗[R] κ` after `S → T`.
- `upperAlgebra_isLocalHom R S T` (scoped instance): the same fact for
  `algebraMap` of the scoped `upperAlgebra`.

## Locality of the actual fibre data

For `D : LocalAlgebraSystem ι R S`, in the namespace `LocalAlgebraSystem`:

| Declaration | Statement |
| --- | --- |
| `fiberRing_isLocalRing i` (instance) | `F_i` is local, from `D.structure_local i` |
| `fiberRingMap_isLocalHom h` (instance) | `D.fiberRingMap h : F_i → F_j` is local |
| `fiberRingι_isLocalHom i` (instance) | `D.fiberRingι i : F_i → F` is local |
| `targetFiberRing_isLocalRing` | `F = S ⊗[R] κ` is local |

The transition and cocone results apply `isLocalHom_of_tmul_one`. Their value
on `s ⊗ 1` is the image of `D.algMap i j h s` (respectively `D.algι i s`)
under the local inclusion into the next fibre. They use only the given
locality fields `algMap_local`, `algι_local` and `structure_local`.

For `D : LocalAlgebraTowerSystem ι R S T`, in the namespace
`LocalAlgebraTowerSystem`:

| Declaration | Statement |
| --- | --- |
| `compositeAlgebra_local i` | `D.rs.base i → D.top i` is local (composite of local maps) |
| `upperFiberRing_isLocalRing i` (instance) | `G_i` is local |
| `fiberHom_isLocalHom i` (instance) | `D.fiberHom i : F_i → G_i` is local |
| `targetFiberHom_isLocalHom` | `targetFiberHom : F → G` is local, given `R → T` local |
| `targetUpperFiberRing_isLocalRing` | `G = T ⊗[R] κ` is local, using `composite_local R S T` |
| `upperFiberRingMap_isLocalHom h` (instance) | `D.upperFiberRingMap h : G_i → G_j` is local |
| `upperFiberRingι_isLocalHom i` (instance) | `D.upperFiberRingι i : G_i → G` is local |

`fiberHom_isLocalHom` and `targetFiberHom_isLocalHom` are instances of
`upperMap_isLocalHom`, because the published `fiberHom` and `targetFiberHom`
are `upperMap`. The upper transition and cocone results are the
`LocalAlgebraSystem` results for `D.rt`, since the published
`upperFiberRingMap` and `upperFiberRingι` are `D.rt.fiberRingMap` and
`D.rt.fiberRingι`. `targetUpperFiberRing_isLocalRing` has the variable `S`
in its arguments, since locality of `R → T` is derived from `R → S → T`.

## The packaged fibre-ring diagram

`D.fiberSystem` is an `abbrev` of type

```lean
letI := composite_local R S T
LocalAlgebraSystem.{uI, max uB uA, max uC uA} ι
  (LocalAlgebraSystem.TargetFiberRing R S) (LocalAlgebraSystem.TargetFiberRing R T)
```

Its fields are exactly the following.

| Field | Value |
| --- | --- |
| `base`, `alg` | `D.rs.FiberRing`, `D.UpperFiberRing` |
| `componentAlgebra i` | `ResidueFiberTensor.upperAlgebra (D.rs.base i) (D.rs.alg i) κ_i (D.top i)` |
| `baseMap i j h`, `algMap i j h` | `D.rs.fiberRingMap h`, `D.upperFiberRingMap h` |
| `baseι i`, `algι i` | `D.rs.fiberRingι i`, `D.upperFiberRingι i` |
| `base_directed`, `alg_directed` | `D.rs.fiberRing_directed`, `D.upperFiberRing_directed` |
| `map_comm`, `ι_comm` | `D.fiberHom_map`, `D.fiberHom_ι` |
| locality fields | the results of the previous section |

The target algebra `F → G` is the instance found on
`TargetFiberRing R S` and `TargetFiberRing R T`. It is the scoped
`upperAlgebra R S κ T`, whose algebra map is `targetFiberHom`. The component
algebra map is therefore `D.fiberHom i`.

All projection equations hold by `rfl`. They are `fiberSystem_base`,
`fiberSystem_alg`, `fiberSystem_componentAlgebra`, `fiberSystem_algebraMap`
(`algebraMap` of the components is `D.fiberHom i`), `fiberSystem_baseMap`,
`fiberSystem_algMap`, `fiberSystem_baseι` and `fiberSystem_algι`.
`fiberSystem_targetAlgebraMap` states that `algebraMap F G` is
`targetFiberHom`.

## The packaged residue-module diagram

`E.fiberModuleSystem` is an `abbrev` of type

```lean
letI := LocalAlgebraTowerSystem.composite_local R S T
LocalModuleSystem.{uI, max uB uA, max uC uA, max uA uN} D.fiberSystem
  (LocalModuleSystem.TargetResidueFiber R M)
```

Its fields are:

| Field | Value |
| --- | --- |
| `obj i` | `N_i = E.rsModule.ResidueFiber i` |
| `objModule i` | the scoped raw action `ResidueFiberTensor.rawModule (D.rs.base i) (D.top i) κ_i (E.stModule.obj i)` of `G_i` on `N_i` |
| `map i j h` | `E.rtModule.residueFiberRingMap h`, semilinear over `D.upperFiberRingMap h` |
| `directed` | `E.rsModule.residueFiber_directed` |
| `ιM i` | `E.rtModule.residueFiberRingι i`, semilinear over `D.upperFiberRingι i` |
| `ιM_compat` | `E.rsModule.residueFiberι_compat` |

The `G`-module structure on `N` required by the type is the scoped raw action
`ResidueFiberTensor.rawModule R T κ M`. This uses the given compatible `R`-
and `T`-actions on `M`. The theorem `fiberModuleSystem_targetModule` records
this by `rfl`.

The upper semilinear maps come from `E.rtModule`. The published equations
`rtModule_residueFiberMap` and `rtModule_residueFiberι` hold by `rfl`. So the
underlying functions are exactly the lower raw maps
`E.rsModule.residueFiberMap h` and `E.rsModule.residueFiberι i`. The interface
equations are:

- `fiberModuleSystem_obj` and `fiberModuleSystem_objModule` identify the
  carrier and the stored action, the latter with the explicit `rawModule` term;
- `fiberModuleSystem_map` and `fiberModuleSystem_ιM` identify the packaged
  semilinear maps with `E.rtModule.residueFiberRingMap h` and
  `E.rtModule.residueFiberRingι i`;
- `fiberModuleSystem_map_apply` and `fiberModuleSystem_ιM_apply` state
  pointwise, by `rfl`, that the underlying functions are
  `E.rsModule.residueFiberMap h` and `E.rsModule.residueFiberι i`;
- `fiberModuleSystem_objBaseModule` states that restricting the packaged
  `G_i`-action along `D.fiberHom i` gives the lower raw action
  `ResidueFiberTensor.rawModule (D.rs.base i) (D.rs.alg i) κ_i (E.stModule.obj i)`.
  This restriction is the scoped `LocalModuleSystem.objBaseModule` of the
  package. The proof is `Module.ext'` together with the published
  `ResidueFiberTensor.upperMap_smul`. The two actions are equal but not
  syntactically identical.

Because the carriers and actions are definitionally those of the imported
module, the published comparisons stay usable with the packages. These are
`E.upperFiberModuleEquiv i`, which is linear over `D.fiberSystem.alg i`;
`E.lowerFiberModuleEquiv i`, after rewriting with
`fiberModuleSystem_objBaseModule`; the target comparisons; and the scalar
tower instance `E.fiberModuleScalarTower i` on
`(D.rs.FiberRing i, D.fiberSystem.alg i, E.fiberModuleSystem.obj i)`.

## Use and universes

Outside these namespaces, enable the scoped instances as needed:

```lean
open scoped TensorProduct
open scoped Langlands.Algebra.ResidueFiberTensor
open scoped Langlands.Algebra.LocalModuleSystem
open scoped Langlands.Algebra.LocalModuleTowerSystem
```

and state results about `D.fiberSystem` or `E.fiberModuleSystem` after
`letI := LocalAlgebraTowerSystem.composite_local R S T`.

The nine universes `uI`, `uA`, `uB`, `uC`, `uN`, `uR`, `uS`, `uT`, `uM` remain
independent. Declaration inspection of `fiberModuleSystem` lists all nine
level parameters. The fibre-ring carriers `F_i` and `G_i` inhabit
`max uB uA` and `max uC uA`. The residue modules `N_i` inhabit `max uA uN`.
The targets `F`, `G` and `N` inhabit `max uS uR`, `max uT uR` and `max uR uM`.
No ambient or component universes are identified.

## Proof methods

The locality results are proved as described above. They use Mathlib's fibre
instance, a tensor commutation, surjectivity of the algebra-first inclusion,
and the published `_tmul` formulas of the fibre maps. The package fields reuse
the published diagram laws, commuting squares and semilinear maps; no
law is reproved. The projection equations are definitional. Only
`fiberModuleSystem_objBaseModule` needs a short argument. No proof
placeholders or additional axioms are used.
