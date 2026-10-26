# Residue-fibre rings and module comparisons

This module constructs actual tensor rings, their induced maps, and linear
comparisons with the raw residue modules of `LocalApproximationResidueFiber`.
It uses the synchronized ring and module towers of `LocalAlgebraTowerSystem`.
All declarations are in `Langlands.Algebra`.

## Provenance and scope

The motivating source is the Stacks Project, Lemma 10.128.8, tag **00R7**,
especially the fibre-system paragraphs of its proof, and Lemma 10.127.13,
tag **00QX**, in Section 10.127, tag **00QL**. The registered source is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`;
the exact files are `00R7.html` and `00QL.html` in that snapshot. No central
errata file for this source was present when checked.

The source writes the fibres as quotients by the maximal ideal of the base:
`S_i / p_i S_i`, `T_i / p_i T_i`, and `M_i / p_i M_i` (its upper ring is
written `S'_i`). Here the rings are presented in algebra-first tensor order,
and the raw modules in residue-field-first tensor order. These definitions and
elementary tensor identities are internal constructions supporting that proof;
the source does not state this Lean API. This module does not construct
quotient-to-tensor comparisons or assert the source's approximation conclusions.
In particular it proves no locality of the fibre rings, colimit preservation,
finite generation, localization property, 00QX compatibility, approximation
existence, or flatness. It adds no such hypotheses or desired-conclusion fields.

## Generic comparison and scalar structures

The namespace `ResidueFiberTensor` works for commutative rings `R`, `S`, and
`K`, algebras `R → S` and `R → K`, and an additive commutative group `M`
with compatible `R`- and `S`-module structures. Here `K` need not be a field.
Its definition `comparison R S K M` is the `R`-linear equivalence

```text
(S ⊗[R] K) ⊗[S] M  ≃ₗ[R]  K ⊗[R] M.
```

The implementation first commutes the outer tensor factors, applies Mathlib's
`TensorProduct.AlgebraTensorModule.cancelBaseChange R S S M K`, and then
commutes the remaining factors. The first two equivalences are restricted to
`R` scalars. The computation lemmas `comparison_tmul` and
`comparison_symm_tmul` give the precise directions:

```text
(s ⊗ a) ⊗ m  ↦  a ⊗ (s • m),
a ⊗ m        ↦  (1 ⊗ a) ⊗ m.
```

The scoped instance `rawModule` transports the existing left
`S ⊗[R] K`-module structure on the source to the raw tensor on the right,
using the inverse additive equivalence. The definition `linearComparison`
is the same concrete equivalence, now linear over `S ⊗[R] K`.
`linearComparison_tmul` and `linearComparison_symm_tmul` give the same
formulas. This transported action is determined explicitly by
`tmul_smul_tmul`:

```text
(s ⊗ a) • (b ⊗ m) = (a * b) ⊗ (s • m).
```

`rawBaseTower` proves compatibility with the pre-existing `R`-action.
`includeRight_smul` states `(1 ⊗ a) • x = a • x`, where the right side is
the pre-existing left-factor `K`-action. `rawFieldTower` expresses this as
`IsScalarTower K (S ⊗[R] K) (K ⊗[R] M)` after installing Mathlib's
`Algebra.TensorProduct.rightAlgebra`. This is a theorem with an explicit
local instance in its result, not a global replacement of the default
left-factor algebra structure.

For a further commutative algebra `T` in a compatible tower `R → S → T`,
`upperMap R S K T` is the ring homomorphism induced by `S → T` and the
identity on `K`. Its formula `upperMap_tmul` is
`s ⊗ a ↦ algebraMap S T s ⊗ a`. The scoped `upperAlgebra` equips
`T ⊗[R] K` with this actual `S ⊗[R] K`-algebra structure;
`upperAlgebra_algebraMap` identifies its algebra map and `upperBaseTower`
proves compatibility with `R`. If `M` also has a compatible `T`-action,
`upperMap_smul` proves

```text
upperMap R S K T f • x = f • x.
```

Thus `upperRawTower` supplies
`IsScalarTower (S ⊗[R] K) (T ⊗[R] K) (K ⊗[R] M)` for the two concrete
transported actions. This also supplies the target fibre scalar tower by
taking `K = ResidueField R`.

## Fibre-ring diagrams

For `D : LocalAlgebraSystem ι R S`, put `R_i = D.base i`, `S_i = D.alg i`,
`κ_i = ResidueField R_i`, and `κ = ResidueField R`. The namespace
`LocalAlgebraSystem` supplies:

| Declaration | Concrete object or map |
| --- | --- |
| `D.FiberRing i` | `F_i = S_i ⊗[R_i] κ_i` |
| `TargetFiberRing R S` | `F = S ⊗[R] κ` |
| `D.fiberRingMap h` | `F_i →+* F_j`, for `h : i ≤ j` |
| `D.fiberRingι i` | `F_i →+* F` |

Both maps are `Algebra.TensorProduct.mapRingHom` constructions using the
published `D.residueMap h` and `D.residueι i`. Their `_tmul` lemmas state

```text
s ⊗ a ↦ D.algMap i j h s ⊗ D.residueMap h a,
s ⊗ a ↦ D.algι i s ⊗ D.residueι i a.
```

`fiberRingMap_self`, `fiberRingMap_comp`, and `fiberRingι_compat` prove
identity, composition, and cocone compatibility pointwise. The instance
`fiberRing_directed` bundles the first two laws as a `DirectedSystem`.

For `D : LocalAlgebraTowerSystem ι R S T`, the lower objects are those of
`D.rs`, and `D.UpperFiberRing i` is `G_i = D.top i ⊗[D.rs.base i] κ_i`.
The upper target is `LocalAlgebraSystem.TargetFiberRing R T`, denoted `G`.
`D.fiberHom i : F_i →+* G_i` and `targetFiberHom : F →+* G` specialize
`upperMap`. Their `_tmul` lemmas send `s ⊗ a` to the image of `s` in the
upper ring tensored with the same `a`.

`upperFiberRingMap` and `upperFiberRingι` reuse the `D.rt` constructions,
locally installing the already proved `composite_local R S T`. Their
`_tmul` equations use `D.topMap` or `D.topι` on the first factor and the
exact `D.rs` residue map on the second. The corresponding `_self`, `_comp`,
and `_compat` lemmas and `upperFiberRing_directed` give the upper diagram
laws. The two pointwise commuting-square laws are

```text
D.upperFiberRingMap h (D.fiberHom i x)
  = D.fiberHom j (D.rs.fiberRingMap h x),
D.upperFiberRingι i (D.fiberHom i x)
  = targetFiberHom (D.rs.fiberRingι i x).
```

Their names are `fiberHom_map` and `fiberHom_ι`. No maps are independently
chosen and no naturality condition is assumed.

## Module diagrams and naturality

For `E : LocalModuleSystem D M`, `E.FiberModule i` denotes
`D.FiberRing i ⊗[D.alg i] E.obj i`. Its comparison `E.fiberModuleEquiv i`
is fibre-ring linear with codomain the published `E.ResidueFiber i`.
`fiberModuleEquiv_tmul` and `fiberModuleEquiv_symm_tmul` are precisely the
forward and inverse formulas above, with the component scalars.
`TargetFiberModule R S M` and `targetFiberModuleEquiv` provide the target
construction. The target `_tmul` and `_symm_tmul` lemmas use the given
compatible `R`- and `S`-actions on `M`.

`residueFiberMap_smul` and `residueFiberι_smul` prove that the existing raw
maps are semilinear for the full fibre-ring maps. `residueFiberRingMap`
and `residueFiberRingι` package this stronger semilinearity; their `_apply`
lemmas identify their underlying functions definitionally with the published
`residueFiberMap` and `residueFiberι`. The scalar-extended transitions
`fiberModuleMap` and cocones `fiberModuleι` are conjugates of those actual
maps by the comparisons. Their pure-tensor formulas are

```text
fiberModuleMap h (f ⊗ m) = D.fiberRingMap h f ⊗ E.map i j h m,
fiberModuleι i (f ⊗ m) = D.fiberRingι i f ⊗ E.ιM i m.
```

`fiberModuleMap_self`, `fiberModuleMap_comp`, `fiberModuleι_compat`, and
`fiberModule_directed` give the diagram laws. The naturality equations,
for every tensor `x`, are

```text
E.fiberModuleEquiv j (E.fiberModuleMap h x)
  = E.residueFiberMap h (E.fiberModuleEquiv i x),
targetFiberModuleEquiv (E.fiberModuleι i x)
  = E.residueFiberι i (E.fiberModuleEquiv i x).
```

These are `fiberModuleEquiv_map` and `targetFiberModuleEquiv_ι`.

For a module tower `E : LocalModuleTowerSystem D M`, write
`M_i = E.stModule.obj i`. In `LocalModuleTowerSystem`, `objMiddleModule`
restricts the actual `T_i`-action along `S_i → T_i`, and `objBaseModule`
restricts it along `R_i → T_i`. The scoped laws `objMiddleTopTower`,
`objBaseTopTower`, and `objBaseMiddleTower` show compatibility. `E.rsModule`
uses the same module carriers, transitions, and cocone, with these restricted
middle actions. It does not introduce new module-map data.

The four requested comparisons are:

| Name in `LocalModuleTowerSystem` | Direction and linearity |
| --- | --- |
| `E.lowerFiberModuleEquiv i` | `F_i ⊗[S_i] M_i ≃ₗ[F_i] κ_i ⊗[R_i] M_i` |
| `E.upperFiberModuleEquiv i` | `G_i ⊗[T_i] M_i ≃ₗ[G_i] κ_i ⊗[R_i] M_i` |
| `targetLowerFiberModuleEquiv` | `F ⊗[S] M ≃ₗ[F] κ ⊗[R] M` |
| `targetUpperFiberModuleEquiv` | `G ⊗[T] M ≃ₗ[G] κ ⊗[R] M` |

The component comparisons have explicit `_tmul` and `_symm_tmul` lemmas.
In the upper case these send `(t ⊗ a) ⊗ m` to `a ⊗ (t • m)`, and
`a ⊗ m` back to `(1 ⊗ a) ⊗ m`. Both component codomains are exactly
`E.rsModule.ResidueFiber i`. The instance `fiberModuleScalarTower` proves
compatibility of their `F_i`- and `G_i`-actions along `D.fiberHom i`.

For lower naturality use the generic module equations on `E.rsModule`.
For upper naturality use them on `E.rtModule` after installing
`LocalAlgebraTowerSystem.composite_local R S T`.
`rtModule_residueFiberMap` and `rtModule_residueFiberι` explicitly identify
the upper raw maps with the lower raw maps on this common carrier.
`upperFiberModuleEquiv_map` and `targetUpperFiberModuleEquiv_ι` state the
upper naturality squares directly against `E.rsModule`'s raw maps.
The two target aliases are the generic `targetFiberModuleEquiv` specialized
to `(R,S,M)` and `(R,T,M)` respectively. Thus their computation lemmas are
`LocalModuleSystem.targetFiberModuleEquiv_tmul` and
`LocalModuleSystem.targetFiberModuleEquiv_symm_tmul` with those substitutions;
these aliases do not take `D` or `E` as arguments.

## Use, universes, and elementary proof methods

For use outside these namespaces, enable the scoped instances as needed:

```lean
open scoped TensorProduct
open scoped Langlands.Algebra.LocalModuleSystem
open scoped Langlands.Algebra.ResidueFiberTensor
open scoped Langlands.Algebra.LocalModuleTowerSystem
```

The target actions are given compatible actions, as in the raw residue API.
Restricting a `T`-action along the specified algebra maps provides these
structures; the module comparisons do not replace an existing compatible
`R`-action. Lower tower comparisons require a compatible target `S`-action
because `rsModule` includes its cocone. Upper comparisons use that same raw
carrier. Target comparison aliases themselves only need the structures
appearing in their respective `(R,S,M)` or `(R,T,M)` tensor construction.

The index universe `uI`, component universes `uA`, `uB`, `uC`, `uN`, and
target universes `uR`, `uS`, `uT`, `uM` remain independent. Full declaration
inspection shows all nine parameters on both component tower comparisons.
Each target comparison has three independent universes; the lower and upper
ones do not identify the universes of `S` and `T`. Tensor carriers inhabit
the appropriate maxima without lifting all objects to a common universe.

The comparison formulas follow by reduction of the Mathlib equivalences.
The transported action formula is proved by multiplication of pure tensors.
Ring laws and commuting squares use tensor induction and the published
ring/residue diagram laws. Semilinearity uses tensor induction on both the
scalar and module tensors. The scalar-extended module formulas and diagram
laws follow by the injectivity of the comparison and the existing raw laws.
The scalar-tower results use the explicit algebra-map action identities.
Every elementary law is proved; no additional axioms or proof placeholders
are introduced.
