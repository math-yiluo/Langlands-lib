# Finiteness of the actual residue-fibre arrow and module

This module defines one proposition,
`Langlands.Algebra.ResidueFiberFinitenessStatement`. It is a statement only:
nothing in this module proves it, and no proof or witness is assumed.

## Statement

Let `R : Type u`, `S : Type v`, `T : Type w` and `M : Type z` be types in four
independent universes. The proposition quantifies over all of the following
data:

- commutative local rings `R`, `S` and `T`;
- algebras `R → S`, `S → T` and `R → T` with `IsScalarTower R S T`, so that
  `R → T` is the composite;
- local algebra maps `R → S` and `S → T` (`IsLocalHom`);
- an additive commutative group `M` with `R`-, `S`- and `T`-module
  structures, compatible through `IsScalarTower R S M`, `IsScalarTower S T M`
  and `IsScalarTower R T M`.

Put

```text
κ = ResidueField R,   F = S ⊗[R] κ,   G = T ⊗[R] κ,   N = κ ⊗[R] M.
```

In Lean, `F` and `G` are written `LocalAlgebraSystem.TargetFiberRing R S` and
`LocalAlgebraSystem.TargetFiberRing R T`, and `N` is written
`LocalModuleSystem.TargetResidueFiber R M`. These are the published aliases of
`Langlands.Algebra.LocalTowerResidueFiberRings` and
`Langlands.Algebra.LocalApproximationResidueFiber`; they unfold to the displayed
tensor products.

The statement says: if `EssFinitePresentation S T` and
`Module.FinitePresentation T M`, then both

```text
EssFinitePresentation F G   and   Module.FinitePresentation G N
```

hold, for the following scalar structures.

- `G` is an `F`-algebra through
  `ResidueFiberTensor.upperAlgebra R S κ T`, installed by `letI` in the
  proposition. Its algebra map is the actual arrow
  `ResidueFiberTensor.upperMap R S κ T`, induced by `S → T` and the identity
  of `κ`:

  ```text
  s ⊗ a ↦ algebraMap S T s ⊗ a.
  ```

  This is the published `targetFiberHom` of `LocalAlgebraTowerSystem`. It is
  not an arbitrary algebra structure on `G`.

- `N` is a `G`-module through `ResidueFiberTensor.rawModule R T κ M`, also
  installed by `letI`. This is the action transported from the left `G`-action
  on `G ⊗[T] M` along the published comparison. By the published lemma
  `ResidueFiberTensor.tmul_smul_tmul` it is determined by

  ```text
  (t ⊗ a) • (b ⊗ m) = (a * b) ⊗ (t • m).
  ```

  The `R`-action on `M` is the given one; it is not replaced.

A private development check confirmed that the proposition is definitionally
equal (`Iff.rfl`) to the same statement written with
`@EssFinitePresentation F G _ _ (ResidueFiberTensor.upperAlgebra R S κ T)` and
`@Module.FinitePresentation G N _ _ (ResidueFiberTensor.rawModule R T κ M)`.
So these two published instances are exactly the ones used.

The only hypotheses beyond the setting above are the two finiteness
assumptions. There is no assumption that `T` or `S` is essentially of finite
presentation over `R`, and none of Noetherianity, flatness, nonvanishing of
`M`, injectivity, finite generation over `R`, or any finiteness of the fibres
themselves. The proposition asserts the conclusion for every such tower and
module. It takes no canonical tensor equivalences, approximation systems or
other witnesses as data.

The four universe parameters `u`, `v`, `w`, `z` stay independent. The fibre
rings `F` and `G` and the module `N` live in the appropriate maxima of these
universes, and no universe is identified with another. Inspecting the complete
declaration reports exactly the level parameters `u`, `v`, `w`, `z` and a
`Prop`-valued result.

## Provenance

The motivating source is the Stacks Project, Lemma 10.128.8, tag **00R7**
(critère de platitude par fibres), and its proof. The registered source is
`stacks-algebra-flatness-criteria-2026-10-22`, content SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`, files
`00R7.html`, `00R3.html` (Section 10.128, containing Lemma 10.128.3, tag
**00R6**), `00QL.html` (Lemma 10.127.13, tag **00QX**) and `07DR.html`
(Definition 10.54.1, tag **00QM**). No errata file for this source was found
when checked on 2026-10-26.

In the proof of 00R7 the source applies Lemma 10.128.3 (00R6) a second time,
to the fibre system
`(S_λ/𝔭_λS_λ → S'_λ/𝔭_λS'_λ, M_λ/𝔭_λM_λ)`, after observing that it is a
system as in Lemma 10.127.13 (00QX). The source's upper ring `S'` is `T` here.
The setting of 00QX asks that the limit ring map be essentially of finite
presentation and the limit module be finitely presented. For the colimit
`S/𝔪S → S'/𝔪S'` with module `M/𝔪M`, the source therefore uses these two
finiteness facts without displaying them separately. This proposition isolates
that ambient finiteness obligation for the project's actual fibres.

The source writes the fibres as quotients `S/𝔪S`, `S'/𝔪S'` and `M/𝔪M`. As
in the published fibre module, the rings are written here in algebra-first
tensor order `S ⊗[R] κ` and `T ⊗[R] κ`, and the module in residue-field-first
order `κ ⊗[R] M`. No quotient-to-tensor comparison is constructed or assumed.
This proposition is a derived internal supporting statement; the source does
not state it as a separate lemma. In the source, `EssFinitePresentation S T`
follows from the hypotheses of 00R7 by cancellation; that derivation is the
separate published statement `EssFinitePresentationTowerCancellationStatement`
and is not a hypothesis here. The statement is not a flatness theorem and does
not assert that any fibre approximation data exist.

`EssFinitePresentation` is the published predicate of
`Langlands.Algebra.EssFinitePresentation` (Stacks 00QM: a localization of a
finitely presented algebra). `Module.FinitePresentation` is Mathlib's notion of
a finitely presented module.

## Expected proof route (not proved here)

The conclusions are expected to follow from two concrete canonical comparisons
along the actual actions.

1. An `F`-algebra equivalence `F ⊗[S] T ≃ₐ[F] G`, where `F` is an `S`-algebra
   by its left factor and `G` is an `F`-algebra through `upperMap`. Its
   forward formula is

   ```text
   (s ⊗ a) ⊗ t ↦ (algebraMap S T s * t) ⊗ a.
   ```

   With the generic base-change statement
   `EssFinitePresentationBaseChangeStatement` (Stacks Lemma 10.54.3, tag
   0AUF), applied to `S → T` and `S → F`, `EssFinitePresentation S T` gives
   `EssFinitePresentation F (F ⊗[S] T)`. Transport along this equivalence would
   then give `EssFinitePresentation F G`.

2. The `G`-linear equivalence `G ⊗[T] M ≃ₗ[G] N`. This is the already
   published `ResidueFiberTensor.linearComparison R T κ M`, also available as
   `LocalModuleTowerSystem.targetUpperFiberModuleEquiv`. It is given by
   `(t ⊗ a) ⊗ m ↦ a ⊗ (t • m)`, with inverse `a ⊗ m ↦ (1 ⊗ a) ⊗ m`.
   Finite presentation is stable under base change, so
   `Module.FinitePresentation T M` gives finite presentation of `G ⊗[T] M` over
   `G`. Transport along this equivalence would then give
   `Module.FinitePresentation G N`.

None of this is proved by this module. In particular the comparison in item 1
is not constructed here. The finiteness implications are also not proved here,
and the base-change statement is not proved by this module. The proposition is
stated so that a proof successor can establish these facts.
