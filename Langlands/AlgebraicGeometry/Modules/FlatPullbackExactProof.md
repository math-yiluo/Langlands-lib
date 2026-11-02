# Pullback of scheme modules along a flat morphism is exact: proof

This proof module imports the published statement
`Langlands.AlgebraicGeometry.Modules.FlatPullbackExactStatement` and changes neither it nor
anything it imports. Its closing theorem is
`Langlands.AlgebraicGeometry.Modules.flatPullbackExact.{u}`, whose complete type is
`Langlands.AlgebraicGeometry.Modules.FlatPullbackExactStatement.{u}`. That type has the
statement's single universe `u` and no further outer parameters or hypotheses. The final
`example` checks this complete type with the unapplied constant `@flatPullbackExact.{u}`.

Unfolded, the theorem says: for all schemes `X Y : Scheme.{u}` and every morphism
`f : X ⟶ Y` with `Flat f`, the functor
`Scheme.Modules.pullback f : Y.Modules ⥤ X.Modules` preserves finite limits. The modules
range over the full categories `X.Modules` and `Y.Modules` of sheaves of modules. The proof
adds no quasi-coherence, finiteness, local-freeness or affineness hypothesis on the modules
or the schemes.

## Declarations

- `Langlands.AlgebraicGeometry.Modules.pullback_map_mono_of_flat` (helper). For schemes
  `X Y : Scheme.{u}`, a morphism `f : X ⟶ Y` with an instance `[Flat f]`, and a
  monomorphism `φ : M ⟶ N` in `Y.Modules` (instance `[Mono φ]`), it concludes
  `Mono ((Scheme.Modules.pullback f).map φ)` in `X.Modules`.
- `Langlands.AlgebraicGeometry.Modules.flatPullbackExact`, the closing theorem described
  above.

## Implemented proof

**Monomorphisms (`pullback_map_mono_of_flat`).** Monomorphisms of scheme modules are tested
on stalks, using two published lemmas of
`Langlands.AlgebraicGeometry.Picard.LineBundleFiniteMonoDetector`:

- `Langlands.SchemeModule.mono_of_stalk_injective`: a morphism of scheme modules is a
  monomorphism if every stalk map of its underlying presheaf map of abelian groups is
  injective.
- `Langlands.SchemeModule.stalk_injective_of_mono`: every stalk map of a monomorphism of
  scheme modules is injective.

The proof applies the first lemma to `(Scheme.Modules.pullback f).map φ`. Fix `x : X`.

1. By `stalk_injective_of_mono φ (f x)` and `ModuleCat.mono_iff_injective`, the stalk map
   `(stalkFunctor (f x)).map φ` is a monomorphism of `𝒪_{Y, f x}`-modules. Here
   `stalkFunctor` is the Library's module stalk functor
   (`Langlands.AlgebraicGeometry.Modules.StalkAdjunction`). Its maps are those stalk maps
   of underlying abelian groups, made linear over the local ring.
2. Mathlib's `Flat.stalkMap f x` says that the ring map `(f.stalkMap x).hom` from
   `𝒪_{Y, f x}` to `𝒪_{X, x}` is flat. Then Mathlib's
   `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` shows that extension of scalars
   `ModuleCat.extendScalars (f.stalkMap x).hom` preserves finite limits. Hence it
   preserves monomorphisms, by Mathlib's instance
   `preservesMonomorphisms_of_preservesLimitsOfShape`.
3. The published natural isomorphism
   `Langlands.AlgebraicGeometry.Modules.StalkPullback.pullbackStalkIso f x` identifies
   `Scheme.Modules.pullback f ⋙ stalkFunctor x` with
   `stalkFunctor (f x) ⋙ ModuleCat.extendScalars (f.stalkMap x).hom`. Mathlib's
   `NatIso.naturality_2` writes the stalk at `x` of `(Scheme.Modules.pullback f).map φ` as
   the composite of an isomorphism, the extension of scalars of
   `(stalkFunctor (f x)).map φ`, and another isomorphism. By steps 1 and 2 this composite is
   a monomorphism.
4. `ModuleCat.mono_iff_injective` turns this monomorphism back into injectivity of the
   underlying function. That function is, by definition, the stalk map at `x` of the
   underlying abelian-group presheaf map, which is what `mono_of_stalk_injective` needs.

**Finite limits (`flatPullbackExact`).** After introducing `X`, `Y`, `f` and the flatness
hypothesis, the proof records that `Scheme.Modules.pullback f` preserves monomorphisms, by
the helper. The categories `X.Modules` and `Y.Modules` are abelian and the pullback functor
is additive (Mathlib instances in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`). For such
functors Mathlib's `Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` (in
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`) reduces the goal to the following.
For every short exact sequence `S` in `Y.Modules`, the image sequence `S.map` under the
pullback is exact and the image of `S.f` is a monomorphism.

- Exactness of the image sequence: the pullback is a left adjoint, so instance search finds
  `PreservesFiniteColimits (Scheme.Modules.pullback f)` for every `f`. Mathlib's
  `Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi` turns this into exactness of
  the image of every short exact sequence (its first component is used).
- The image of `S.f` is a monomorphism: `S.f` is a monomorphism because `S` is short exact
  (`hS.mono_f`), and the pullback preserves monomorphisms.

The file sets `backward.isDefEq.respectTransparency false`, as do the imported Library
modules `StalkPullback` and `LineBundleFiniteMonoDetector`. The proof uses only the axioms
`propext`, `Classical.choice` and `Quot.sound`. It uses no `sorry`, no native computation
and no raised heartbeat limit.

Not claimed: the module proves only this preservation of finite limits. It does not prove
the converse discussed in the comments on tag 02N4 (that exactness of pullback implies
flatness), the statement for general ringed spaces or ringed topoi, or any base-change
theorem.

## Imports

- `Langlands.AlgebraicGeometry.Modules.FlatPullbackExactStatement`: the target.
- `Langlands.AlgebraicGeometry.Modules.StalkPullback`: `pullbackStalkIso` and, through
  `StalkAdjunction`, the module stalk functor `stalkFunctor`.
- `Langlands.AlgebraicGeometry.Picard.LineBundleFiniteMonoDetector`: the two stalk tests
  for monomorphisms. Its import closure has nine Library modules. None of them is the flat
  higher-direct-image base-change statement, a Mumford Euler statement, or downstream of
  them.
- `Mathlib.Algebra.Category.ModuleCat.Descent`: flat extension of scalars preserves finite
  limits.
- `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`: the two exactness criteria.

All Library results used are published with proofs. No published statement is assumed as
data.

## Provenance

The original is the Stacks Project Authors, *The Stacks Project*, Sheaves of Modules,
Lemma 17.20.2 ([tag 02N4](https://stacks.math.columbia.edu/tag/02N4), label
`lemma-pullback-flat`): pullback along a flat morphism of ringed spaces is exact. The
published statement's Markdown explains why preservation of finite limits is the remaining
part of exactness and how the lemma specializes to schemes. The registered sources are
`stacks-closed-immersion-exactness-a04446e5` (`modules.tex`, lines 3190–3209, at Stacks
commit `a04446e57ec1fbc252a871afcec7752fb2807b14`) and
`stacks-flat-pullback-exactness-2026-11-02` (tag pages 02N4, 02N3, 01AJ, 0034 and 010N).

The source proof writes `f^*` as the exact inverse image `f^{-1}` followed by
`- ⊗_{f^{-1}𝒪_Y} 𝒪_X`, which is exact because `𝒪_X` is a flat `f^{-1}𝒪_Y`-module. The
Lean proof takes a different, stalkwise route. Right exactness of `f^*` is already
available, so only preservation of monomorphisms is needed. That is checked on stalks,
where the stalk of `f^*` at `x` is extension of scalars along the flat local ring map
`𝒪_{Y, f x} → 𝒪_{X, x}`. Both routes use the same input, flatness of the stalk maps
(Stacks, Definition 17.20.1, tag 02N3).

The proof relies on pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`,
specifically `AlgebraicGeometry.Flat.stalkMap` (`Mathlib.AlgebraicGeometry.Morphisms.Flat`),
`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`
(`Mathlib.Algebra.Category.ModuleCat.Descent`), `ModuleCat.mono_iff_injective`
(`Mathlib.Algebra.Category.ModuleCat.EpiMono`), `CategoryTheory.NatIso.naturality_2`, and
`Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono` and
`Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi`
(`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`).

Worker 228 wrote the published statement, this Lean proof and this explanation. Worker 1098
published the proof task for the parent flat base-change task of Workers 360 and 1098.
