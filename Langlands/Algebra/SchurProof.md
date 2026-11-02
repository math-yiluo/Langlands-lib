# Renard B.II: proof of Schur's lemma, unital core

`Langlands/Algebra/SchurProof.lean` proves the published aggregate proposition
`Langlands.Renard.SchurTheoremStatement A M` from `Langlands.Algebra.SchurStatements`.
It also proves each of the eight component propositions of that file under its own
name. The main theorem is

```lean
theorem Langlands.Renard.schurTheorem (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurTheoremStatement A M
```

Every theorem keeps the complete parameter list of its target proposition, in the same
order. The algebra universe `u` and the module universe `v` stay independent. The two
ring-level theorems assume only `[Ring A]` and an ordinary unital `A`-module `M`. The
complex theorems assume a unital complex algebra `A`, which need not be commutative,
and a module `M` whose complex structure is compatible with that of `A` through
`IsScalarTower ℂ A M`. In `schurModuleRankCountable` this compatibility is a premise
inside the proposition, as in the statement. Simplicity is always Mathlib's
`IsSimpleModule A M`, and it remains a premise. "Dimension at most countable" is
`Module.rank ℂ _ ≤ Cardinal.aleph0`. No finite dimension is assumed anywhere.
Scalarity is bijectivity of the actual map `algebraMap ℂ (Module.End A M)`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`
(SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`): B.II
"Lemme de Schur", printed page 272 / PDF page 278. It uses the Théorème d'Amitsur of
B.I, printed pages 271–272 / PDF pages 277–278. The 2010-edition *corrections et
compléments* (`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, PDF pages 18–19)
add that `M` is a complex vector space, and that one may pass to a unital algebra and
a unital module. The 2026 text already says both. The statements formalized here are
the resulting unital core, so the proof starts after that reduction.

## The proof route

The Lean proof follows the source.

1. A nonzero endomorphism `f` of the simple module `M` has kernel `0` and image `M`,
   so it is bijective. A bijective endomorphism is a unit of `Module.End A M`, so
   `Module.End A M` is a division ring.
2. For `m ≠ 0`, the submodule `A • m` is nonzero, so it is all of `M`. Thus the
   action map `a ↦ a • m` from `A` to `M` is surjective.
3. An endomorphism `f` with `f m = 0` is not injective, so it is zero by step 1. Hence
   the evaluation map `f ↦ f m` is injective. The source argues instead that
   `f (a • m) = a • f m` and `A • m = M`, so `f m` determines `f`. Both arguments
   give the same injectivity.
4. Rank transfer from `A` to `M`: a surjective complex-linear map cannot increase
   rank, so the map of step 2 gives `Module.rank ℂ M ≤ Module.rank ℂ A`.
5. Rank transfer from `M` to `Module.End A M`: an injective complex-linear map cannot
   decrease rank, so the map of step 3 gives
   `Module.rank ℂ (Module.End A M) ≤ Module.rank ℂ M`.
6. If `M` has at most countable dimension, step 5 shows that the division algebra
   `Module.End A M` has at most countable dimension. Amitsur's theorem then says that
   its canonical scalar map is bijective. If `A` has at most countable dimension, step 4
   reduces to the previous case.

## The canonical scalar map

Because of `IsScalarTower ℂ A M`, complex scalars commute with the action of `A` on
`M`. Mathlib therefore makes `Module.End A M` a complex algebra
(`Module.End.instAlgebra`). Its complex vector-space structure is the pointwise one,
`(z • f) m = z • f m`, and its scalar map sends `z` to multiplication by `z`:
`algebraMap ℂ (Module.End A M) z m = z • m` (`Module.algebraMap_end_apply`). The
published lemma `bijective_algebraMap_end_iff` in the statement file shows that
bijectivity of this map says exactly this: every `A`-linear endomorphism is
multiplication by a unique complex number. The same complex structure is used both in
the rank bound of step 5 and in the application of Amitsur's theorem. The two Lean
instances agree definitionally, so no transport is needed.

## Declarations

All declarations are theorems in namespace `Langlands.Renard`.

### `schurEndBijective`

```lean
theorem schurEndBijective (A : Type u) [Ring A] (M : Type v) [AddCommGroup M]
    [Module A M] : SchurEndBijectiveStatement A M
```

The first step of the proof, over an arbitrary ring. Given `IsSimpleModule A M` and
`f ≠ 0`, Mathlib's `LinearMap.bijective_of_ne_zero` gives bijectivity. That lemma is
proved by the source's argument: kernel and range of `f` are submodules, so each is
`⊥` or `⊤`.

### `schurEndDivision`

```lean
theorem schurEndDivision (A : Type u) [Ring A] (M : Type v) [AddCommGroup M]
    [Module A M] : SchurEndDivisionStatement A M
```

B.II a), over an arbitrary ring. A simple module is nontrivial
(`IsSimpleModule.nontrivial`), so `Module.End A M` is nontrivial
(`Module.End.instNontrivial`). A nonzero `f` is bijective by `schurEndBijective`, and a
bijective endomorphism is a unit (`Module.End.isUnit_iff`).

### `schurCyclicMapSurjective`

```lean
theorem schurCyclicMapSurjective (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurCyclicMapSurjectiveStatement A M
```

Step 2. The map in the statement is
`(LinearMap.toSpanSingleton A M m).restrictScalars ℂ`. Restricting scalars does not
change the underlying function, so surjectivity is Mathlib's
`IsSimpleModule.toSpanSingleton_surjective`. That lemma rests on
`IsSimpleModule.span_singleton_eq_top`: the span of a nonzero vector is not `⊥`, so it
is `⊤`.

### `schurEvaluationInjective`

```lean
theorem schurEvaluationInjective (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurEvaluationInjectiveStatement A M
```

Step 3, for the map `LinearMap.applyₗ' ℂ m : Module.End A M →ₗ[ℂ] M`. Since it is
additive, it suffices that `f m = 0` forces `f = 0` (`injective_iff_map_eq_zero`). If
`f ≠ 0`, then `f` is injective (`LinearMap.injective_of_ne_zero`), and `f m = 0 = f 0`
gives `m = 0`, contradicting `m ≠ 0`.

### `schurModuleRankCountable`

```lean
theorem schurModuleRankCountable (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] : SchurModuleRankCountableStatement A M
```

The rank transfer of step 4. After introducing the premises `IsScalarTower ℂ A M`,
`IsSimpleModule A M` and `Module.rank ℂ A ≤ ℵ₀`, the proof chooses `m ≠ 0`, which
exists because `M` is nontrivial. The surjective map of `schurCyclicMapSurjective`
then gives, by `LinearMap.lift_rank_le_of_surjective`,

```lean
Cardinal.lift.{u} (Module.rank ℂ M) ≤ Cardinal.lift.{v} (Module.rank ℂ A)
```

`A` and `M` live in different universes, so the two ranks are compared after lifting
both to a common universe. `Cardinal.lift_le_aleph0` says that lifting preserves and
reflects the bound `≤ ℵ₀`. It moves the hypothesis on `A` up to the common universe and
the resulting bound on `M` back down.

### `schurEndRankCountable`

```lean
theorem schurEndRankCountable (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurEndRankCountableStatement A M
```

The rank transfer of step 5. With `m ≠ 0`, the injective map of
`schurEvaluationInjective` gives
`Module.rank ℂ (Module.End A M) ≤ Module.rank ℂ M` by `LinearMap.rank_le_of_injective`.
Both carriers are in universe `v`, so no lift is needed. The bound `≤ ℵ₀` follows by
transitivity.

### `schurScalarOfModuleRankCountable`

```lean
theorem schurScalarOfModuleRankCountable (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v)
    [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurScalarOfModuleRankCountableStatement A M
```

B.II b). Assume simplicity and `Module.rank ℂ M ≤ ℵ₀`. With classical decidable
equality, Mathlib's instance `Module.End.instDivisionRing` makes `Module.End A M` a
division ring. This is the division-ring form of `schurEndDivision`, built on the same
ring structure. The published B.I theorem

```lean
theorem Langlands.Renard.amitsurDivisionAlgebra (D : Type u) [DivisionRing D]
    [Algebra ℂ D] : AmitsurDivisionAlgebraStatement D
```

from `Langlands.Algebra.AmitsurProof` is applied to `D = Module.End A M`, at universe
`v`, with the complex algebra structure described above. Its hypothesis
`Module.rank ℂ (Module.End A M) ≤ ℵ₀` is `schurEndRankCountable`. Its conclusion is
bijectivity of `algebraMap ℂ (Module.End A M)`. Choosing a decidable-equality
instance affects only the auxiliary division-ring structure. It does not appear in
the proposition.

### `schurScalarOfAlgebraRankCountable`

```lean
theorem schurScalarOfAlgebraRankCountable (A : Type u) [Ring A] [Algebra ℂ A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] :
    SchurScalarOfAlgebraRankCountableStatement A M
```

The final sentence of B.II b). From `Module.rank ℂ A ≤ ℵ₀`,
`schurModuleRankCountable` gives `Module.rank ℂ M ≤ ℵ₀`, with the ambient instance
`IsScalarTower ℂ A M` supplied as its premise. Then
`schurScalarOfModuleRankCountable` applies.

### `schurTheorem`

```lean
theorem schurTheorem (A : Type u) [Ring A] [Algebra ℂ A] (M : Type v) [AddCommGroup M]
    [Module A M] [Module ℂ M] [IsScalarTower ℂ A M] : SchurTheoremStatement A M
```

The aggregate is the triple `⟨schurEndDivision A M, schurScalarOfModuleRankCountable A M,
schurScalarOfAlgebraRankCountable A M⟩`. It covers division and both scalarity
alternatives.

## Scope

This module proves the unital core stated in `Langlands.Algebra.SchurStatements`. It
does not prove the source's reduction from a nonunital algebra and module to the
unitization `Ã = A ⊕ ℂ1_A`. It also does not prove the original nonunital-action
statements of `Langlands.Algebra.NonUnitalSchurStatements`. Those are separate
obligations.

## Provenance and credit

Worker 972 wrote this module and this note. The route is the source's own proof,
combined with Mathlib's simple-module lemmas and the published B.I proof
`amitsurDivisionAlgebra`, which Worker 972 also wrote for task
`f7c4f5a9-27df-440c-b35f-885a29760bf7`. No code was taken from other Schur proofs in
the Library.

## Checks

In Lean environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` the module compiles with no
errors or warnings. A separate check assigned each of the nine unapplied constants
(`@schurEndDivision.{u, v}`, …, `@schurTheorem.{u, v}`) to the complete telescope of
its target proposition, and all nine assignments compiled. The axioms of
`schurTheorem` and of each component theorem are `propext`, `Classical.choice` and
`Quot.sound`.
