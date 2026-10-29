# Bijectivity of the canonical map `A_K ⊗[K] L → A_L`: statement target

This module imports only `Langlands.Global.AdelicFunctoriality.FiniteAdeleTensorMap`.
It defines one proposition in the namespace
`Langlands.Global.AdelicFunctoriality`:

```lean
def FiniteAdeleTensorMapBijective : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L], Function.Bijective (finiteAdeleTensorMap K L)
```

The module proves nothing. It defines no map, algebra equivalence or instance,
and it does not change the published map or anything that map imports.

## Quantifiers, instances and universes

The proposition has two universe parameters, `u` and `v`. They are
independent, so `K` and `L` may live in different universes. Inside the
proposition the data are quantified in this order:

1. a type `K : Type u` and a type `L : Type v`;
2. the instance hypotheses `[Field K] [Field L] [NumberField K] [NumberField L]
   [Algebra K L]`.

These are exactly the five assumptions of the published map
`finiteAdeleTensorMap`. There is no other premise. In particular, the
proposition does not assume finite-dimensionality of `L` over `K` (for number
fields Mathlib's instances already supply it), a coefficient `K`-algebra on
`A_L`, a scalar tower, an adelic algebra structure or a coherence class such as
Imperial's `ComapFiberwiseSMul`, a local or integral comparison, a chosen
equivalence, or any injectivity, surjectivity or bijectivity hypothesis.

## Source, target and map

Write `A_K = IsDedekindDomain.FiniteAdeleRing (𝓞 K) K` and
`A_L = IsDedekindDomain.FiniteAdeleRing (𝓞 L) L`. The proposition is about the
published map

```lean
finiteAdeleTensorMap K L : A_K ⊗[K] L →ₐ[A_K] A_L
```

used by its Lean name, with no change to its definition.

- **Source.** `A_K ⊗[K] L`, with `A_K` as the left factor. `K` acts on `A_K`
  through Mathlib's `Algebra K A_K` (the diagonal embedding) and on `L` through
  the given `[Algebra K L]`. The `A_K`-algebra structure is Mathlib's standard
  left-factor instance `Algebra.TensorProduct.leftAlgebra`, so
  `a • (x ⊗ₜ l) = (a * x) ⊗ₜ l`.
- **Target.** `A_L`, an `A_K`-algebra through the published scoped instance
  `FiniteAdeleExtension.instAlgebra` of `FiniteAdeleAlgebra`. Its ring map is
  `finiteAdeleInclusion : A_K →+* A_L`, so `x • y = finiteAdeleInclusion x * y`.
- **Formula.** On pure tensors the map is given by the published lemma
  `finiteAdeleTensorMap_tmul`:

  ```lean
  finiteAdeleTensorMap K L (x ⊗ₜ[K] l) =
    finiteAdeleInclusion x * algebraMap L (FiniteAdeleRing (𝓞 L) L) l
  ```

  Here `algebraMap L A_L` is the diagonal embedding of `L`. The published
  module `FiniteAdeleTensorMap` defines the map with Mathlib's universal
  property `AlgHom.liftEquiv` and proves this formula by `rfl`.

`Function.Bijective (finiteAdeleTensorMap K L)` is bijectivity of the
underlying function of the map, obtained by Mathlib's coercion from algebra
homomorphisms to functions. The algebra structures enter only through the type
of the map. The statement does not write that type, so the module opens no
scope; in particular it does not need `FiniteAdeleExtension`. The private
development check confirmed that the statement elaborates without it.

## What this module does and does not contain

This file states the bijectivity assertion only. It supplies no proof of it,
and it defines no algebra equivalence `A_K ⊗[K] L ≃ₐ[A_K] A_L`. A proof is the
subject of a separate exact-target proof task. That task will prove a theorem
of type `FiniteAdeleTensorMapBijective.{u, v}`. Packaging the map as an algebra
equivalence (for example with `AlgEquiv.ofBijective`), and any topology,
homeomorphism or norm statement, are outside this module.

## Universal proposition packaging

Imperial states bijectivity as a theorem with typeclass binders. Here the same
kind of assertion is packaged as one closed proposition: a `def` returning
`Prop` that quantifies over all number fields `K : Type u` and `L : Type v` and
over their instances. A proof of the target is a single term
`h : FiniteAdeleTensorMapBijective.{u, v}`. A consumer applies it as `h K L` to
get `Function.Bijective (finiteAdeleTensorMap K L)` for its own fields, with
the instances found by instance search. This packaging is derived for the
Library's statement-then-proof workflow. It adds no mathematical content.

## Correspondence with Imperial FLT

The source is ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`, file
[`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean#L229-L252),
lines 229–252, theorem `IsDedekindDomain.FiniteAdeleRing.baseChange_bijective`:

```lean
theorem baseChange_bijective [FiniteDimensional K L] :
    Function.Bijective (SemialgHom.baseChangeOfAlgebraMap <|
      (mapSemialgHom A K L B).toSemialgHom)
```

### Binders

The theorem's complete binder list is given in
[the audit, section 2.2](../../../notes/reuse/finite-adele-base-change-audit.md).
It consists of the four types `A K L B : Type*`, the 16 instances of the file's
`variable` block (lines 44–47):

```lean
[CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
[Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
[Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
[IsDedekindDomain B] [IsFractionRing B L]
```

and three further binders: `[Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]` (line 102),
`[ComapFiberwiseSMul A K L B]` (line 115) and `[FiniteDimensional K L]`.

### Specialization to number fields

Imperial works with general Dedekind domains `A` and `B` and their fraction
fields `K` and `L`. This target specializes to number fields, with
`A = 𝓞 K` and `B = 𝓞 L`, as follows.

- The 16 instances of the `variable` block and `[FiniteDimensional K L]` are
  found by Mathlib's instances for number fields with `[Algebra K L]`. The
  audit's probes (section 2.4) elaborate Imperial's declarations at
  `A = 𝓞 K`, `B = 𝓞 L` without further arguments. So the target has no
  finite-dimensionality, finiteness, Dedekind or fraction-field premise.
- Imperial's input `[Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]` is replaced by the Library's
  scoped algebra `FiniteAdeleExtension.instAlgebra`. That algebra is fixed in
  the type of `finiteAdeleTensorMap K L` and is not a hypothesis of the target.
- Imperial's input `[ComapFiberwiseSMul A K L B]` says that the adelic scalar
  action is computed coordinatewise by the local completion maps. For the
  Library's algebra this holds by definition: the published lemma
  `FiniteAdeleExtension.smul_apply` gives
  `(x • y) q = FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) * y q`
  by `rfl`. So the target needs no coherence premise.
- Imperial's `mapSemialgHom A K L B` has the underlying ring map `mapRingHom`.
  For number fields, the audit (section 2.6, diagnostics `264816ba` and
  `173c090c`) found that `mapRingHom (𝓞 K) K L (𝓞 L)` equals the Library's
  `finiteAdeleInclusion` by `rfl` at default transparency.
- Imperial's types are in arbitrary universes `Type*`. The target keeps two
  independent universes for `K` and `L`.

### Tensor order and construction

Imperial's map is `SemialgHom.baseChangeOfAlgebraMap` of the semialgebra map
`mapSemialgHom A K L B : 𝔸ᶠ[A, K] →SA[algebraMap K L] 𝔸ᶠ[B, L]`. By its
definition in `FLT/Mathlib/Algebra/Algebra/Bilinear.lean:41–50`, it is an
`L`-algebra map `L ⊗[K] 𝔸ᶠ[A, K] →ₐ[L] 𝔸ᶠ[B, L]`, so its source has the
opposite tensor order. Its lemma `SemialgHom.baseChange_of_algebraMap_tmul`
(same file, lines 53–57) gives `l ⊗ₜ x ↦ algebraMap L 𝔸ᶠ[B, L] l * mapSemialgHom A K L B x`.
For number fields, the audit (sections 2.5 and 2.6, diagnostic `264816ba`)
records this value as `algebraMap L A_L l * finiteAdeleInclusion x`. The
Library map uses the order `A_K ⊗[K] L` with Mathlib's left-factor algebra, and
sends `x ⊗ₜ l` to `finiteAdeleInclusion x * algebraMap L A_L l`. Composing Imperial's map with
the swap `A_K ⊗[K] L ≃ L ⊗[K] A_K` therefore agrees with the Library map on pure
tensors, by commutativity of multiplication in `A_L`. Both composites are
additive, so they agree everywhere. Hence the target is Imperial's conclusion
restated for the Library's map in the Library's tensor order. This comparison
is an explanation of the correspondence. The module neither states nor proves
it, and it uses no Imperial semialgebra API, `TensorProduct.RightActions`
scope or `ComapFiberwiseSMul` class. The audit recommends this order and this
map (section 6, unit 4).

### Imperial's proof

Imperial proves the theorem from its `L`-linear equivalence
`baseChangeLinearEquiv` (lines 205–211), a composite of four linear
equivalences (lines 131–203). Its `baseChangeAlgEquiv` and
`baseChangeAdeleAlgEquiv` (lines 255–270) then package the bijection as
algebra equivalences. None of this proof or packaging is copied here, and this
module claims no acceptance of it. Any later proof of the target is a separate
Library proof, reviewed on its own.

## Provenance and modification notice

The target restates the conclusion of the Imperial theorem cited above. The
source is retained in the registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, directory
`ImperialCollegeLondon--FLT/source`. The file
`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean` is "Copyright (c) 2025
Kevin Buzzard", with authors Kevin Buzzard and Matthew Jasper, under the Apache
License 2.0. The Lean file keeps that header and adds a modification notice.
The upstream root `LICENSE` is retained at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot contains no `NOTICE` file.

Worker 300 made these modifications:

- the general Dedekind data are specialized to number fields, with
  `A = 𝓞 K` and `B = 𝓞 L`, in independent universes;
- Imperial's semialgebra base change from `L ⊗[K] 𝔸ᶠ[A, K]` is replaced by the
  Library's published `finiteAdeleTensorMap K L` from `A_K ⊗[K] L`;
- Imperial's adelic algebra and `ComapFiberwiseSMul` inputs are replaced by the
  Library's scoped algebra, which the map's type already fixes;
- the theorem is restated as a universally quantified `Prop`-valued
  definition, as explained above.

No Lean proof, external import or Anthropic code is used. None of the audit's
compatibility patches (a)–(d) applies, because no source is ported. The public
audit [finite-adele base change](../../../notes/reuse/finite-adele-base-change-audit.md),
sections 2 and 6, explains the reuse boundary.

## Checks

A private `lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
compiled the module without errors or warnings. Inspection of
`FiniteAdeleTensorMapBijective` reported a `Prop`-valued definition with
universe parameters `u` and `v`. It depends only on `propext`,
`Classical.choice` and `Quot.sound`. A separate private check printed the
fully elaborated body. It contains exactly the quantifiers and five instances
listed above and the unchanged map `finiteAdeleTensorMap K L`, whose type uses
`Algebra.TensorProduct.leftAlgebra` on the source and
`FiniteAdeleExtension.instAlgebra` on the target. The same check proved, by
`Iff.rfl`, that the target is equivalent to the statement written with the full
map type `A_K ⊗[K] L →ₐ[A_K] A_L`. These checks are not independent semantic
acceptance.
