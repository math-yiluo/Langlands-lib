# The canonical map `A_K ⊗[K] L → A_L` of finite adele rings

This module imports `Langlands.Global.AdelicFunctoriality.FiniteAdeleAlgebra`
and defines the canonical algebra map from the base change of the finite adeles
of `K` to the finite adeles of `L`. The fields `K : Type u` and `L : Type v`
have independent universes. Write `A_K = FiniteAdeleRing (𝓞 K) K` and
`A_L = FiniteAdeleRing (𝓞 L) L` in this document. All declarations are in the
namespace `Langlands.Global.AdelicFunctoriality`. The module defines no instance
and does not change any existing one.

The map and its four evaluation lemmas take exactly the assumptions
`[Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]`. They have no
other coefficient action, local-completion algebra, `ComapFiberwiseSMul`-type
class, integral comparison or bijectivity hypothesis. For the map, `K` and `L`
are explicit arguments: `finiteAdeleTensorMap K L`. They are implicit in the
evaluation lemmas.

## Tensor order and the two algebra structures

The source is `A_K ⊗[K] L`, with `A_K` as the left factor. Its `A_K`-algebra
structure is Mathlib's standard left-factor instance
`Algebra.TensorProduct.leftAlgebra`, so `a • (x ⊗ₜ l) = (a * x) ⊗ₜ l`. The
`K`-module structure on `A_K` is Mathlib's `Algebra K A_K`, given by the
diagonal embedding. This is the tensor order of the Library's local map
`finiteTensorMap`. Imperial's right-factor order `L ⊗[K] A_K` and its
`TensorProduct.RightActions` scope are not used.

The target `A_L` is an `A_K`-algebra through unit 1's scoped instance
`FiniteAdeleExtension.instAlgebra`. Its ring map is `finiteAdeleInclusion`, so
`x • y = finiteAdeleInclusion x * y`. The module opens
`scoped Langlands.Global.AdelicFunctoriality.FiniteAdeleExtension` to state the
type of the map. A client that writes `A_K`-linear or `A_K`-algebra types with
target `A_L`, such as an algebra equivalence built from this map, must open the
same scope. Applying the map to elements does not need the scope.

## The coefficient `K`-algebra on `A_L`

Mathlib's universal property needs a `K`-algebra structure on `A_L` and two
compatible scalar towers. Mathlib and the Library provide no such structure, so
this module defines one. It is the `L` diagonal restricted along `K → L`:

```lean
abbrev finiteAdeleCoefficientAlgebra : Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  Algebra.compHom _ (algebraMap K L)
```

It is not an instance. As an instance it would apply to every `K` with
`[Algebra K L]`, including `K = L`, where it would compete with Mathlib's
`Algebra L A_L`. The module installs it only with `letI` inside the proofs and
the definition below, and the type of `finiteAdeleTensorMap` does not mention it.
It needs only `[Field K] [Field L] [NumberField L] [Algebra K L]`. The three
lemmas below state their conclusions under `letI := finiteAdeleCoefficientAlgebra K L`:

- `finiteAdeleCoefficientAlgebra_algebraMap`: the scalar map is
  `(algebraMap L A_L).comp (algebraMap K L)`, by `rfl`.
- `finiteAdeleCoefficientAlgebra_isScalarTower : IsScalarTower K L A_L`, proved
  by `IsScalarTower.of_algebraMap_eq` with `rfl` at each element.
- `finiteAdeleCoefficientAlgebra_isScalarTower_finiteAdeleRing :
  IsScalarTower K A_K A_L`. This is unit 1's scoped instance
  `FiniteAdeleExtension.instIsScalarTower`, applied to the previous tower. That
  instance rests on `finiteAdeleInclusion_diagonal`.

The first two lemmas do not need `[NumberField K]`, and Lean omits it from their
signatures. The third lemma has all five assumptions.

## The map

```lean
def finiteAdeleTensorMap :
    FiniteAdeleRing (𝓞 K) K ⊗[K] L →ₐ[FiniteAdeleRing (𝓞 K) K] FiniteAdeleRing (𝓞 L) L
```

is Mathlib's `AlgHom.liftEquiv K A_K L A_L`, from
`Mathlib.RingTheory.TensorProduct.Basic`, applied to the `K`-algebra map
`IsScalarTower.toAlgHom K L A_L`, the diagonal `L → A_L`. The definition installs
the coefficient algebra and the two towers above with `letI`/`haveI`.
`AlgHom.liftEquiv` is the base-change adjunction
`(L →ₐ[K] A_L) ≃ (A_K ⊗[K] L →ₐ[A_K] A_L)`. So the map is the unique `A_K`-algebra
map that restricts to the diagonal on `1 ⊗ L`. This module does not state that
uniqueness.

## Evaluation lemmas

The map is defined by

- `finiteAdeleTensorMap_tmul` (simp):
  `finiteAdeleTensorMap K L (x ⊗ₜ[K] l) = finiteAdeleInclusion x * algebraMap L A_L l`.
  The proof is `rfl`. `AlgHom.liftEquiv_tmul` gives `x • algebraMap L A_L l`,
  and unit 1's scalar action is multiplication by `finiteAdeleInclusion x`.
- `finiteAdeleTensorMap_tmul_apply`: at a finite place `q` of `L`,

  ```
  finiteAdeleTensorMap K L (x ⊗ₜ[K] l) q =
    FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) *
      algebraMap L (q.adicCompletion L) l.
  ```

  The proof is `rfl`. It combines the published `finiteAdeleInclusion_apply`,
  coordinatewise multiplication in `A_L`, and the fact that the coordinate of
  `algebraMap L A_L l` at `q` is the image of `l` in `q.adicCompletion L`. The
  first factor uses the published `FiniteExtension.completionMap` at the place
  `q.under (𝓞 K)` below `q`.
- `finiteAdeleTensorMap_one_tmul`:
  `finiteAdeleTensorMap K L (1 ⊗ₜ[K] l) = algebraMap L A_L l`. The proof
  rewrites with the pure-tensor lemma, `map_one` and `one_mul`.
- `finiteAdeleTensorMap_tmul_one`:
  `finiteAdeleTensorMap K L (x ⊗ₜ[K] 1) = finiteAdeleInclusion x`. The proof
  rewrites with the pure-tensor lemma, `map_one` and `mul_one`.

Since it is an `A_K`-algebra map, `finiteAdeleTensorMap K L` is also `A_K`-linear
and commutes with `algebraMap A_K`. This follows from its type.

## Scope of this module

This is the definition phase of the global finite-adele base change, unit 4.
The module does not state or prove that `finiteAdeleTensorMap K L` is bijective.
It constructs no algebra equivalence, topology, module topology or homeomorphism,
and makes no norm statement. A later Prop-valued statement and its exact proof
will treat bijectivity, using the published unit-2 restricted-product tensor
equivalences and the unit-3 integral local comparison. The module imports neither.

## Provenance and modification notice

The construction is a derived reformulation, not a copy. The source is
ImperialCollegeLondon/FLT at commit `923d45174c500aa1d994ba973bac38ea39eacbf7`,
retained in registered source `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`),
directory `ImperialCollegeLondon--FLT/source`. The relevant parts of
[`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean#L75)
are:

- lines 75–127: the adelic map `mapRingHom`, which is the Library's
  `finiteAdeleInclusion`; the coherence class `ComapFiberwiseSMul`; and
  `BaseChange.algebraMap_apply`, the coordinate formula of the adelic scalar map;
- lines 255–270: `baseChangeAlgEquiv` and `baseChangeAdeleAlgEquiv`. Their
  underlying map `L ⊗[K] A_K → A_L` is the base change of `mapSemialgHom` along
  `K → L`, with `A_K` acting on the right factor.

That file is copyright (c) 2025 Kevin Buzzard, with authors Kevin Buzzard and
Matthew Jasper, under the Apache License 2.0. Its copyright, license and author
header are retained in the Lean file, together with a modification notice. The
upstream root `LICENSE` is retained byte-for-byte at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot contains no `NOTICE` file.

Worker 300's modifications are as follows. The map is in the Library's tensor
order `A_K ⊗[K] L` with Mathlib's left-factor algebra, not Imperial's right
actions. It is defined by Mathlib's universal property `AlgHom.liftEquiv` from
the diagonal `L → A_L`, not as a semialgebra base change. It uses unit 1's scoped
algebra and `finiteAdeleInclusion` in place of `mapRingHom` and
`ComapFiberwiseSMul`. The coefficient `K`-algebra on `A_L` is an explicit
non-instance definition. Independent universes are kept. The map is only the
underlying map of Imperial's equivalence: Imperial's bijectivity proof (lines
129–252) and equivalence packaging are not ported here. The coefficient algebra,
its towers and the four evaluation lemmas are derived additions. Their proofs
are described above. None of the audit's compatibility patches (a)–(d) is needed.
No Imperial semialgebra API and no Anthropic code is used. The public audit
[finite-adele base change, sections 2 and 6](../../../notes/reuse/finite-adele-base-change-audit.md)
recommends this tensor order and the formula `x ⊗ l ↦ finiteAdeleInclusion x * algebraMap L _ l`
(its unit 4).

Private `lean_check` runs in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
compiled the module without warnings. The inspected declarations use only
`propext`, `Classical.choice` and `Quot.sound`. Development checks are not
independent semantic acceptance.
