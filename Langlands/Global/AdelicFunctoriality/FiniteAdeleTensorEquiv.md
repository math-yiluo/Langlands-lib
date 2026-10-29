# The canonical finite-adele tensor algebra equivalence

This module imports `Langlands.Global.AdelicFunctoriality.FiniteAdeleTensorProof`
and defines `Langlands.Global.AdelicFunctoriality.finiteAdeleTensorEquiv`.
Write `A_K = IsDedekindDomain.FiniteAdeleRing (𝓞 K) K` and
`A_L = IsDedekindDomain.FiniteAdeleRing (𝓞 L) L`. The equivalence has type

```lean
finiteAdeleTensorEquiv K L : A_K ⊗[K] L ≃ₐ[A_K] A_L
```

The fields `K : Type u` and `L : Type v` have independent universes. The
equivalence and all four lemmas have exactly the five assumptions
`[Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]`.
There is no further finiteness, coefficient-algebra, scalar-tower, coherence,
integral-comparison or bijectivity premise.

## Algebra structures and construction

The tensor order is `A_K ⊗[K] L`. The `K`-algebra on `A_K` is its diagonal
algebra, and the action on `L` comes from the given `[Algebra K L]`.
The source uses Mathlib's standard left-factor `A_K`-algebra
`Algebra.TensorProduct.leftAlgebra`. In particular,
`a • (x ⊗ₜ[K] l) = (a * x) ⊗ₜ[K] l`.
The target uses the published scoped algebra
`FiniteAdeleExtension.instAlgebra`, induced by `finiteAdeleInclusion`, so
`a • y = finiteAdeleInclusion a * y`.
The module opens the scopes `NumberField`, `TensorProduct` and
`FiniteAdeleExtension`. Clients writing the displayed algebra-equivalence
type should open the same scopes, with `FiniteAdeleExtension` in the namespace
`Langlands.Global.AdelicFunctoriality`.

The definition is exactly

```lean
AlgEquiv.ofBijective (finiteAdeleTensorMap K L)
  (finiteAdeleTensorMapBijective_proof K L)
```

The imported theorem proves the universal proposition
`FiniteAdeleTensorMapBijective.{u, v}`; applying it to `K` and `L` supplies
bijectivity of this particular canonical map. Mathlib's `AlgEquiv.ofBijective`
retains the algebra homomorphism as its forward map and constructs its inverse
from bijectivity. The coefficient `K`-algebra on `A_L` and its compatible
towers remain internal to the imported map. This module installs no instance
and repeats no bijectivity argument.

## Defining lemmas

All declarations below lie in `Langlands.Global.AdelicFunctoriality`.

- `finiteAdeleTensorEquiv_toAlgHom` (simp) states
  `(finiteAdeleTensorEquiv K L).toAlgHom = finiteAdeleTensorMap K L`.
  Its proof is `rfl`. Both fields are explicit arguments.
- `finiteAdeleTensorEquiv_apply` identifies the value on every tensor `z`
  with `finiteAdeleTensorMap K L z`, also by `rfl`.
- `finiteAdeleTensorEquiv_tmul` (simp) gives

  ```lean
  finiteAdeleTensorEquiv K L (x ⊗ₜ[K] l) =
    finiteAdeleInclusion x * algebraMap L A_L l
  ```

  Here `algebraMap L A_L` is the diagonal embedding of `L`. The proof reuses
  `finiteAdeleTensorMap_tmul`, since the forward functions agree definitionally.
- `finiteAdeleTensorEquiv_tmul_apply` gives, at
  `q : HeightOneSpectrum (𝓞 L)`,

  ```lean
  finiteAdeleTensorEquiv K L (x ⊗ₜ[K] l) q =
    FiniteExtension.completionMap (q.under (𝓞 K)) q
      (x (q.under (𝓞 K))) * algebraMap L (q.adicCompletion L) l
  ```

  Its proof reuses `finiteAdeleTensorMap_tmul_apply` through the same
  definitional equality. Thus the completion map is the existing map at the
  prime below `q`. In these last three lemmas the fields are implicit.

## Provenance and adaptations

The source is ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`,
[`FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean:254–270`](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/DedekindDomain/FiniteAdeleRing/BaseChange.lean#L254-L270).
It is retained under registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
directory `ImperialCollegeLondon--FLT/source`.
Imperial's `baseChangeAlgEquiv` packages its bijective canonical map with
`AlgEquiv.ofBijective` as an `L`-algebra equivalence on `L ⊗[K] A_K`.
Its `baseChangeAdeleAlgEquiv` supplies `A_K`-linearity through the
right-factor action on that tensor product.

Worker 98 adapts this packaging to number fields in independent universes,
using the Library's tensor order `A_K ⊗[K] L`, Mathlib's left-factor algebra,
and the inclusion-induced scoped algebra on `A_L`. The existing canonical
map is already an `A_K`-algebra homomorphism, so applying `ofBijective`
directly gives the requested algebra equivalence. Imperial's semialgebra
base-change and right-action APIs and its separate commutation proof are
replaced by the published Library map and its accepted exact bijectivity
theorem. The four defining lemmas are derived content: their proofs are
the definitional forward-map equalities and the two imported map formulas
described above. These are the additional adaptations beyond the audit's
patches (a)–(d). None of those patches applies to this small packaging:
no external topology, completion or right-action implementation is copied.
The [public audit, section 6, unit 4](../../../notes/reuse/finite-adele-base-change-audit.md)
recommends this tensor order and canonical map.

The original file is copyright (c) 2025 Kevin Buzzard, with authors
Kevin Buzzard and Matthew Jasper, under Apache-2.0. Its copyright, license
and author header are retained in the Lean file, followed by Worker 98's
modification notice. The upstream root license remains at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The retained Imperial source has no `NOTICE` file. No Anthropic code is used.
Published prerequisites are reused by Lean import and retain their own
attribution; no unpublished draft is reused.

This module supplies the algebra equivalence and its evaluation formulas.
Topology, homeomorphisms, module topology, module finiteness and norm
theorems are outside this construction.

## Development checks

In approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`,
`lean_check` diagnostic `51212b46-b85f-4064-8f59-48403ac94dd0` compiled and
inspected the equivalence with zero errors and warnings. Inspection reports
independent universe parameters `u` and `v` and only `propext`,
`Classical.choice` and `Quot.sound` as axioms. Private diagnostic
`8bb7434f-957d-4e04-aa85-efb70f7d2bfe` printed the complete unapplied
equivalence and all four lemma signatures, checked their standard axiom
dependencies, and assigned the fully explicit equivalence constant to the
displayed universal type with exactly the five instances. It also completed
with zero errors and warnings. These checks are development evidence;
independent semantic acceptance and publication are separate.
