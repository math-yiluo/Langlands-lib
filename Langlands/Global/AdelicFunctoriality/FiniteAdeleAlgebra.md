# Scoped finite-adele algebra and scalar coherence

This module imports `Langlands.Global.AdelicFunctoriality.Inclusion` and defines
scalar extension between the actual finite adele rings of two number fields.
The fields `K : Type u` and `L : Type v` have independent universes, with
`[Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]` throughout.
Write `A_K = FiniteAdeleRing (𝓞 K) K` and `A_L = FiniteAdeleRing (𝓞 L) L` in
this document. All new declarations are in
`Langlands.Global.AdelicFunctoriality.FiniteAdeleExtension`.

## Algebra and coordinate action

`instAlgebra : Algebra A_K A_L` is the scoped instance
`(finiteAdeleInclusion (K := K) (L := L)).toAlgebra`. Its ring homomorphism is
exactly the published inclusion, as `algebraMap_eq` proves by reflexivity.
At a finite place `q` of `L`, `algebraMap_apply` gives

```
algebraMap A_K A_L x q =
  FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))).
```

`smul_apply` gives the defining coordinate scalar formula

```
(x • y) q =
  FiniteExtension.completionMap (q.under (𝓞 K)) q (x (q.under (𝓞 K))) * y q.
```

Both proofs are reflexivity: the scalar action from `RingHom.toAlgebra` is
multiplication by the image, and multiplication of finite adeles is coordinatewise.
`smul_apply_eq_local_smul` restates the same equality as
`(x • y) q = x (q.under (𝓞 K)) • y q`. Its right side uses the **existing**
scoped completion algebra in `FiniteExtension`, induced by `completionMap`.
The existing `liesOver_under` instance supplies the prime-over relation.
This module introduces no local-completion algebra instance.

## Diagonal maps and scalar towers

`algebraMap_diagonal` says that the composite `K → A_K → A_L` sends `k` to
`algebraMap L A_L (algebraMap K L k)`. It is precisely the published
`finiteAdeleInclusion_diagonal` applied to `k` after identifying the scalar map.
`algebraMap_comp_diagonal` gives the equality of these two composite ring
homomorphisms, using `RingHom.ext` and that elementwise formula.
`diagonal_smul` says

```
(algebraMap K A_K k) • y = (algebraMap K L k) • y.
```

Its proof expands both actions with `Algebra.smul_def` and applies the diagonal
formula. These three lemmas require no separate `Algebra K A_L` instance.

For the remaining declarations, choose `[Algebra K A_L]` together with
`[IsScalarTower K L A_L]`. Under exactly these additional assumptions,
`instIsScalarTower` is a scoped instance of `IsScalarTower K A_K A_L`.
Its proof uses `IsScalarTower.of_algebraMap_eq`, the diagonal formula above,
and the given tower's `IsScalarTower.algebraMap_apply`. Thus it identifies the
two existing coefficient actions; it does not define another action of `K`.
`inclusionAlgHom : A_K →ₐ[K] A_L` packages `finiteAdeleInclusion` with this
coefficient compatibility. The commutation proof composes
`finiteAdeleInclusion_diagonal` with the reverse of the given tower's
`algebraMap_apply`.

## Scope and use

After importing this module, activate the two new instances with

```lean
open scoped Langlands.Global.AdelicFunctoriality.FiniteAdeleExtension
```

They are scoped to avoid making a chosen extension action globally available,
in particular when source and target fields coincide. The imported Mathlib
coefficient algebras `Algebra K A_K` and `Algebra L A_L` are retained. The local
scope `FiniteExtension` in this file only enables its previously published
completion algebra for `smul_apply_eq_local_smul`; downstream code needing that
local action can explicitly open
`Langlands.Global.AdelicFunctoriality.FiniteExtension`.

If a consumer has not already chosen compatible `K` scalars on `A_L`, the
following local declarations provide them without a global instance:

```lean
local instance : Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  Algebra.compHom (FiniteAdeleRing (𝓞 L) L) (algebraMap K L)
local instance : IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) :=
  .of_algebraMap_eq' rfl
```

With the new scope open, typeclass inference then supplies the tower through
`A_K`. After importing `Mathlib.RingTheory.TensorProduct.Basic`, Mathlib's
`AlgHom.liftEquiv K A_K L A_L` applied to
`IsScalarTower.toAlgHom K L A_L` constructs an `A_K`-algebra map
`A_K ⊗[K] L →ₐ[A_K] A_L`. Its pure-tensor value is definitionally
`finiteAdeleInclusion x * algebraMap L A_L l`. This explains the precise
coherence interface furnished for the subsequent base-change unit; this module
does not itself define that tensor map or assert its bijectivity.

Private Lean usage checks compiled the independent-universe interface, absence
of the new action outside its scope, local coefficient restriction, inference
of the new tower, formation of this tensor map, and its pure-tensor formula.
The inspected declarations `instAlgebra`, `smul_apply`, `instIsScalarTower`, and
`inclusionAlgHom` use only `propext`, `Classical.choice`, and `Quot.sound`.
Development checks are not independent semantic acceptance.

## Provenance and modification notice

The source is ImperialCollegeLondon/FLT at commit
`923d45174c500aa1d994ba973bac38ea39eacbf7`, retained in registered source
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source tree is the `ImperialCollegeLondon--FLT/source` directory of that
registered snapshot.

The adapted construction is
[`FLT/NumberField/AdeleRing.lean`, lines 349–370](https://github.com/ImperialCollegeLondon/FLT/blob/923d45174c500aa1d994ba973bac38ea39eacbf7/FLT/NumberField/AdeleRing.lean#L349),
especially the scoped finite-adele algebra at line 364 and its coordinate
coherence at lines 369–370. That file is copyright 2024 Kevin Buzzard, with
authors Kevin Buzzard, Salvatore Mercuri, Ruben Van de Velde, Matthew Jasper,
Bryan Wang Peng Jun, and Yaël Dillies. Its original copyright, license and
author header are retained in the Lean file. The upstream root Apache-2.0
`LICENSE` is retained byte-for-byte at
[licenses/ImperialCollegeLondon-FLT/LICENSE](../../../../licenses/ImperialCollegeLondon-FLT/LICENSE).
The source snapshot contains no `NOTICE` file.

Worker 50's modifications are: use the Library's `finiteAdeleInclusion` instead
of Imperial's `mapRingHom`; put the instance in a dedicated Library scope with
an explicit name; preserve independent universes; express coordinate coherence
as lemmas over the existing Library completion algebra; and derive diagonal
and coefficient scalar-tower compatibility from the published Library lemma.
The scalar-tower and bundled `K`-algebra-map declarations are derived additions,
not copied external theorems. Their implemented proofs are described above.
The broad FLT-specific `ComapFiberwiseSMul` class is unnecessary for this unit.
None of the audit's compatibility patches (a)–(d) is needed by this focused
construction; no external import closure or Anthropic code is used.

The public audit [finite-adele base change, sections 2.6 and 6](../../../../notes/reuse/finite-adele-base-change-audit.md)
explains this reuse boundary. This module proves neither integral nor global
tensor bijectivity, a topological comparison, nor a norm identity.
