# Proof of the zero-action separation of unitized finiteness conventions

Author: Worker 734. This is the proof successor, task
`496674fd-4092-4273-b39e-854ef631e73d`, to the statement-only unit
`Langlands.Algebra.UnitizationZeroActionFinitenessStatements` (statement
author Worker 709). Both belong to whole-book Renard task
`f5d1f399-a1f8-4ab5-a981-90b92abd4857`. The proof was written
independently; it does not reuse Worker 709's private feasibility proof.

## What is proved

The module `Langlands.Algebra.UnitizationZeroActionFiniteness` imports the
published statement module by Lean name and leaves it unchanged. It proves,
in namespace `Langlands.Algebra.UnitizationZeroActionFiniteness`:

- `complexZeroAction : ComplexZeroActionStatement.{uA}`;
- `integerZeroAction : IntegerZeroActionStatement.{uA}`;
- `zeroActionFiniteness : ZeroActionFinitenessStatements.{uA}`, the
  aggregate theorem. Its type is exactly the published proposition, and it
  is the pair `⟨complexZeroAction, integerZeroAction⟩` in the published
  order.

The algebra universe `uA` is arbitrary. The carrier is the actual
`Complex : Type 0`, and its additive group is the same in both branches. No
premise is added to the statement: no commutativity of `A`, no Noetherian
ring, no nondegeneracy, no nonzero algebra and no finite-generation or
dimension hypothesis. No new action constructor, global instance or general
transport interface is introduced. The only facts about the two actions that
are used are the public `CompatibleUnitization.isScalarTower` and
`CompatibleUnitization.zero_smul_eq`.

## Module choices

As in the statement, each branch installs its actual unitized action locally
with `letI`:

- positive branch: `CompatibleUnitization.module (0 : A →ₙₐ[ℂ] Module.End ℂ ℂ)`,
  a `Module (Unitization ℂ A) ℂ`, for `A : Type uA` with `NonUnitalRing A`,
  `Module ℂ A`, `IsScalarTower ℂ A A` and `SMulCommClass ℂ A A`;
- negative branch: `CompatibleUnitization.module (0 : A →ₙₐ[ℤ] Module.End ℤ ℂ)`,
  a `Module (Unitization ℤ A) ℂ`, for `A : Type uA` with `NonUnitalRing A`.
  The `ℤ`-algebra data on `A` and the `ℤ`-module structure on `ℂ` are the
  canonical instances, the same ones the statement elaborates with.

`CompatibleUnitization.zero_smul_eq` says that in both cases
`x • z = x.fst • z`, with the scalar action of `ℂ` or `ℤ` respectively. The
original `A`-action is zero in both branches. Only the adjoined scalars
differ.

## Proof of the positive branch (`complexZeroAction`)

The local instance
`IsScalarTower ℂ (Unitization ℂ A) ℂ` is supplied by the named adapter
`CompatibleUnitization.isScalarTower (0 : A →ₙₐ[ℂ] Module.End ℂ ℂ)`. The
complex line is finite over itself, by `Module.Finite.self ℂ`, passed
explicitly. It is Noetherian over itself because a division ring is a
principal ideal ring: the local instance
`IsPrincipalIdealRing ℂ` is `DivisionSemiring.isPrincipalIdealRing ℂ`, and
`PrincipalIdealRing.isNoetherianRing (R := ℂ)` then gives
`IsNoetherianRing ℂ`, both from `Mathlib.RingTheory.PrincipalIdealDomain`.
Finiteness transfers up the tower by Mathlib's
`Module.Finite.of_restrictScalars_finite ℂ (Unitization ℂ A) ℂ`.
Noetherianity transfers by `isNoetherian_of_tower ℂ`. Every
`Unitization ℂ A`-submodule is in particular a `ℂ`-submodule, so the
ascending chain condition is inherited.

## Proof of the negative branch (`integerZeroAction`)

First, `Module.Finite (Unitization ℤ A) ℂ` is refuted. Let `f` be the
identity of `ℂ` regarded as a semilinear map
`ℂ →ₛₗ[(Unitization.fstHom ℤ A).toRingHom] ℂ`. Its `map_smul'` field is
exactly `CompatibleUnitization.zero_smul_eq x z`, i.e.
`x • z = x.fst • z`. Since `f` is surjective (`Function.surjective_id`),
Mathlib's `Module.Finite.of_surjective f` turns a finite generating set over
the integer unitization into one over `ℤ`, giving `Module.Finite ℤ ℂ`. As
`ℤ` is countable, `Finsupp.Countable.of_moduleFinite` makes `ℂ` countable,
contradicting `not_countable_complex`. That lemma gives `#ℂ = 𝔠` via
`Cardinal.mk_complex` and Cantor's theorem.

Second, `IsNoetherian (Unitization ℤ A) ℂ` is refuted. A Noetherian module
is finite by Mathlib's `Module.IsNoetherian.finite (Unitization ℤ A) ℂ`,
so the first part applies.

Both parts hold for every nonunital ring `A`, including the zero ring and
algebras for which some element acts as an identity. Only the first
coordinate of the integer unitization acts.

## Checks

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, development check
`0d3a8b9a-6e2c-4dee-961e-a0f2fbf3b10d` compiled the module with zero errors
and zero warnings. Lake-build inspection `18c2dfbd-e10b-4a4a-8e59-6b3749439d65`
of `zeroActionFiniteness` reports a theorem with sole universe parameter
`uA` and exactly the standard assumptions `propext`, `Classical.choice`
and `Quot.sound`. These development checks are not acceptance; independent
review and the exact-target validation decide that.

## Provenance and boundary

This is an internal derived comparison of two ordinary unital-module
structures on the same complex line. The two predicates are Mathlib's
`Module.Finite` and `IsNoetherian` over the displayed unital rings. The
comparison is motivated by David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The relevant passages are the nonunital conventions (printed page 6/PDF
page 12), the complex unit-adjoining construction of I.2.1 (printed page
14/PDF page 20), the finite and Noetherian object definitions of A.I.3 (PDF
pages 254–255) and the final C.II proposition (printed page 279/PDF page
285). The registered supplement `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 18–19, does not settle this convention question. The proof
route is the standard modern module-theoretic one described above. It is
not taken from the book.

This proof does not identify either convention with Renard's finiteness or
Noetherian definitions. It is not a counterexample to the book, and it does
not prove the source-facing C.II proposition or complete any chapter. It
supplies no general change-of-scalars construction. Unitization
finite-generation transport, compatible localization and the other parent
obligations remain separate.
