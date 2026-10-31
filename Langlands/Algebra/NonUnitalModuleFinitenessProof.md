# Object finiteness for original additive nonunital modules: proof

This module proves the published aggregate
`Langlands.Algebra.NonUnitalModuleFiniteness.NonUnitalModuleFinitenessStatement`
in the theorem `nonUnitalModuleFiniteness`, whose complete type is
`NonUnitalModuleFinitenessStatement.{uA, uM}` with the independent universe
parameters `uA, uM` in that order. It imports the statement module
`Langlands.Algebra.NonUnitalModuleFinitenessStatements` by its Lean name and
leaves that module, its Markdown and its imports unchanged. The closed
theorems `finiteType`, `finiteSubcover`, `noetherian`, `finiteGeneration` and
`noetherianGeneration` prove the five components, and
`nonUnitalModuleFiniteness` pairs them in the aggregate's order.

Worker 1113 wrote this Lean proof. It follows the route that Worker 734
outlined in the task context, based on Worker 734's private probe: the
transport lemmas, the composite order isomorphism and the published
theorems composed. Both are credited as coauthors. No code from the probe
was copied.

## Transport along subobject order isomorphisms

The first section works in arbitrary categories `C` and `D`, with four
independent universe parameters, for objects `X : C` and `Y : D` and an
order isomorphism `e : Subobject X ≃o Subobject Y` of the actual subobject
types. It uses only the order structure of `Subobject`, so the predicates
from `Langlands.CategoryTheory.RenardFiniteType` transfer as follows.

- `hasSubobjectUnions_of_orderIso`: for a set `S` of subobjects of `X`, the
  union of `e '' S` in `Y` is pulled back by `e.symm`. Mathlib's
  `OrderIso.isLUB_image` says that this is a least upper bound of `S`.
- `hasFiniteSubcoverProperty_of_orderIso`: unions transfer as above. If `S`
  has least upper bound `⊤`, then `OrderIso.isLUB_image'` and `e ⊤ = ⊤` show
  that `e '' S` has least upper bound `⊤`. The hypothesis on `Y` then gives a
  finite `T ⊆ e '' S` with least upper bound `⊤`. The finite subcover for `X`
  is `T.image e.symm`, formed with classical decidable equality. Each member
  is `e.symm (e R) = R` for some `R ∈ S`. By `Finset.coe_image` and
  `OrderIso.isLUB_image'` for `e.symm`, it again has least upper bound `⊤`.
  An empty finite subcover is handled the same way.
- `isNoetherianObject_of_orderIso`: a nonempty set `S` of subobjects of `X`
  has nonempty image `e '' S`. The hypothesis on `Y` gives a maximal member
  `e P'` with `P' ∈ S`. If `P' ≤ Q` with `Q ∈ S`, then `e P' ≤ e Q` by
  monotonicity, so maximality gives `e Q = e P'`, and injectivity of `e`
  gives `Q = P'`.
- `hasFiniteSubcoverProperty_congr` and `isNoetherianObject_congr` state the
  two equivalences. They apply the one-way lemmas to `e.symm` and to `e`.

No union-existence, finiteness or size assumption is added. The
finite-type predicate is not transported directly. Component 1 instead uses
the published finite-type/finite-subcover theorem in the original category.

## The subobject comparison with the unitized module

For `A : Type uA` with `[NonUnitalRing A]` and
`M : NonUnitalModuleCat.{uA, uM} A`, the definition
`subobjectExtendOrderIso M : Subobject M ≃o Subobject (IntegerUnitization.extendObj A M)`
is the composite of three published order isomorphisms:

1. `NonUnitalModuleCat.subobjectOrderIso M`, from
   `Langlands.Algebra.NonUnitalModuleSubobject`. It sends categorical
   subobjects of `M` in `NonUnitalModuleCat.{uA, uM} A` to the original
   stable additive subgroups `NonUnitalSubmodule A M`.
2. `NonUnitalSubmodule.intUnitizedOrderIso (A := A) (M := M)`. It sends
   these subgroups to the submodules of the module
   `CompatibleUnitization.module (NonUnitalModule.toIntLinearEndHom (A := A) (V := M))`
   over `Unitization ℤ A` on the same carrier.
3. The inverse of Mathlib's
   `ModuleCat.subobjectModule (IntegerUnitization.extendObj A M)`. It sends
   these submodules to the categorical subobjects of
   `IntegerUnitization.extendObj A M` in `ModuleCat (Unitization ℤ A)`.

`IntegerUnitization.extendObj A M` is defined as `ModuleCat.of` of the same
carrier with the same locally selected `CompatibleUnitization.module`
instance. The composite therefore type-checks without casts. No other
correspondence between categorical subobjects and subgroups is built, and
none is assumed.

## The five components

Each component is first proved for one object, with the target's exact right
side. That right side installs the selected module with the same `letI`.

- Component 2, `finiteSubcover_iff_finite M`: `hasFiniteSubcoverProperty_congr`
  along `subobjectExtendOrderIso M`, followed by the published
  `Langlands.Renard.ModuleFiniteType.finiteSubcover_iff_finite`
  for `IntegerUnitization.extendObj A M`. The resulting
  `Module.Finite (Unitization ℤ A) (IntegerUnitization.extendObj A M)` is
  definitionally the target's right side, so `Iff.trans` composes them
  directly.
- Component 1, `finiteType_iff_finite M`: the published
  `Langlands.Renard.finiteTypeFiniteSubcover (NonUnitalModuleCat.{uA, uM} A) M`.
  In the original category it identifies `IsFiniteTypeObject M` with
  `HasFiniteSubcoverProperty M`. Component 2 completes the proof.
- Component 3, `noetherianObject_iff_isNoetherian M`:
  `isNoetherianObject_congr` along the same order isomorphism, followed by the
  published `Langlands.Renard.ModuleNoetherian.object_iff (Unitization ℤ A)
  (IntegerUnitization.extendObj A M)`.
- Component 4, `finiteType_iff_original_stable_generators M`: component 1,
  followed by the published
  `IntegerOriginalSubmoduleGeneration.finite_iff_original_stable_generators`.
  That theorem is applied with the additive group and original action stored
  in `M`, and its right side is the target's right side.
- Component 5, `noetherianObject_iff_original_stable_generators M`:
  component 3, followed by the published
  `IntegerOriginalSubmoduleGeneration.noetherian_iff_original_stable_generators`.

The closed theorems apply these to the binders `A`, the `NonUnitalRing`
instance and `M` of each component statement.

## Scope and checks

No hypothesis is added. In particular there is no original unit law,
nondegeneracy, commutativity, scalar field, finiteness, Noetherian, `Small` or
universe-relation assumption, and no universe is specialized. Zero rings,
zero carriers, zero original actions and empty finite sets are covered by the
same arguments. No global instance is declared. The only module structure
over `Unitization ℤ A` is the selected `CompatibleUnitization.module`, through
`IntegerUnitization.extendObj`.

The approved Lean service compiled the module with no errors and no warnings.
Declaration inspection of `nonUnitalModuleFiniteness` reports level parameters
`uA, uM` and only the axioms `propext`, `Classical.choice` and `Quot.sound`.

The statement is derived internal content about Renard, *Représentations des
groupes réductifs p-adiques* (French version dated 9 July 2026), Chapter I
conventions and Appendix A.I.2–A.I.3, printed pp. 248–249. That source gives
no proof of these integer comparisons. This proof follows no literature route.
It proves only the five stated comparisons and makes no claim about the
source's complex scalars, the nondegenerate-module category or the
convention for possibly nonunital Noetherian algebras.
