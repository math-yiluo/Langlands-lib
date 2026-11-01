# Proof of the completed submodule inclusion and the ranges of Renard I.1.5.3

Author: Worker 1125 (Lean proof and this explanation).

This module proves the published closed proposition
`Langlands.Algebra.NonUnitalModuleCompletionSubmoduleTheorem.{uA,uM}` from
`Langlands.Algebra.NonUnitalModuleCompletionSubmoduleStatements`, for
exact-target proof task `6468e0c5-0007-44c1-b87b-96f1d4c19ab4`. The final theorem
is `Langlands.Algebra.nonUnitalModuleCompletionSubmoduleTheorem_proof`. It is
stated at arbitrary independent universes `uA` and `uM` and has exactly the type
`NonUnitalModuleCompletionSubmoduleTheorem.{uA, uM}`. The statement module and
its imports are used by Lean name and are not changed. The proof adds no
hypotheses and no axioms beyond Lean's standard `propext`, `Classical.choice`
and `Quot.sound`.

## Source remark and internal package

The original is David Renard, *Représentations des groupes réductifs p-adiques*
(French version dated 9 July 2026), the remark after the I.1.5 proposition,
formula (I.1.5.3), printed p.11/PDF17. It says that for a nondegenerate `M` and
a submodule `N`, the completion of `N` is the closure of `N` in the completion of
`M`, and it gives two descriptions of this subset: the families `n̄` with
`n̄(e) ∈ e·N` for every idempotent `e`, and the families with `A·n̄ ⊂ N`. The
source prints no proof.

The target splits this into two parts, and this proof keeps them apart.

- `NonUnitalModuleCompletionSubmoduleRange hA M S` is the source remark. Its
  three set equalities identify the range of the actual completed inclusion
  `j = NonUnitalModuleLeftLimit.mapHom hA S.subtype` with the closure of the
  canonical image of `S` and with each displayed description.
- `NonUnitalModuleCompletionSubmoduleInclusion hA M S` is internal packaging
  rather than a numbered claim of the source. It spells out how the completed
  submodule is identified with its image: `j` has additive map `mapAddHom S.subtype`, it is
  injective, it is a uniform embedding for the two coordinate uniformities,
  and its range is closed.

Both parts are proved for the fixed structures installed by the target: the
completed actions `NonUnitalModuleLeftLimit.nonUnitalModule hA` on
`NonUnitalModuleLeftLimit A S` and `NonUnitalModuleLeftLimit A M`, the
coordinate uniformities `NonUnitalModuleLeftLimit.uniformSpace A S` and
`NonUnitalModuleLeftLimit.uniformSpace A M`, and their topologies.

## The central set

Every assertion is reduced to one set of ambient families,

`R = {x : NonUnitalModuleLeftLimit A M | ∀ e : Idempotent A, x.val e ∈ S}`,

the families all of whose coordinates lie in `S`.

`nonUnitalModuleCompletionSubmodule_range_mapAddHom` proves
`range (mapAddHom S.subtype) = R`. A family in the image has coordinates
`(y.val e : M)` with `y.val e ∈ S`. Conversely, if every coordinate of `x` lies
in `S`, the family `e ↦ ⟨x.val e, _⟩` of `S` satisfies the two left-compatibility
conditions, because those conditions hold for `x` and equality in the subtype is
equality in `M` (`Subtype.ext`). Its image is `x` by definition.

## Inclusion package

The equality `(mapHom hA S.subtype).toAddMonoidHom = mapAddHom S.subtype` holds
by `rfl`, so all further statements about `mapHom hA S.subtype` are proved for
`mapAddHom S.subtype`.

- Injectivity (`nonUnitalModuleCompletionSubmodule_mapAddHom_injective`): if two
  families of `S` have the same image, then their coordinates are equal in `M`,
  hence in `S`.
- Uniform embedding (`nonUnitalModuleCompletionSubmodule_comap_uniformSpace` and
  `nonUnitalModuleCompletionSubmodule_isUniformEmbedding`): the published
  `NonUnitalModuleLeftLimitUniformity` lemma `uniformity_eq` writes both
  coordinate uniformities as the infimum over idempotents `e` of the
  principal filters of the coordinate entourages `{(x, y) | x.val e = y.val e}`.
  The pullback of the ambient uniformity along `mapAddHom S.subtype` is computed
  by `uniformity_comap`, `Filter.comap_iInf` and `comap_principal`. The
  preimage of the ambient `e`-entourage is the `e`-entourage of `S`, because
  equality of the included coordinates in `M` is equality in `S`. So the pullback is
  the uniformity of `S`. Mathlib's `isUniformInducing_iff_uniformSpace`
  turns this into uniform inducing, and with injectivity it gives
  `IsUniformEmbedding`.
- Closed range (`nonUnitalModuleCompletionSubmodule_isClosed_range`): the range
  equals `R`, which equals the closure of the canonical image of `S` (next
  section), and every closure is closed.

## Range equalities

All three use `range (mapHom hA S.subtype) = R` from the central set section.

1. Closure. `nonUnitalModuleLeftLimit_mem_closure_iff` uses the published
   neighborhood basis `NonUnitalModuleLeftLimit.nhds_hasBasis hA`. Each family `x` has the
   basic neighborhoods `{y | y.val e = x.val e}`, and Mathlib's
   `mem_closure_iff_nhds_basis` gives: `x` lies in the closure of `T` exactly
   when for every idempotent `e` some `y ∈ T` has `y.val e = x.val e`.
   `nonUnitalModuleCompletionSubmodule_closure_canonical` applies this to
   `T = canonical '' S`. If `x` is in the closure, then for each `e` there is
   an `m ∈ S` with `x.val e = e • m`, and this lies in `S` because `S` is stable
   under the action. Conversely, for `x ∈ R` and each `e`, the vector
   `x.val e ∈ S` works, since the `e` coordinate of `canonical (x.val e)` is
   `e • x.val e = x.val e` by the fixed-point condition on `x`. The topological
   arguments use `IsIdempotented A` only through this neighborhood basis. The
   uniform embedding does not use it.
2. Coordinates in `e • S`
   (`nonUnitalModuleCompletionSubmodule_coordinate_eq_exists`). If
   `x.val e ∈ S`, then the witness is `n = x.val e`, and `e • n = x.val e` is
   the fixed-point condition. If `x.val e = e • n` with `n ∈ S`, then
   `x.val e ∈ S` by stability.
3. Scalar translates in the canonical image
   (`nonUnitalModuleCompletionSubmodule_coordinate_eq_smul`). The action
   `a • x` here is the installed completed action, `scalarAction hA a x`.
   - For `x ∈ R` and `a : A`, the published local-unit characterization
     `IsIdempotented.iff_two_sided_local_units`, applied to `{a}`, gives an
     idempotent `f` with `a * f = a`. Put `n = a • x.val f`, which lies in `S`.
     For every `e`, `(e * a) * f = e * a`, so the published
     `scalarAction_val` gives the `e`-coordinate of `a • x` as
     `(e * a) • x.val f = e • (a • x.val f)`. This is the `e`-coordinate of
     `canonical n`. Hence `a • x = canonical n`.
   - Conversely, take `a = e`. The published `idempotent_scalarAction` gives
     `e • x = canonical (x.val e)`. By hypothesis this equals `canonical n` for some
     `n ∈ S`. Comparing `e`-coordinates gives `e • n = e • x.val e = x.val e`, so
     `x.val e ∈ S`.

## Assembly and the nondegeneracy premise

`nonUnitalModuleCompletionSubmoduleInclusion_proof` and
`nonUnitalModuleCompletionSubmoduleRange_proof` unfold the two per-action
targets with `delta`. They introduce the six installed structures and supply the
results above. They hold for every original action of an idempotented ring, not
only nondegenerate ones. The master theorem introduces all the data and
the premise `IsNondegenerate A M`, then returns both packages. The target keeps
the nondegeneracy premise of the source remark, but this argument never uses it.
The proof does not use injectivity of the canonical map, and the third
range equality is proved by comparing coordinates.

The trailing `example`s check the full unapplied interfaces of the two
per-action proofs and the master at general independent universes. They also
instantiate the master at `(uA, uM) = (0, 1)` and `(1, 0)`.

Out of scope here are recovery and faithfulness, the smoothing/completion adjunction,
analytic completion, right-ring completion, endomorphism descriptions and the rest
of I.1.5.
