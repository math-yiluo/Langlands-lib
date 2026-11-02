# Detection of zero on `Alg({I})` from detection on irreducible members

Implementation and documentation: Worker 379 (task
`0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4`).

This module proves one implication between the targets of
`SupportCategoryStatements`, and two generic lemmas used for it. It asserts no
target.

## Generic lemmas

* `subtype_mkQ_isShortExact A S`: for a smooth complex representation `A` and an
  invariant subspace `S`, the inclusion `SmoothRep.subtype A S` and the quotient
  map `SmoothRep.mkQ A S` form an actual short exact sequence in the sense of the
  Library's `SmoothRep.IsShortExact` (injective, surjective, range equals kernel).
  The kernel computation is `Submodule.Quotient.mk_eq_zero`. This holds for any
  topological group.
* `jacquet_subsingleton_of_isSubquotient h hU hUc hπ hE`: let
  `h : IsSemidirectDecomposition P M U` with `U` closed (`hU`) and a limit of
  compact subgroups (`hUc : Jacquet.Localization.IsLimitOfCompactSubgroups U`).
  If `π` is a subquotient of `E` and the normalized Jacquet module
  `(jacquetFunctor h hU).obj E` is zero, then so is
  `(jacquetFunctor h hU).obj π`. Write `π ≅ S/T` with `T ⊆ S ⊆ E`. Worker 23's
  `jacquetFunctor_map_isShortExact` (exactness of the normalized Jacquet functor
  on every short exact sequence, under `hUc`) applied to `S ↪ E ↠ E/S` makes
  `r(S) → r(E)` injective, so `r(S)` is zero. Applied to `T ↪ S ↠ S/T`, it makes
  `r(S) → r(S/T)` surjective, so `r(S/T)` is zero. Finally `r(π) ≅ r(S/T)`.

## The reduction

`supportCategoryZeroDetection_of_irreducibleJacquetDetection hUc hdet`: if every
`U J` is a limit of compact subgroups and
`SupportCategoryIrreducibleJacquetDetectionTarget P M U h hU hM hL IsAssociate`
holds, then `SupportCategoryZeroDetectionTarget P M U h hU hM hL IsAssociate`
holds (both at the same universes).

Proof. Let `E ∈ Alg({I})` have zero Jacquet modules along every associated
standard Levi, and suppose `E` is nonzero. By
`SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` it has an
irreducible subquotient `π`. By `IsInSupportCategory.of_isSubquotient`, `π` lies
in `Alg({I})`. The detection target gives `J`, `n` with `L_J` associated to `L_I`
through `n` and `r_J(π)` nonzero. But `r_J(E)` is zero by hypothesis, so `r_J(π)`
is zero by the second lemma, a contradiction.

The hypothesis `hUc` holds for the unipotent radicals of parabolic subgroups of a
reductive group over a nonarchimedean local field (Renard V.5.2 (iii), printed
p. 123, used for the same purpose in Worker 23's adapter). In this generic module
it is a hypothesis.

No declaration uses axioms beyond Lean's standard ones.
