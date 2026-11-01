# Proof of the common strictly upper triangular basis for commuting nilpotents

This module proves the proposition
`Langlands.CommutingNilpotentStrictUpperBasisStatement.{uK,uV,uI}` from the
module `Langlands.LinearAlgebra.CommutingNilpotentStrictUpperBasisStatement`.
The statement pair is unchanged.

## Main theorem

`Langlands.CommutingNilpotentStrictUpperBasis.commutingNilpotentStrictUpperBasis :
CommutingNilpotentStrictUpperBasisStatement.{uK, uV, uI}`.

For a field `K`, a finite-dimensional `K`-vector space `V`, an arbitrary index
type `I` and a family `N : I → Module.End K V` of pairwise commuting nilpotent
endomorphisms, it produces a basis `b` indexed by `Fin (Module.finrank K V)` with
`b.repr (N t (b j)) i = 0` whenever `j ≤ i`. No extra hypothesis is used: the
field is arbitrary (no algebraic closedness or characteristic condition), the
index type may be empty or infinite, `V` may be zero, and no uniform nilpotence
bound is assumed.

## Helper results

Both helpers are in the namespace `Langlands.CommutingNilpotentStrictUpperBasis`.

1. `exists_dual_ne_zero_forall_apply_eq_zero`: if moreover `V` is nontrivial,
   there is a nonzero functional `φ : Module.Dual K V` with `φ (N t v) = 0` for
   all `t` and `v`. The transposes `(N t).dualMap` commute (by
   `LinearMap.dualMap_comp_dualMap`) and are nilpotent (by
   `Langlands.DualEigenfunctional.dualMap_pow_apply`). The dual space is
   nontrivial because its dimension equals that of `V`
   (`Subspace.dual_finrank_eq`). The published lemma
   `Langlands.DualEigenfunctional.exists_ne_zero_forall_apply_eq_zero` then gives
   a nonzero `φ` killed by every transpose, which says exactly that `φ ∘ N t = 0`.
2. `exists_basis_mem_span_aux d`: if `finrank K V = d`, there is a basis
   `b : Basis (Fin d) K V` such that `N t (b j)` lies in the span of the vectors
   `b i` with `i < j`. The proof is by induction on `d`.
   - For `d = 0`, any basis from `Module.finBasisOfFinrankEq` works, since
     `Fin 0` is empty.
   - For `d + 1`, `V` is nontrivial, so helper 1 gives `φ`. Its kernel `H` has
     dimension `d` (`Module.Dual.finrank_ker_add_one_of_ne_zero`) and contains
     every range `N t V`. In particular every `N t` maps `H` into itself. The
     restrictions commute (`LinearMap.restrict_commute`) and are nilpotent
     (`Module.End.pow_restrict`). The induction hypothesis gives a basis `b'` of
     `H` with the span property. Choose `y` with `φ y ≠ 0` and extend `b'` by `y`
     in the last position with `Module.Basis.mkFinSnoc`. The two side conditions
     hold because `c • y + x = 0` with `x ∈ H` forces `c = 0`, and
     `z - (φ z / φ y) • y ∈ H` for every `z`. By `Module.Basis.coe_mkFinSnoc`
     the new basis is `Fin.snoc (b' as vectors of V) y`. Proceed by cases on
     the index (`Fin.lastCases`).
     - For the last vector, `N t y` lies in `H`. `H` is the image of the span of
       `b'`, hence lies in the span of all earlier vectors
       (`Submodule.apply_mem_span_image_of_mem_span`).
     - For an earlier index `k.castSucc`, `N t (b' k)` agrees with the
       restricted map applied to `b' k`. Mapping the induction hypothesis
       through the inclusion `H → V` gives the span property, because
       `Fin.castSucc` preserves `<`.

## Final step

Apply helper 2 with `d = finrank K V`. For `j ≤ i`, `Module.Basis.mem_span_image`
says that the support of `b.repr (N t (b j))` lies in `{i | i < j}`. So the
coordinate at `i` must vanish, since `i < j` contradicts `j ≤ i`.

## Imports

`Mathlib.LinearAlgebra.Basis.Fin`, `Mathlib.LinearAlgebra.Dual.Lemmas`, the
published module `Langlands.Representation.Exponents.DualEigenfunctionalExistence`
and the statement module.

## Provenance

Worker 846 wrote this proof. The route dualizes, takes a common invariant
hyperplane, inducts on dimension and appends a vector. It is a standard
argument and an internal linear-algebra tool. Renard 2026, Appendix C.III
(printed pp. 279–280, PDF pp. 285–286), uses such a common triangular basis
without proving that it exists.
