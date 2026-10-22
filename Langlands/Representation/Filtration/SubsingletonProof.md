# Proof of the finite-filtration zero criterion

Author: Worker 221.

This pair proves the exact Library proposition
`Langlands.ObjectRepFiltrationSubsingletonStatement` from
`Langlands.Representation.Filtration.VanishingStatement`, as the theorem
`Langlands.objectRepFiltrationSubsingleton`. The universes `uR`, `uG` and
`uV` of the ring, monoid and carrier stay independent, as in the
statement. The statement pair and everything it imports are unchanged.

## Provenance

The statement is an internal derived criterion behind Bernstein and
Zelevinsky, *Induced representations of reductive p-adic groups. I*,
Ann. Sci. ENS (4) 10 (1977), Corollary 2.13(a),(b) (printed p.449), where
finite gluing (§1.11, printed p.445) is used through its actual successive
quotients. The article gives no separate proof of this elementary fact; the
proof below is the standard one and is the one implemented.

## Implemented proof

Write `S_k`, for `k : Fin (r + 1)`, for the invariant subspaces
`s.subrepresentation k` of the filtration `s` of `A`, so that `S_0 = ⊥`
and `S_r = ⊤`.

1. `ObjectRepFiltration.gradedProjection_eq_zero_iff`. For `i : Fin r`
   and a vector `v` of `S_(i+1)`, the class of `v` under the actual graded
   projection `s.gradedProjection i` is zero exactly when `v` lies in
   `S_i`. This is `Submodule.Quotient.mk_eq_zero`, since the graded quotient
   is by definition the quotient of `S_(i+1)` by the inverse image of `S_i`.
2. `ObjectRepFiltration.subrepresentation_succ_le_of_subsingleton`. If the
   `i`th graded representation is a subsingleton, every class in it equals
   zero, so step 1 gives `S_(i+1) ≤ S_i`.
3. `ObjectRepFiltration.subrepresentation_eq_top_of_subsingleton`. If all
   graded representations are subsingletons, then `S_k = ⊤` for every `k`.
   The proof is downward induction with `Fin.reverseInduction`: the case
   `k = r` is the endpoint `subrepresentation_last`, and if `S_(i+1) = ⊤`
   then step 2 gives `⊤ ≤ S_i`.
4. `Langlands.objectRepFiltrationSubsingleton`. Step 3 at `k = 0`, combined
   with the endpoint `subrepresentation_zero`, gives `⊥ = ⊤` as
   subrepresentations of `A`. Hence every vector of `A`, being in `⊤`, is in
   `⊥` and equals zero, so any two vectors of `A` are equal.

The case `r = 0` needs no separate treatment: the induction then has only
its base case, and the endpoints give `⊥ = ⊤` directly. No hypothesis beyond
the statement's is used; in particular no field, topology, smoothness or
finiteness assumption appears.

## Axioms

`lean_check` inspection reports only `propext`, `Classical.choice` and
`Quot.sound`.
