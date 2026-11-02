# Nagata's openness criterion

Author: Worker 1103.

Helper module for the openness of the flat locus over Noetherian rings, used for
Stacks Algebra, Lemma 10.168.1(1). It feeds the module
`Langlands.Algebra.NoetherianFlatLocusOpen`. Source: H. Matsumura,
*Commutative Ring Theory*, Theorem 24.2 (Nagata's criterion for openness),
the "if" direction only. No axioms are added; declarations live in
`Langlands.Algebra`.

## Declarations

`exists_finset_isClosed_isIrreducible_irredundant`: in a Noetherian
topological space, every closed set `C` is `⋃ t ∈ S, t` for a finite set `S`
of closed irreducible sets, none of which lies in the union of the others.
This is a standard internal step, stated for reuse. The Lean proof takes a
decomposition from Mathlib's
`NoetherianSpace.exists_finite_set_isClosed_irreducible` of minimal
cardinality (`Nat.find`). If some `T ∈ S` were contained in the union of
`S.erase T`, then `S.erase T` would be a smaller decomposition, contradicting
minimality.

`isOpen_of_stableUnderGeneralization_of_forall_exists`: let `A` be a
Noetherian ring and `U ⊆ Spec A` stable under generization. Suppose that for
every `p ∈ U` there is `f ∉ p` such that every prime `q ⊇ p` with `f ∉ q` lies
in `U`, i.e. `V(p) ∩ D(f) ⊆ U`. Then `U` is open. This is Matsumura's
condition that `U ∩ V(p)` contain a nonempty open subset of `V(p)`, phrased
with a basic open neighbourhood of `p`.

## Lean proof

It suffices that `closure Uᶜ ⊆ Uᶜ`. Write `closure Uᶜ` as an irredundant
union of closed irreducible sets `T`, and let `η` be the generic point of `T`
(`PrimeSpectrum` is quasi-sober), so `closure {η} = T`. Suppose `η ∈ U`, and
take `f` from the hypothesis. Let `W` be the closed union of the other
members. By irredundancy `T ⊄ W`, and `η ∈ D(f)`. So irreducibility of `T`
gives `z ∈ T ∩ D(f) ∩ Wᶜ`. As `z ∈ closure Uᶜ`, the open set `D(f) ∩ Wᶜ`
contains some `w ∉ U`. Since `w` lies in the union but not in `W`, `w ∈ T`,
so `η ≤ w` and `f ∉ w`. The hypothesis then gives `w ∈ U`, a contradiction.
Hence `η ∉ U`. Every `y ∈ T` is a specialization of `η`, and `U` is stable
under generization, so `y ∉ U`.
