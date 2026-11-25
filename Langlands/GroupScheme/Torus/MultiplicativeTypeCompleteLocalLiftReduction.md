# Reduction of lifting over complete local rings to adic lifting

This internal helper module reduces
[`MultiplicativeTypeCompleteLocalLiftStatement`](MultiplicativeTypeCompleteLocalLiftStatement.md)
(Conrad, *Reductive group schemes*, Corollary B.3.5, p.292) to two other published
statements:

- [`MultiplicativeTypeQuasiIsotrivialStatement`](MultiplicativeTypeQuasiIsotrivialStatement.md)
  (Conrad, Proposition B.3.4). Its clause (2) says that a group of multiplicative type
  over a Henselian local ring splits after a finite étale surjective base change. It is
  proved in the Library as `multiplicativeTypeQuasiIsotrivial`
  ([`MultiplicativeTypeQuasiIsotrivialProof`](MultiplicativeTypeQuasiIsotrivialProof.md)).
- [`MultiplicativeTypeAdicLiftStatement`](MultiplicativeTypeAdicLiftStatement.md)
  (SGA 3, IX, 7.3). It lifts homomorphisms from isotrivial groups over adically complete
  noetherian rings, uniquely up to conjugacy. This module does not prove it; it stays an
  explicit hypothesis.

The module proves no unconditional form of Corollary B.3.5. Its last theorem shows that
the corollary follows from `MultiplicativeTypeAdicLiftStatement` alone.

## `henselianLocalRing_of_isAdicComplete`

A local ring `A` that is `maximalIdeal A`-adically complete is a `HenselianLocalRing`.
Mathlib's instance gives `HenselianRing A (maximalIdeal A)` from `IsAdicComplete`. The
Henselian local ring condition asks for a root lifting `a₀` of a monic `f` with
`f(a₀) ∈ 𝔪` and `f'(a₀)` a unit. `HenselianRing.is_henselian` needs `f(a₀) ∈ 𝔪` and
`f'(a₀)` a unit modulo `𝔪`, which is the image of the unit `f'(a₀)` under the quotient map.

## `multiplicativeTypeCompleteLocalLift_of_quasiIsotrivial_of_adicLift`

Assume `hQ : MultiplicativeTypeQuasiIsotrivialStatement.{u}` and
`hA : MultiplicativeTypeAdicLiftStatement.{u}`. Then
`MultiplicativeTypeCompleteLocalLiftStatement.{u}` holds. Let `A` be a complete local
noetherian ring, `G` a smooth affine group and `H` a group of multiplicative type over
`Spec A`.

1. `A` is a Henselian local ring by `henselianLocalRing_of_isAdicComplete`, so clause (2)
   of `hQ` gives a finite étale surjective `p : S' ⟶ Spec A` with `H_{S'}` diagonalizable.
2. Apply `hA` with the ideal `I = maximalIdeal A` and this splitting. Its morphism
   `r = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk 𝔪))` is definitionally the closed
   point `Spec.algebraMap A (ResidueField A)` of the target statement, because
   `ResidueField A` is `A ⧸ 𝔪` and its algebra map is the quotient map. So the two
   conclusions of `hA` are exactly clauses (1) existence of lifts and (2) conjugacy of
   lifts, with no transport.
3. Clause (3), closed immersions, is
   `MultiplicativeTypeLocalClosed.isClosedSubgroup_of_isotrivial` (module
   [`MultiplicativeTypeLocalClosed`](MultiplicativeTypeLocalClosed.md)) applied to the
   same splitting. It uses only that `A` is local and `G` is affine.

## `multiplicativeTypeCompleteLocalLift_of_adicLift`

Assume `hA : MultiplicativeTypeAdicLiftStatement.{u}`. Then
`MultiplicativeTypeCompleteLocalLiftStatement.{u}` holds: apply the previous theorem with
`hQ := multiplicativeTypeQuasiIsotrivial`.

## Provenance

Conrad notes that Corollary B.3.5 is a special case of SGA 3, IX, 7.3 (p.292). His proof
(pp.292–293) invokes Proposition B.3.4 so that the bijectivity of the comparison map
(B.3.1) applies, builds the lifts step by step over `A/𝔪^{n+1}` and passes to the limit.
Here those steps are left to the proof of `MultiplicativeTypeAdicLiftStatement`, the
`I`-adic form of SGA 3, IX, 7.3 used in the Library, and B.3.4 enters through its
clause (2). The closed-immersion clause is proved by a different route (see
[`MultiplicativeTypeLocalClosed`](MultiplicativeTypeLocalClosed.md)); Conrad uses
Lemma B.1.3, Nakayama's lemma and reduction to a discrete valuation ring. The assembly of
the three clauses from these inputs is the author's own.
