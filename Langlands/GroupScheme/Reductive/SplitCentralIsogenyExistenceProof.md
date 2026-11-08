# The central split Isogeny Theorem

`Langlands.GroupScheme.splitCentralIsogenyExistence` proves the published proposition
`Langlands.GroupScheme.SplitCentralIsogenyExistenceStatement.{u}` (module
`Langlands.GroupScheme.Reductive.SplitClassificationStatement`): the Isogeny Theorem, central
case, of Milne, *Algebraic Groups* (2017), Theorem 23.9. Let `i : T ⟶ G` and `i' : T' ⟶ G'` be
split maximal tori of connected reductive groups over a field `k : Type u`, with root data `P` and
`P'`. Then every morphism of root pairings `f : P' ⟶ P` with injective weight map
`X(T') → X(T)` and injective coweight map `Y(T) → Y(T')` comes from a central isogeny
`φ : G ⟶ G'` and a torus homomorphism `t : T ⟶ T'` such that `i ≫ φ = t ≫ i'` and
`f χ = t ≫ χ` for every character `χ` of `T'`.

The theorem has no hypotheses. It keeps the field arbitrary, of any characteristic, and keeps the
original universe `u`.

## Proof

The proof is a single application of the published reduction
`splitCentralIsogenyExistence_of_commonTorusIsomorphism` (module
`Langlands.GroupScheme.Reductive.SplitCentralIsogenyReduction`). That reduction derives the
target from four published propositions. Each of them now has a published unconditional proof,
and the theorem passes those proofs in:

1. `rootDatumExistence : RootDatumExistenceStatement.{u}` (module
   `Langlands.GroupScheme.Reductive.RootDatumExistence`, Milne Theorem 21.11 and
   Corollary 21.12): every split maximal torus of a connected reductive group has a finite
   reduced root datum.
2. `centralIsogenyRootDatumHom : CentralIsogenyRootDatumHomStatement.{u}` (module
   `Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof`, Milne Proposition 23.5, central
   case): a central isogeny `φ : G ⟶ G'` with `i ≫ φ = t ≫ i'` for split maximal tori induces a
   morphism of root pairings `P' ⟶ P` with weight map `χ ↦ t ≫ χ` and coweight map
   `ν ↦ ν ≫ t`.
3. `splitCentralTorusQuotient : SplitCentralTorusQuotientStatement.{u}` (module
   `Langlands.GroupScheme.Reductive.CentralTorusQuotientProof`): if `t : T ⟶ T'` maps to a split
   torus, is injective on character and cocharacter lattices, and every root of `i` has the form
   `t ≫ α'`, then there are a connected reductive group `Q`, a central isogeny `q : G ⟶ Q` and a
   maximal torus `i'' : T' ⟶ Q` with `i ≫ q = t ≫ i''`.
4. `splitCommonTorusIsomorphism : SplitCommonTorusIsomorphismStatement.{u}` (module
   `Langlands.GroupScheme.Reductive.SplitIsomorphismProof`, Milne Remark 23.26): if two connected
   reductive groups have maximal tori `i₁`, `i₂` with the same split torus, and root data of `i₁`
   and `i₂` differ by a reindexing that matches roots and coroots, then there is an isomorphism
   `ψ` of the groups with `i₁ ≫ ψ.hom = i₂`.

Inside the reduction, `t : T ⟶ T'` is the torus map whose character pullback is the weight map of
`f`. Its lattice maps are the weight and coweight maps of `f`, so they are injective, and every
root of `i` is `t ≫ α'` for a root `α'` of `P'`. Item 3 then gives the central isogeny
`q : G ⟶ Q` and the maximal torus `i'' : T' ⟶ Q`. Item 1 gives a root datum `P''` of `i''`, and
item 2 gives a morphism `P'' ⟶ P` with weight map `χ ↦ t ≫ χ` and coweight map `ν ↦ ν ≫ t`.
The morphism `f : P' ⟶ P` has the same weight and coweight maps. Reindexing along
`J'' ≃ J ≃ J'`, the roots of `P''` and `P'` agree because this weight map is injective, and
their coroots agree because both coroot families are images of the coroots of `P` under the
coweight map. Item 4 gives an isomorphism `ψ : Q ≅ G'` with `i'' ≫ ψ.hom = i'`. The theorem takes
`φ = q ≫ ψ.hom`, which is a central isogeny, and `t` as the torus map.

`lean_check` builds the module with no errors or warnings. The theorem depends only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.
