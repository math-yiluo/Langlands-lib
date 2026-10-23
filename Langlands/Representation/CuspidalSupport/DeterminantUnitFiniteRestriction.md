# Finite irreducible restriction to the determinant-unit subgroup of a product Levi

This internal module proves the reduced spanning form of Bernstein–Zelevinsky 1976,
Lemma 3.26, for the product Levi `B.Levi F.Carrier` of a block shape `B` over a
`p`-adic field `F`. Let `D` be an irreducible smooth complex representation. Its
restriction to the determinant-unit subgroup `G°` is semisimple and is spanned by
finitely many irreducible subrepresentations. Only irreducibility of `D` is assumed:
no cuspidality, admissibility, central character or finite dimension. The
declarations are in namespace `Langlands.CuspidalSupport.FiniteRestriction`.

The topology on `F.Carrier` is `T.topology` for the given `F.TopologicalData` `T`,
installed with `letI` in the statements. Its valuative relation `T.valuativeRel` and
local-field structure `T.localField` are installed inside the proofs.

## The centre acts by scalars

`exists_scalar_center T B ρ` states: for every representation `ρ` of
`B.Levi F.Carrier` on a complex vector space `V` (in any universe `uV`), if `ρ` is
smooth and irreducible, then every element `z` of `Subgroup.center (B.Levi F.Carrier)`
acts by a scalar `c : ℂ`, that is, `ρ z v = c • v` for all `v`.

The proof uses three published lemmas of
`Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof`
(namespace `Langlands.CuspidalSupport.LeviAdmissibility`):

1. Choose a uniformizer `ϖ` with the published `Iwasawa.exists_isUniformizingElement`.
2. The block Cartan decomposition `exists_levi_cartan` writes every element of the
   Levi as `k₁ * leviTorus B ϖ lam * k₂` with `k₁, k₂` in the compact open subgroup
   `integralLevi B` (compact by `isCompact_integralLevi`). The torus elements form a
   countable set, so the Levi is covered by countably many double cosets.
3. `rank_le_aleph0_of_doubleCoset_cover` then bounds the dimension of an irreducible
   smooth `ρ` by `ℵ₀`.
4. `exists_scalar_of_central` applies Schur's lemma in countable dimension (the
   published `Langlands.countableDimensionalSchur`) to the intertwiner `ρ z`.

This is how admissibility is avoided. BZ76 cite Schur's lemma for this step. Their
Schur lemma, Proposition 2.11 (p. 18), is also proved through countable dimension,
for groups that are countable at infinity. Here the countable dimension is
obtained from the Cartan decomposition instead.

## The finite restriction

`leviFiniteRestriction F T B` states, after `letI := T.topology`: for every
`D : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier)` with `D.IsIrreducible`, let
`ρD := determinantUnitRestriction T B D.representation`. Then

- `Representation.IsSemisimpleRepresentation ρD`, and
- there are `m : ℕ` and `V : Fin m → Subrepresentation ρD` such that every
  `(V i).toRepresentation` is irreducible and `⨆ i, (V i).toSubmodule = ⊤`.

The universes `uF` of the field and `uV` of the carrier are independent. The finite
family is a finite family of irreducible invariant subspaces whose sum is the whole
carrier. The carrier itself need not be finite-dimensional, and the sum is not
claimed to be direct.

Proof. The published `determinantUnitSubgroup T B` is normal
(`determinantUnitSubgroup_normal`). The published
`determinantUnit_sup_center_finiteIndex T B` gives finite index of
`determinantUnitSubgroup T B ⊔ Subgroup.center (B.Levi F.Carrier)`. The published
`determinantUnitRestriction T B ρ` is by definition
`ρ.comp (determinantUnitSubgroup T B).subtype`. The generic
`Langlands.FiniteIndexRestriction.finite_irreducible_restriction` from
`Langlands.Representation.Category.FiniteIndexRestriction` then applies with
`hscalar` given by `exists_scalar_center`.

The proof treats every rank `n`, including `n = 0`, uniformly. For `n = 0` the
product Levi is an empty product and hence trivial, and nothing special is needed.

## Use and provenance

This is BZ76 (`bernstein-zelevinsky-1976-representations-gln`) Lemma 3.26, p. 36.
Their proof cites 2.9 (Clifford, p. 17) and 3.20(b) (`G/G°·Z` is finite, p. 34) to
decompose `E` over `G°·Z`, and Schur's lemma to make the centre act by scalars. The
formal proof follows the same route. It replaces the direct-sum conclusion by
semisimplicity together with a finite spanning family of irreducibles. The
countable-dimension argument for Schur is from the published Levi admissibility
proof.

The statement matches the finite-family clauses of
`Langlands.CuspidalSupport.LeviCuspidalBlockIsolationTheorem`, whose proof task
`cae15ca4` uses it. It also matches the planned statement task `5c2d84e5`
(`LeviFiniteRestrictionTheorem`), which is not yet published.
