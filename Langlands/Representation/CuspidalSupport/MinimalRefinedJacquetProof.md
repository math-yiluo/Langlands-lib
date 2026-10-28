# Nonzero quasicuspidal refined Jacquet descent in a product Levi

This module proves the published proposition
`Langlands.CuspidalSupport.MinimalNonzeroRefinedJacquetTheorem.{uF,uV} F T`
from `Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetStatement`.
The theorem is

```
theorem Langlands.CuspidalSupport.minimalNonzeroRefinedJacquet
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MinimalNonzeroRefinedJacquetTheorem.{uF, uV} F T
```

Its type is exactly the statement, with independent universe levels `uF` and
`uV`. It adds no hypotheses. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## Mathematical content

The statement says the following. Let `B` be any block shape of any rank `n`,
and let `A` be a nonzero smooth complex representation of the product Levi
`B.Levi F`, smooth for the topology `T.topology`. Then some block refinement
`S` of `B` has the following two properties.

- The full refined Jacquet coinvariant module
  `RefinedJacquetModule B S A.representation` is nonzero.
- Pull the normalized refined Jacquet action `T.normalizedRefinedJacquet` back
  along the statement's coordinate equivalence
  `BlockShape.leviRefinementEquiv (B.flatten S) B S (B.flattenBlockEquiv S) _ F.Carrier`,
  from the Levi of the flattened shape `B.flatten S` onto the refined Levi.
  The result is `IsLeviQuasicuspidal`: for every proper refinement `S'` of
  `B.flatten S`, its coinvariants for the radical of `S'` are zero.

This is the descent step at the start of BZ77 2.14(1): by 2.3(c), every nonzero
object has a nonzero quasicuspidal Jacquet module along some standard subgroup.
The source is I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups. I*, Ann. Sci. ENS 10 (1977), literature ID
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The relevant
passages are:

- 2.1–2.4 (printed p.446, PDF p.7): standard subgroups of GL as ordered
  partitions, and quasicuspidality;
- the composition identity 2.3(c), `r_{N,M} ∘ r_{M,G} = r_{N,G}`;
- the opening of 2.14(1) (printed p.449, PDF p.10).

The source works with a reductive group `G`. This proof works inside an
arbitrary product Levi `B.Levi F`. It uses the explicit nested-refinement
coordinates of the Library, not the general composition functor isomorphism.

## Implemented proof

The proof is a finite maximum argument on the number of flattened blocks. It
needs no composition isomorphism, only a surjection in one direction.

1. **A witness: the whole refinement.** `MinimalRefinedJacquet.wholeRefinement B`
   keeps each outer block `i` as a single inner block of size `B.size i`. Every
   inner shape then has one block, so each component of its refined radical is
   the identity (`unipotentRadical_val_eq_one` with `le_rfl`). This gives
   `eq_one_of_mem_refinedUnipotent_wholeRefinement`. All relations
   `ρ u w - w` therefore vanish, and `refinedJacquetMk` is injective (via
   `Jacquet.ker_mk`, `Jacquet.relations_eq_span` and `Submodule.span_eq_bot`).
   So a nonzero `V` gives a nonzero refined Jacquet module
   (`nontrivial_wholeRefinement`).

2. **Maximal choice.** Let `P k` say that some refinement `S` of `B` has
   `(B.flatten S).length = k` and a nonzero `RefinedJacquetModule B S
   A.representation`. Flattened lengths are at most `n`
   (`BlockShape.length_le`). Step 1 gives an instance of `P`, so
   `Nat.findGreatest_spec` yields a refinement `S` that attains
   `Nat.findGreatest P n` and has a nonzero refined Jacquet module. This is the
   first conjunct.

3. **Quasicuspidality by contradiction.** Let `S'` be a proper refinement of
   `B.flatten S`, so `refinedParabolic F (B.flatten S) S' ≠ ⊤`, and suppose its
   coinvariants are nonzero. Compose to get
   `B.composeRefinement S S'` from `Group.GL.NestedRefinement`. Then:
   - `BlockShape.flatten_composeRefinement` and `BlockShape.length_lt_flatten`
     show that its flattened length exceeds that of `S`;
   - `composeJacquetMap_surjective`, described below, shows that its refined
     Jacquet module is nonzero.

   Together these contradict `Nat.findGreatest_is_greatest`.

### The comparison surjection

`composeJacquetMap T B S S' ρ` is a linear map

```
RefinedJacquetModule B (B.composeRefinement S S') ρ →
  Jacquet.Coinvariants (flattenedAction T B S ρ) (refinedUnipotent F (B.flatten S) S')
```

It is induced by `v ↦ mk (refinedJacquetMk B S ρ v)`. Here
`flattenedAction T B S ρ` is, by definition (an `abbrev`), the pulled-back action
of the target statement:
`(T.normalizedRefinedJacquet B S ρ).comp (flattenLeviEquiv B S).toMonoidHom`.
Also, `flattenLeviEquiv B S` is, by definition (an `abbrev`), the statement's
exact `leviRefinementEquiv` term. The map is surjective because both quotient
maps are surjective (`Jacquet.mk_surjective`).

To show the map is well defined, take `g` in the composed refined radical. We
must show that `g` acts trivially on the iterated coinvariants
(`mk_refinedJacquetMk_composeRefinement`). This takes four steps.

- **Group coordinates.** Block `i` of the composed refinement is
  `(S i).flatten (B.refinementWithin S S' i)`, which holds by definition. So
  `BlockShape.flatten_unipotentSubgroup_le` (from
  `CuspidalSupport.MinimalJacquetProof`) and `mem_leviPreimage_iff` (from
  `Parabolic.RefinementPreimage`) give two facts about each component `g i`:
  it lies in the parabolic of `S i`, and its Levi projection lies in the refined
  radical of `B.refinementWithin S S' i`
  (`exists_mem_parabolic_of_mem_composeRefinement`). Hence `g` lies in the middle
  refined parabolic `refinedParabolic F B S`
  (`composeRefinement_refinedUnipotent_le`). Its Levi projection `m` has nested
  coordinates `(refinedLeviEquiv F B S).symm m i` in those radicals
  (`refinedLeviEquiv_symm_refinedLeviProjection`, `refinedLeviEquiv_symm_mem`).

- **Radical part.** Write `g = u · m` with `u = refinedUnipotentPart F B S q` in
  the refined radical of `S`. Then `u` dies in `RefinedJacquetModule B S ρ`
  (`Jacquet.mk_apply_subgroup`), so `[ρ g v] = [ρ m v]`.

- **Normalization.** The action is `T.normalizedRefinedJacquet`. On
  `refinedJacquetMk v` it multiplies `refinedJacquetMk (ρ m v)` by the inverse
  half-modulus `T.refinedLeviInverseHalfModulus B S m`
  (`T.normalizedRefinedJacquet_mk`). By `T.refinedLeviModulus_apply`, the full
  refined modulus is the product over `i` of the block moduli `T.leviModulus (S i)`
  at the components `refinedLeviBlock B S i m`. These components are
  definitionally the nested coordinates. Each factor is `1`, by
  `T.leviModulus_refinedUnipotent` (the block modulus is trivial on the refined
  radical inside a block Levi). This gives `refinedLeviModulus_eq_one`, and then
  `Jacquet.inverseHalfCharacter_eq_one` makes the inverse half-modulus `1`. The
  normalization is the actual inverse half-modulus. It is neither removed nor
  assumed; it is shown to be trivial on these particular elements.

- **Coordinate transport.** It remains to show that
  `(flattenLeviEquiv B S).symm m` lies in
  `refinedUnipotent F (B.flatten S) S'` (`flattenLeviEquiv_symm_mem`). Every
  flattened block is `B.flattenBlockEquiv S ⟨i, j⟩`. The inverse of
  `leviRefinementEquiv` is `nestedLeviEquiv.symm ∘ refinedLeviEquiv.symm` by
  definition. `BlockShape.nestedLeviEquiv_symm_apply` writes that block as
  `reindex (finCongr _)` of coordinate `j` of `(refinedLeviEquiv F B S).symm m i`.
  The latter lies in the radical of `S' (B.flattenBlockEquiv S ⟨i, j⟩)`,
  rank-cast to `(S i).size j`; this rank cast is the definition of
  `refinementWithin`. The local lemma `reindex_mem_unipotentSubgroup`, proved by
  `subst` on the rank equality, removes the cast. Then `m` acts with factor `1`
  and lies in the radical of `S'`, so it dies in the iterated coinvariants.

## Cases and universes

- **All ranks and the empty shape.** No case split is made. For rank zero and the
  empty shape, the whole refinement is the empty family and the same argument
  applies. These are elementary internal extensions; BZ77 does not discuss
  `GL_0`. Whole-product refinements arise as the witness of step 1.
- **Topology.** The proof binds `T.topology` before introducing the
  representation. The smoothness topology is therefore exactly the one the
  statement uses. Smoothness itself is not needed by the argument.
- **Universes.** The theorem is universe-polymorphic in independent `uF` and
  `uV`, and the quotient stays in `uV`. A closing `example` checks the
  specialization `MinimalNonzeroRefinedJacquetTheorem.{uF, max uF uV}`.
- **No extra hypotheses.** The theorem assumes no irreducibility, admissibility,
  finite generation or finite length, finite dimension, central character,
  positive rank, tensor factorization, embedding, chosen refinement, or
  transitivity statement.

## Local declarations

All are in namespace `Langlands.CuspidalSupport.MinimalRefinedJacquet`:

- `reindex_mem_unipotentSubgroup`: reindexing along a rank equality carries the
  radical of a rank-cast shape into the radical of the original shape;
- `wholeRefinement` and `eq_one_of_mem_refinedUnipotent_wholeRefinement`;
- `exists_mem_parabolic_of_mem_composeRefinement`,
  `composeRefinement_refinedUnipotent_le`,
  `refinedLeviEquiv_symm_refinedLeviProjection` and `refinedLeviEquiv_symm_mem`:
  group coordinates of composed radical elements;
- `flattenLeviEquiv` (an abbreviation for the statement's equivalence) and
  `flattenLeviEquiv_symm_mem`;
- `refinedLeviModulus_eq_one`;
- `flattenedAction` (an abbreviation for the statement's pulled-back action),
  `mk_refinedJacquetMk_composeRefinement`, `composeJacquetMap`,
  `composeJacquetMap_surjective` and `nontrivial_composeRefinement`;
- `nontrivial_wholeRefinement`.

## Imports and independence audit

The module imports only:

- the statement module `Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetStatement`,
  which is left unchanged along with all of its imports;
- `Langlands.Group.GL.NestedRefinement`, which itself imports only
  `Langlands.Representation.CuspidalSupport.MinimalJacquetProof`. That module is
  already in the statement's import closure.

So the project import closure is the statement's 63 modules plus
`Group.GL.NestedRefinement`, 64 in all. Its only Classification modules are
`Classification.Supercuspidal` and `Classification.SupercuspidalTwist`. None of
these modules is a conclusion, proof successor or transitive proof dependency of
any excluded task:

- analytic segment classification `aca8805b`;
- special-head multisegment exhaustion `3bfb61fa`;
- ordered strong-head existence `ebea9a8a`;
- quotient coverage `20e4e1c6`;
- tempered block uniqueness `52e97845`;
- `SquareIntegrableLanglandsClassification` / `1cb45da2`;
- square-integrable exhaustion `cd8ab97c`;
- regular exhaustion `bf433f0a`.

The proof also uses no results of the arbitrary irreducible-Levi task
`3b437c95`, the finite-length admissibility task `d9898ee2`, the parabolic
finite-length task `2a216dfa`, or the upper/opposite refinement-transitivity
task `32edfd0a`. From `CuspidalSupport.MinimalJacquetProof` it reuses only
group-level material in namespace `GeneralLinear.BlockShape`:

- the shape constructions `BlockShape.flatten` and `BlockShape.flattenBlockEquiv`,
  which the statement itself uses;
- the lemmas `BlockShape.flatten_size_flattenBlockEquiv`,
  `BlockShape.length_lt_flatten`, `BlockShape.flatten_unipotentSubgroup_le` and
  `BlockShape.unipotentRadical_val_eq_one`.

It uses nothing from namespace `CuspidalSupport.MinimalJacquet`, in particular
neither the GL-input theorem `minimalNonzeroJacquet` nor `flattenJacquetMap`.
