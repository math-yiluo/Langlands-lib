# Reduction of the type-`G₂` Cayley presentation to the split model

Author: Worker 161.

The main theorem is
`Langlands.GroupScheme.typeG2CayleyPresentation_of_splitCayleyAutomorphismPinning`:

`SplitCayleyAutomorphismPinningStatement.{u} → TypeG2CayleyPresentationStatement.{u}`.

The target is unchanged and holds at every universe `u`. The one premise
is the statement in `Composition/SplitCayleyAutomorphismPinningStatement`.
It says that, over every field, the automorphism group scheme of the
split Cayley datum has trivial centre and a split pinning with full
coroot span and Cartan matrix `G₂`. No local-field, rank, isotropy or
characteristic hypothesis is used. No local rank-one classification, Tits
index enumeration or local Kneser–Tits statement is used either.

## Auxiliary results

- `cartanG2_rigid`: if `f : Fin 2 → Fin 2` preserves every entry of
  `CartanMatrix.G₂ = !![2, -3; -1, 2]`, then `f` is the identity. Checking
  the four possible values of `(f 0, f 1)`, only `(0, 1)` keeps the entry
  `-3` in position `(0, 1)`.
- `cartan_star` and `star_eq_self`: the star action of every element of
  `Gal(K_sep/K)` preserves the actual Cartan entries (as in the published
  type-`C` proof). Under the numbering `e` it is therefore a symmetry of
  `CartanMatrix.G₂`, so it is trivial on the vertices.
- `isAutomorphismRepresentation_iso_comp`: precomposing an automorphism
  representation `i : H ⟶ GL₈` with a group-scheme isomorphism
  `φ : H' ≅ H` gives an automorphism representation `φ ≫ i`. An
  isomorphism followed by a closed immersion is a closed immersion. The
  range is unchanged by the published `SubgroupFunctor.range_iso_comp`.

## Proof of the main theorem

Take `K`, `G`, Tits-index data `d`, the numbering `eG` and the hypotheses
of the target. Write `H` for `(CayleyDatum.split K).automorphismGroup`.
The premise at `K` gives `center H = ⊥`, a split pinning `p` of `H`, full
coroot span, and a numbering `e1` with Cartan matrix `G₂`.

1. **Splitting field and trivial star action.** These steps follow the
   published `typeCQuasiSplitInnerForm` proof.
   - `starActionFiniteStage` gives a finite Galois extension `L/K` and
     Galois pinning data `d'` of `G_L`. It also gives a root-datum
     equivalence `ε` with the pinning of `d`, compatible with the bases
     and with the star actions.
   - `isSimplyConnectedFieldExtension` and `splitSimplyConnectedCorootSpan`
     give full coroot span for `d'`.
   - `star_eq_self` and `InnerTypeANormOneReduction.finiteStage_starAction_eq_one`
     make the star action of `Gal(L/K)` on `d'` trivial.
2. **Comparison of split groups over `L`.** Base-change `p` to `L` to get
   `pL`, which keeps full coroot span (`corootSpan_eq_top_of_equiv`).
   - Numbering the simple roots of `pL` and of `d'` through `e1`, `eG` and
     `ε` matches their Cartan entries (`hpair`). Both equal
     `CartanMatrix.G₂`, by the premise and by the target's hypothesis.
   - The published `corootSpanCartanEquiv` gives an isomorphism of root
     data preserving the bases.
   - The published `pinnedIsomorphism` gives a pinned isomorphism `E` from
     `H_L` to `G_L`.
3. **Inner twisting.** `center H = ⊥` and the connected reductivity in `p`
   make `H` adjoint (`isAdjoint_of_isConnectedReductive_of_center_eq_bot`).
   So the identity of `H` is an adjoint quotient (`identityQuotient`).
   The published `TrivialStarInnerTwist.hasInnerDiscrepancy` shows that the
   local isomorphisms of `E` over `Spec L` have inner discrepancy for this
   quotient. `LocalGroupIso.innerCocycle` and `innerCocycle_hasDiscrepancy`
   turn this into an `H`-valued cocycle `ξ` with the same discrepancy.
4. **Descent.** `TypeG2CayleyDescent.exists_iso_automorphismGroup` gives a
   Cayley datum `c` over `K` and a group-scheme isomorphism
   `φ : G ≅ c.automorphismGroup`.
5. **Conclusion.** Set `iG = φ.hom ≫ c.automorphismInclusion`.
   `isAutomorphismRepresentation_automorphismInclusion` (from
   `CayleyAutomorphismGroup`) and `isAutomorphismRepresentation_iso_comp`
   give
   `c.IsAutomorphismRepresentation iG`. So `iG` is a closed immersion, and
   its range on every test scheme is exactly the automorphism matrices of
   `c`, through `GeneralLinear.pointsEquiv`.

## Source

Knus, Merkurjev, Rost and Tignol, *The Book of Involutions* (1998),
registered as `knus-merkurjev-rost-tignol-1998-book-of-involutions`.
Theorem 26.19, printed p.373 / PDF p.396, gives an equivalence between
Cayley algebras and simple groups of type `G₂`. It descends the
multiplication tensor and uses that automorphisms of type-`G₂` groups are
inner (Theorem 25.16). Theorem 25.14, printed p.360 / PDF p.383, describes
the split model. In this proof, innerness comes from the rigidity of the
`G₂` Cartan matrix and the published trivial-star twisting theorem. The
split-model input is the separate premise.
