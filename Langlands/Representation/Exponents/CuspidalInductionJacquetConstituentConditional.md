# The cuspidal-induction Jacquet constituent from cuspidal geometric pieces

Module `Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentConditional`.
Helpers are in namespace `Langlands.CuspidalInductionJacquetConstituent`. The
conditional main theorem is
`Langlands.glCuspidalInductionJacquetConstituent_of_cuspidalPiece`. A definition
record must name a Lean definition, so the submission record names the module's
only `def`, `Langlands.CuspidalInductionJacquetConstituent.blockTransportEquiv`
(described under "Declarations" below), as its entry declaration. The main
content of the module is still the conditional theorem.

## Purpose and provenance

This module contributes to the proof of the published statement
`Langlands.GLCuspidalInductionJacquetConstituentStatement` (module
`Exponents/WeylBranchPiecesStatement`). That statement is an internal derived
product-Levi form, for opposite Jacquet modules, of the cuspidal case of
Bernstein–Zelevinsky 1977 (`bernstein-zelevinsky-1977-induced-i`), Theorem 2.12
with §2.4(d), as used in Corollary 2.13. It follows the task's suggested tensor
route (route A).

The module proves no literature statement unconditionally. Its main theorem is
an implication:

```
theorem glCuspidalInductionJacquetConstituent_of_cuspidalPiece
    (hP : GLInducedOppositeJacquetCuspidalPieceStatement.{uF, uW, uV}) :
    GLCuspidalInductionJacquetConstituentStatement.{uF, uV, uW}
```

The hypothesis `Langlands.GLInducedOppositeJacquetCuspidalPieceStatement`
(module `Geometric/InducedOppositeCuspidalPieceStatement`) is the published
general-linear statement. If some subrepresentation of the opposite Jacquet module
along `C` of the normalized induction of a smooth `π` from `B` surjects onto an
irreducible Levi-cuspidal `ρ`, then there are a refinement `S` of `B`, a
permutation `w` with `ConjugatesLevi (B.flatten S) C w`, and a subrepresentation
of the flattened upper normalized refined Jacquet module of `π` along `S` whose
transport by `w` surjects onto `ρ`. Its proof is the subject of task
`32a402c0-697b-4091-b597-d960900c54cf`. That task derives it from the GL_n
geometric lemma (task `67ebcf61-3d58-4499-9c0c-c847e90aaeb4`). Once that proof is
published, the target follows by applying this theorem to it. The hypothesis is
used at universes `.{uF, uW, uV}`: its inducing representation is in universe
`uV` (factors of `ω`), and its cuspidal quotient is in universe `uW` (factors
of `ρ`).

No filtration, branch or geometric-lemma certificate is a premise. The excluded
results (`GLRelativeRegularComparisonStatement`, reflection, Langlands
parameter/data uniqueness, square-integrable classification, Silberger
Lemma 5.3/Corollary 5.4) are not used. The axioms are `propext`,
`Classical.choice` and `Quot.sound`. The level parameters of the main theorem
are `uF uV uW`, all independent.

## Proof outline

Let `ω` (on `(D.flatten R).Levi`, universe `uV`) and `ρ` (on
`(D.flatten R').Levi`, universe `uW`) be irreducible and Levi-cuspidal. Let `ρ`
be an actual subquotient of the pull-back along `flattenedLeviEquiv F D R'` of
`innerJacquet T D R' (innerInduced T D R (ω ∘ (flattenedLeviEquiv F D R)⁻¹))`.

1. **Factor both cuspidals.** `ProductLeviCuspidalJacquetAssembly.exists_factors`
   writes `ω` as the pull-back along `flattenedLeviProductEquiv F D R` of an
   external tensor product `⊗_i A_i`. Each `A_i` is a smooth irreducible
   Levi-cuspidal representation of `(R i).Levi`. Likewise `ρ ≃ (⊗_i A'_i)`
   pulled back along `flattenedLeviProductEquiv F D R'`, with `A'_i` on
   `(R' i).Levi`.
2. **Tensor decomposition of the inner Jacquet module.** `inducingEquiv` and
   `normalizedRefinedInducedCongr` replace the inducing representation by the
   tensor product. The published proof `Parabolic.refinedInductionTensor`
   identifies the inner normalized induction with the external tensor product
   of the blockwise normalized inductions `Ai i = induced T (R i) A_i`.
   `RefinedOppositeJacquetTensor.normalizedRefinedOppositeJacquetCongr` and
   `oppositeJacquetEquiv` then identify `innerJacquet T D R' (…)` with
   `(⊗_i Jo i)` pulled back along `(refinedLeviEquiv F D R')⁻¹`, where
   `Jo i = oppositeJacquet T (R' i) (Ai i)`. Composing with
   `flattenedLeviEquiv F D R'` turns this pull-back into the pull-back along
   `flattenedLeviProductEquiv F D R'`
   (`refinedLeviEquiv_symm_comp_flattenedLeviEquiv`).
3. **Factorwise subquotients.** Remove the common pull-back along the group
   isomorphism `flattenedLeviProductEquiv F D R'`
   (`isSubquotient_of_comp_equiv`). Then `⊗_i A'_i` is an actual subquotient of
   `⊗_i Jo i`. `FiniteTensor.isSubquotient_factor_of_external` (module
   `Tensor/ExternalSubquotient`) gives, for each block `i`, that `A'_i` is an
   actual subquotient of `Jo i`.
4. **General-linear step per block** (`exists_equiv_transport_of_cuspidalPiece`,
   applied with `B := R i`, `C := R' i`). There are `σ_i` and
   `hσ_i : ConjugatesLevi (R i) (R' i) σ_i` with
   `A'_i ≃ transport (R i) (R' i) σ_i hσ_i A_i`.
5. **Block-diagonal assembly.** Put `h = blockPermOf D σ ∈ blockWeyl D`
   (`blockPermOf_mem_blockWeyl`). By `conjugatesLevi_flatten_blockPermOf`, `h`
   conjugates `D.flatten R` to `D.flatten R'`. `blockTransportEquiv` identifies
   the pulled-back tensor product of the blockwise transports with
   `transport (D.flatten R) (D.flatten R') h hh ω`. Chaining the equivalence of
   step 1 for `ρ`, `externalCongr` of step 4, and `blockTransportEquiv` gives the
   required `ρ.ρ.Equiv (transport (D.flatten R) (D.flatten R') h hh ω.ρ)`.

## Declarations

### Subquotients (section `Subquotient`)

* `nonempty_equiv_of_isSubquotient hA hY h`: if `A` and `Y` are irreducible and
  `IsSubquotient A Y`, then `Nonempty (A.Equiv Y)`. The subrepresentation `U` is
  `⊥` or `⊤`. It is not `⊥`, since then the surjection onto the nonzero `Y`
  would be zero. For `U = ⊤`, composing with the inclusion `A → ⊤` gives a
  surjective intertwining map `f : A → Y`. Schur's lemma
  (`Representation.IsIrreducible.bijective_or_eq_zero`) makes `f` bijective,
  since it is nonzero, and `f.ofBijective` is the equivalence.
* `isSubquotient_of_comp_equiv e h`: for a group isomorphism `e : H ≃* G`,
  `IsSubquotient (A.comp e) (Y.comp e)` implies `IsSubquotient A Y`. Pull back
  along `e.symm` (`IsSubquotient.comp`) and simplify the double pull-back.

### Full refinements (section `FullRefinement`)

Here `K` is a field, `B C : BlockShape m`, `S : BlockRefinement B`, and the
hypothesis is `refinedLevi K B S = ⊤`.

* `leviSubgroup_flatten_of_full`: `(B.flatten S).leviSubgroup K = B.leviSubgroup K`.
  Proved by `flattenedLeviEquiv_embedding` and `flattenedLeviEquiv_symm_embedding`.
* `conjugatesLevi_of_full`: a permutation conjugating the Levi of `B.flatten S`
  to that of `C` also conjugates the Levi of `B` to it.
* `flattenedLeviEquiv_leviConjugation_symm_of_full`: the inverse conjugation from
  `C` to `B.flatten S`, followed by `flattenedLeviEquiv`, is the inverse
  conjugation from `C` to `B`. Checked after `B.leviEmbedding`, which is
  injective.
* `transport_comp_flattenedLeviEquiv_of_full`: the transport by `w` of
  `π ∘ (subtype ∘ flattenedLeviEquiv K B S)` from `B.flatten S` equals the
  transport of `π` from `B`, as an equality of representations.
* `surjective_subtype_comp_flattenedLeviEquiv_of_full`: the map
  `(B.flatten S).Levi → B.Levi`, `subtype ∘ flattenedLeviEquiv`, is surjective.

### General-linear constituent step (section `GeneralLinearStep`)

`exists_equiv_transport_of_cuspidalPiece T hP hm B C π ρ`: let `0 < m`,
`B C : BlockShape m`, and `π` a smooth, irreducible, Levi-cuspidal
representation of `B.Levi` on `V : Type uV`. Let `ρ` be an irreducible
Levi-cuspidal representation of `C.Levi` on `W : Type uW`. Assume `ρ` is an
actual subquotient of
`(CuspidalJacquetMultiplicity.oppositeJacquet T C (CuspidalJacquetMultiplicity.induced T B (Rep.of π))).ρ`.
Then there are `w` and `hw : ConjugatesLevi B C w` with
`Nonempty (ρ.Equiv (transport B C w hw π))`.

Proof. `hP` gives `S`, `w`, `hw`, a subrepresentation `U` of
`Jf = (T.normalizedRefinedJacquet B S π).comp flattenedLeviEquiv` and a
surjection `q` from the transport of `U` onto `ρ`.

* If `refinedParabolic B S ≠ ⊤`, Levi-cuspidality of `π` makes the refined
  Jacquet module zero (`hπc.2 S hne : Subsingleton (RefinedJacquetModule B S π)`).
  Then `q` would vanish on the nonzero `ρ`, which is impossible.
* So `refinedParabolic B S = ⊤`, and `refinedLevi B S = ⊤`
  (`refinedLevi_eq_top_of_refinedParabolic_eq_top`).
  `CuspidalSupport.fullRefinedJacquetEquiv` and `compCongr` give
  `eJ : Jf ≃ π ∘ ψ` with `ψ = subtype ∘ flattenedLeviEquiv`. `(U, q)` exhibits
  `ρ` as an actual subquotient of `transport (B.flatten S) C w hw Jf`, using the
  same subspace. That transport is irreducible:
  `JacquetLength.isIrreducible_comp` (with `ψ` surjective),
  `isIrreducible_of_equiv` and `isIrreducible_transport` apply. By
  `nonempty_equiv_of_isSubquotient` the transport is equivalent to `ρ`.
  Finally `transport_comp_flattenedLeviEquiv_of_full` and `compCongr eJ`
  rewrite the transport of `Jf` as `transport B C w _ π`.

### Block assembly (section `Blocks`)

Here `K` is a field, `D : BlockShape n`, `R R' : BlockRefinement D`, and
`σ : ∀ i, Equiv.Perm (Fin (D.size i))` with
`hσ : ∀ i, ConjugatesLevi (R i) (R' i) (σ i)`. These generalize the
self-conjugating (`R = R'`) assembly of `Classification/ProductLeviMinimalIndex`
to two refinements.

* `conjugatesLevi_flatten_blockPermOf`: `blockPermOf D σ` conjugates
  `D.flatten R` to `D.flatten R'`. By `TotalConjugatingCount.conjugatesLevi_iff`,
  conjugation of Levis means preservation of the "same block" relation. For two
  indices in the same block `i` of `D`, use
  `ProductLeviMinimalIndex.blockIndex_flatten_index_eq_iff` and `hσ i`. For
  indices in different blocks of `D`, both sides are false
  (`blockIndex_flatten_index_ne`).
* `nestedEmbedding_injective`: the map from `∀ i, (S i).Levi` to `GL_n` through
  `refinedLeviEquiv` and `D.leviEmbedding` is injective.
* `flattenedLeviProductEquiv_leviConjugation`: in the product coordinates
  `flattenedLeviProductEquiv`, conjugation by `blockPermOf D σ` from
  `D.flatten R` to `D.flatten R'` is blockwise conjugation by `σ i`. Checked
  after the injective nested embedding, using
  `ProductLeviMinimalIndex.leviEmbedding_conj_blockPermOf`.
* `flattenedLeviProductEquiv_leviConjugation_symm`: the same for the inverse
  conjugations.
* `external_transport`: the external tensor product of the blockwise transports
  `transport (R i) (R' i) (σ i) (hσ i) (A i)` acts at `y` as `⊗ A_i` at the
  blockwise inverse conjugates of `y`. Checked on pure tensors.
* `blockTransportEquiv ω A E σ hσ hw` (a `def`): from
  `E : ω ≃ (⊗_i A_i) ∘ flattenedLeviProductEquiv K D R`, it builds
  `(⊗_i transport (R i) (R' i) (σ i) (hσ i) (A i)) ∘ flattenedLeviProductEquiv K D R'
  ≃ transport (D.flatten R) (D.flatten R') (blockPermOf D σ) hw ω`. Its linear
  equivalence is `E.symm`. Intertwining follows from `E.symm` at the inverse
  conjugate of the group element, `external_transport` and
  `flattenedLeviProductEquiv_leviConjugation_symm`.
* `refinedLeviEquiv_symm_comp_flattenedLeviEquiv`:
  `(refinedLeviEquiv K D S)⁻¹ ∘ flattenedLeviEquiv K D S = flattenedLeviProductEquiv K D S`
  as monoid homomorphisms. This holds by unfolding `flattenedLeviEquiv`.

### Main theorem

`Langlands.glCuspidalInductionJacquetConstituent_of_cuspidalPiece hP` follows
the proof outline above: steps 1–3 in the main body, step 4 by
`exists_equiv_transport_of_cuspidalPiece` for each block (positivity
`D.positive i`), and step 5 by `conjugatesLevi_flatten_blockPermOf`,
`blockPermOf_mem_blockWeyl` and `blockTransportEquiv`. The final equivalence is
`E'.trans ((compCongr (externalCongr fun i => (e i).some) _).trans (blockTransportEquiv …))`.

## Dependencies

Imports: `Exponents/WeylBranchPiecesStatement` (target statement),
`Geometric/InducedOppositeCuspidalPieceStatement` (hypothesis statement),
`Classification/ProductLeviCuspidalJacquetAssembly` (`exists_factors`,
`inducingEquiv`, `normalizedRefinedInducedCongr`, and transitively the
refined opposite Jacquet tensor comparison and `ProductLeviMinimalIndex`),
`Parabolic/RefinedInductionTensorProof` (`Parabolic.refinedInductionTensor`),
`CuspidalSupport/AssociatedGeometricPiecesEquivalenceProof`
(`fullRefinedJacquetEquiv`; transitively
`CuspidalSupport.refinedLevi_eq_top_of_refinedParabolic_eq_top` from
`CuspidalSupport/JacquetVanishingSubgroups` and the irreducibility lemmas of
`CuspidalSupport/InducedJacquetCount`) and the new helper
`Tensor/ExternalSubquotient`.
