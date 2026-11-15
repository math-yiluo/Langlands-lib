# Products of left reduced representations (clause 2)

Lean module: `Langlands.Representation.Classification.LeftCuspidalDerivative.Product`.

An internal step of the proof of
`Langlands.Classification.LeftCuspidalDerivative.LeftCuspidalDerivativeLemma`: its product
clause. The final theorem `leftReduced_binaryProduct` takes the per-piece proposition
`BinaryGeometricPieces.BinaryGeometricPieceConstituents` (module
`Langlands.Representation.Classification.BinaryGeometricPieceConstituentsStatement`) as an
explicit hypothesis `hPP`; no other premise is added. The argument is a Frobenius-reciprocity
and geometric-lemma argument in the spirit of Zelevinsky, *Induced representations of reductive
p-adic groups II* (1980), §§1–2; the route below is internal to this proof.

Throughout, `A` is a supercuspidal representation of `GL_d`, `Y₁`, `Y₂` are smooth
representations of `GL_{m₁}`, `GL_{m₂}`, and `Y₁ × Y₂` is the Library binary normalized
product `(T.binaryNormalizedProductFunctor m₁ m₂).obj (Y₁, Y₂)`.

## Sections and results

### FirstBlockQuotient

* `isSubquotient_firstBlock_of_ne_zero`: for groups `H 0`, `H 1`, a nonzero intertwiner
  `ρ → τ 0 ⊠ τ 1` with `τ 0` irreducible exhibits `τ 0` as a quotient (hence subquotient) of
  the restriction of `ρ` along `MonoidHom.mulSingle H 0`. Proof: pick `v` with `f v ≠ 0`, a
  functional `φ` on the second factor not killing `f v` (`exists_dual_rid_lTensor_ne_zero`),
  and contract the second slot (`firstSlotContraction`); the composite is a nonzero map to the
  irreducible `τ 0`, hence surjective.

### GluedRestriction

* `exists_isSubquotient_piece_comp`: if a functor `F` is glued from pieces
  (`IsGluedFrom F pieces`) and `ρ` is an irreducible subquotient of the restriction of
  `F.obj Y` along a group homomorphism `φ`, then `ρ` is a subquotient of the restriction of
  some piece. Proof: restrict the filtration along `φ`
  (`RepFunctorFiltration.restrictGroup`, `restrictGroupGradedIso`) and apply
  `WeylBranchPieces.exists_isSubquotient_graded`.

### Supercuspidal

* `exists_injective_of_isSubquotient_supercuspidal` (`0 < d`): an admissible representation of
  `GL_d` with `A` as a subquotient contains `A` as a subrepresentation (single-block case of
  `CuspidalSupport.leviCuspidalConstituent_maps`).
* `not_isSubquotient_binaryProduct_of_supercuspidal` (`0 < a₁, a₂`): a supercuspidal `A` of
  `GL_{a₁+a₂}` is not a subquotient of `ρ₁ × ρ₂` for finite-length `ρ₁`, `ρ₂`. Proof: the
  product has finite length, hence is admissible, so `A` embeds into it (previous item);
  Frobenius reciprocity (`exists_jacquet_ne_zero_of_isSubrepresentation`) gives a nonzero map
  out of the Jacquet module `r_{(a₁,a₂)}(A)`, which is zero because `A` is supercuspidal
  (`subsingleton_jacquet_of_isSupercuspidal`).
* `not_isSubquotient_castRank_binaryProduct_of_supercuspidal`: the same after a rank transport
  `a₁ + a₂ = a`.
* `exists_supercuspidal_castRank`: rank transport of a supercuspidal representation is
  supercuspidal.

### RankTransport, Degenerate, RankZero

* `castRank_castRank`, `isIrreducible_castRank`, `isSubquotient_castRank`,
  `isSubrepresentation_castRank`: rank transport along `r = s` composes and preserves these
  properties (by `subst`).
* `nontrivial_of_isIrreducible`, `not_isSubquotient_of_subsingleton`,
  `subsingleton_piTensorProduct`: irreducible representations are nonzero, nothing nonzero is
  a subquotient of zero, and a tensor product with a zero factor is zero.
* `isSubrepresentation_rankZero_product`: for a nonzero representation `A` of `GL_0`, every `Z`
  embeds into `A × Z` (by `z ↦ a ⊗ z` for some `a ≠ 0`, through
  `binaryLeftZeroTensorEquiv` and `castRankEquiv`).
* `subsingleton_of_leftReduced_rankZero` (`d = 0`): a finite-length left `A`-reduced `Y` is
  zero, since otherwise an irreducible subrepresentation `Z` of `Y` embeds into `A × Z`.

### Main

* `exists_isSubquotient_geometricPiece_firstBlock`: the previous gluing result specialised to
  the geometric lemma filtration of `r_{(d,k)} ∘ i_{(m₁,m₂)}`, with the first-block embedding
  and the piece written exactly as in `BinaryGeometricPieceConstituents`.
* `false_of_isSubquotient_binaryProduct_of_pos` (`m₁, m₂, d, k > 0`, `d + k = m₁ + m₂`, given
  `hPP`): if `Y₁`, `Y₂` are finite-length and left `A`-reduced, no irreducible subquotient `Z`
  of `Y₁ × Y₂` embeds into `A × σ`. Proof:
  1. Frobenius reciprocity gives a nonzero map `r_{(d,k)}(Z) → A ⊠ σ`, so `A` is a subquotient
     of the first-block restriction of `r_{(d,k)}(Z)` (FirstBlockQuotient).
  2. The normalized Jacquet functor preserves subquotients
     (`CuspidalSupport.normalizedJacquetSubquotient`), so `A` is a first-block subquotient of
     `r_{(d,k)}(Y₁ × Y₂)`, and `Y₁ × Y₂ ≅ i_{(m₁,m₂)}(Y₁ ⊠ Y₂)`
     (`SegmentSocleDerivativesProof.nonempty_ofPairProductIso`).
  3. The geometric lemma (`Geometric.padicGeometricLemma`) glues
     `r_{(d,k)} ∘ i_{(m₁,m₂)}` from the geometric pieces; by the previous item `A` is a
     first-block subquotient of one piece applied to `Y₁ ⊠ Y₂`.
  4. `hPP` gives three cases: `A` is a first-block constituent of `Y₁` or of `Y₂`, both
     excluded by the first-block criterion `not_leftReduced_of_isFirstBlockConstituent`
     (module `FirstBlock`), or `A` is a subquotient of a proper normalized product `ρ₁ × ρ₂`
     of irreducible representations, excluded by
     `not_isSubquotient_castRank_binaryProduct_of_supercuspidal`.

  Lean technicality: the bodies of the Library's `padicGeometricLemma` statement and of
  `BinaryGeometricPieceConstituents` carry abstracted auxiliary proof terms, so the same data
  elaborates there and here with different (proof-irrelevant) proofs inside. Lean's default
  definitional-equality check gets lost unfolding them, so each argument coming from
  `padicGeometricLemma` or going into `hPP` is passed as `(by with_reducible exact _)`, which
  succeeds at once by proof irrelevance.

### Wrapper

* `leftReduced_of_castRank_isSubquotient`: if every irreducible subquotient of `P` is, after a
  rank transport `m = m'`, a subquotient of a left `A`-reduced `Y`, then `P` is left
  `A`-reduced.
* `isSubquotient_of_isSubquotient_binaryProduct_zero_left` / `_right` (`m₁ = 0` /
  `m₂ = 0`): an irreducible subquotient of `Y₁ × Y₂` is, after rank transport, a subquotient of
  `Y₂` / `Y₁`. Proof: `Y₁ × Y₂` is the tensor product with a factor on which the group acts
  trivially (`binaryLeftZeroTensorEquiv` / `binaryRightZeroTensorEquiv`, with
  `TensorProduct.comm` for the right case), and
  `FiniteTensor.isSubquotient_of_tprod_trivial` applies.
* `subsingleton_binaryProduct_of_left`: if `Y₁ = 0` (positive ranks), then `Y₁ × Y₂ = 0`.
* `leftReduced_binaryProduct` (**clause 2**, given `hPP`): for finite-length left
  `A`-reduced `Y₁`, `Y₂`, the product `Y₁ × Y₂` is left `A`-reduced. Cases:
  `m₁ = 0` or `m₂ = 0` (previous items); otherwise let `Z` be an irreducible subquotient
  embedding into `A × σ` with `d + k = m₁ + m₂`:
  `d = 0` (then `Y₁ = 0` by `subsingleton_of_leftReduced_rankZero`, so the product is zero);
  `k = 0` (here `σ` is an arbitrary representation of `GL_0`, and `A × σ` is not `A` in
  general but `A ⊗ σ` with the group acting trivially on `σ`, `binaryRightZeroTensorEquiv`;
  `exists_ne_zero_of_isSubrepresentation_rankZero` (module `Frobenius`) contracts the
  embedding `Z ↪ A ⊗ σ` against a functional on `σ` to give a nonzero intertwiner `Z → A`
  after rank transport; it is surjective because `A` is irreducible, so `A` is a quotient,
  hence a subquotient, of `Z` and so of `Y₁ × Y₂`, which
  `not_isSubquotient_castRank_binaryProduct_of_supercuspidal` excludes; no assumption on `σ`
  is used);
  `d, k > 0` (`false_of_isSubquotient_binaryProduct_of_pos`).
