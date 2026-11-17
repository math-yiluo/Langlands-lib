# Groups of multiplicative type over a field split over a finite Galois extension

Author: Worker 60.

`Langlands.GroupScheme.multiplicativeTypeFiniteGaloisSplitting` proves exactly
`Langlands.GroupScheme.MultiplicativeTypeFiniteGaloisSplittingStatement.{u}`, imported
unchanged from `Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingStatement`.
The universe `u` is arbitrary. For every field `k : Type u` and every group scheme `H`
over `Spec k` with `IsMultiplicativeType H`, it produces a field `K : Type u` with a
`k`-algebra structure, `FiniteDimensional k K` and `IsGalois k K`, a finitely generated
abelian group `Λ : Type u`, and an isomorphism of group schemes over `Spec K` from the
base change of `H` onto `Diagonalizable.groupScheme (CommRingCat.of K) Λ`.

The theorem has no hypotheses beyond the statement's. The splitting extension supplied by
`IsMultiplicativeType H` may be infinite, transcendental or inseparable. The proof derives
affineness and finite type of `H`; they are not extra premises. There is no perfectness,
infinitude or characteristic restriction. Torsion in the character group is allowed, so
finite groups such as `μ_n` are covered, including when they are not smooth. The trivial
character group is also covered.

## Helper declarations

All helpers are in the namespace `Langlands.GroupScheme.MultiplicativeTypeSplitting`.

- `IsFGDiagonalizable G` is an internal `Prop`: `G` is isomorphic to
  `(Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp` for some finitely generated
  `Λ : Type u`. With this predicate, `IsMultiplicativeType G` says that some base change
  `G_K` satisfies `IsFGDiagonalizable`, and the target statement asks for a finite Galois
  `K` with this property. The predicate is only a proof device.
- `IsFGDiagonalizable.of_iso` transports the predicate along an isomorphism.
- `IsFGDiagonalizable.baseChange` keeps it, with the same `Λ`, under base change along
  `algebraBaseMap k K` for any field extension `K / k`. The proof uses the published
  comparison `Diagonalizable.baseChangeIso`.
- `IsFGDiagonalizable.fieldTower` passes the predicate from `L` to `K` for a tower
  `k → L → K`, using the published `baseChangeFieldTowerIso`.
- `diagonalizableIsoOfGroupLikeSpan` replaces `I → ℤ` by an arbitrary abelian group `Λ`
  in the published `AffineCoordinates.splitIsoOfGroupLikeSpan`. Its inputs are an affine
  `T`, an isomorphism `T_K ≅ D_K(Λ)`, and the condition that the group-like elements span
  the coordinate Hopf algebra `A` of `T` over `k`. It builds an isomorphism
  `T ≅ D_k(Λ)`. The proof follows the torus construction:
  - The isomorphism over `K` gives a bialgebra isomorphism `K ⊗ A ≃ K[Λ]`.
  - Spanning identifies the group-likes of `A` with those of `K ⊗ A`
    (`GroupLike.baseChangeMulEquivOfSpan`), and hence with `Λ`.
  - The reconstruction `MonoidAlgebra.bialgEquivOfSpanGroupLike` gives
    `A ≃ k[Additive (GroupLike k A)]`.
  - `Diagonalizable.congrIso` reindexes the result by `Additive (GroupLike k A) ≃+ Λ`.
- `isFGDiagonalizable_of_isSepClosed`: over a separably closed field, every group of
  multiplicative type satisfies `IsFGDiagonalizable`. The proof runs as follows:
  - `IsMultiplicativeType.isAffine` (published) makes `H` affine.
  - The given model over `K` gives group-like spanning of `K ⊗ A`, through
    `SplittingAssembly.scalarExtensionCoordinatesIso`,
    `SplittingAssembly.span_of_hopfSpecIso` and Mathlib's
    `AddMonoidAlgebra.span_isGroupLikeElem`.
  - The published theorem `CoalgebraDescent.separablyClosedGroupLikeSpanning.{u,u,u}`
    descends the spanning to `A`.
  - `diagonalizableIsoOfGroupLikeSpan` gives the isomorphism over `k`, with the same `Λ`.
- `isMultiplicativeType_baseChange_of_isAlgebraic`: base change along an algebraic
  extension `L / k` preserves `IsMultiplicativeType`. Take a model over `K` and embed `L`
  into `E = AlgebraicClosure K` over `k`. The tower isomorphisms for `k → L → E` and
  `k → K → E`, together with `Diagonalizable.baseChangeIso`, give
  `(H_L)_E ≅ D_E(Λ)`. This mirrors the published `IsTorus.baseChange_of_isAlgebraic`.
- `exists_finiteIntermediateField`: for `H` of multiplicative type there is a finite
  intermediate field `E` of `SeparableClosure k / k` over which `H` satisfies
  `IsFGDiagonalizable`. The proof runs as follows:
  - The previous two helpers give `H_{k_s} ≅ D_{k_s}(Λ)` for `k_s = SeparableClosure k`.
  - Composing with `Diagonalizable.baseChangeIso` gives an isomorphism
    `H_{k_s} ≅ (D_k(Λ))_{k_s}` of base changes of two group schemes over `k`.
  - `H` is affine, so its structure morphism is quasi-compact and quasi-separated.
  - `D_k(Λ)` is locally of finite type, by the published `Diagonalizable.locallyOfFiniteType`
    since `Λ` is finitely generated. Since `Spec k` is Noetherian, it is also locally of
    finite presentation.
  - The published `Descent.FiniteStage.isoModel` therefore yields a finite intermediate
    field `E` and an isomorphism `H_E ≅ (D_k(Λ))_E`. Composing with
    `Diagonalizable.baseChangeIso` gives `H_E ≅ D_E(Λ)`.

## Final theorem

`multiplicativeTypeFiniteGaloisSplitting` takes `E` from `exists_finiteIntermediateField`
and sets `K := IntermediateField.normalClosure k E (SeparableClosure k)`.

- `K` is finite over `k`, by Mathlib's instance for the normal closure of a
  finite-dimensional extension.
- `K` is Galois over `k`, by `IsGalois.normalClosure`, because `SeparableClosure k` is
  Galois over `k`.
- `IsFGDiagonalizable.fieldTower` for `k → E → K` gives `H_K ≅ D_K(Λ)` with the same
  finitely generated `Λ`.

`K` is an intermediate field of `SeparableClosure k`, so it lies in universe `u`. The
conclusion is unpacked exactly into the statement's existential form.

The axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Dependencies and provenance

The statement module and everything it imports are unchanged. The proof imports these
published modules by their Lean names:

- `Torus.MultiplicativeTypeGeometry` for affineness.
- `Torus.SplitOfGroupLikeSpan`, `Torus.SplittingAssembly`, `Algebra.GroupLikeBaseChange`
  and `Algebra.GroupLikeReconstruction` (the last two through imports) for the Hopf
  coordinates and group-like comparisons.
- `Torus.SplittingDescentHelpers` for the field-tower isomorphism.
- `Torus.DiagonalizableBaseChange`, `Torus.DiagonalizableDecomposition` and
  `Torus.DiagonalizableGeometry` for the diagonalizable base change, reindexing and finite
  type.
- `Torus.LatticeGalois` for `algebraBaseMap`.
- `Descent.FiniteStageIso` for finite-stage descent of isomorphisms.
- `RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof` for the coalgebra descent.

The mathematics follows the statement's sources:

- Milne, *Algebraic Groups* (2017), Theorem 12.18, (a) ⇒ (d) (p.237), and
  Corollary 12.19 (p.238).
- Conrad, *Reductive group schemes* (2014), Lemma B.1.5 (p.283).
- SGA 3, Exposé X, Proposition 1.4.

Diagonalizability over the separable closure comes from the coétale argument behind
Theorem 12.18. The formalization packages that argument in the published coalgebra
descent theorem. The descent to a finite separable extension is Corollary 12.19:
finitely many elements of `k_s` suffice. Here it comes from the published finite-stage
descent of isomorphisms over an algebraic extension. The Galois closure is then taken
inside `SeparableClosure k`, as the statement Markdown explains. The route is the one used
for the torus case in `Torus.FiniteGaloisSplittingProof`, extended from free character
groups to arbitrary finitely generated ones. The torus versions of the two key steps,
`AffineCoordinates.splitIsoOfGroupLikeSpan` and
`IsSplitTorus.exists_finiteIntermediateField_of_algebraic`, are stated for split tori
only. This module therefore proves `diagonalizableIsoOfGroupLikeSpan` and uses the
general `Descent.FiniteStage.isoModel` instead. No new source assertion is made.
