# Injectivity of inertia coinvariants for a central induced torus quotient: proof

This module proves
`Langlands.Geometry.Building.Kottwitz.InducedCentralTorusInertiaInjectivityStatement`
(module `Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaInjectivityStatement`)
as the theorem `inducedCentralTorusInertiaInjectivity`. The proof keeps the
full generality of the statement: fields of any characteristic, any tower
`k → K → E` with `IsScalarTower k K E`, `IsSepClosure k E` and `Normal k K`,
and the actual selected map `fundamentalInertiaMap`. The axioms used are
`propext`, `Classical.choice` and `Quot.sound`.

## Sources and route

The statement is the injectivity claim in the proof of Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 11.5.3, printed
p. 431 / PDF p. 462. KP refer to an argument that they write out in the proofs
of Lemma 11.1.10 (printed p. 425 / PDF p. 456) and Lemma 11.1.12(2) (printed
p. 426 / PDF p. 457). There the kernel of `X_*(A)_I → X_*(B)_I` is the image
of the finite group `H₁(Ī, X_*(C))` for a finite quotient `Ī` of inertia, and
`X_*(A)_I` is torsion-free. The statement Markdown gives the quotations.

The Lean proof follows the same two ideas, finiteness of the inertia action and
torsion-freeness, but replaces the connecting homomorphism by a norm argument
(module `Langlands.Algebra.CoinvariantsNormTorsion`). It uses only the
injectivity of `π₁(Z) → π₁(H)`, not exactness in the middle.

## `fundamentalGroupGalois_finite_range`

For a connected reductive `G` over `k` and a separable closure `E`, the set of
operators `Set.range (fundamentalGroupGalois k G E hG)` is finite.

Let `T` be the chosen maximal torus `(chosenChoice k G hG).torus`. Its base
change to `E` is split (`isSplitTorus_baseChange_of_isSepClosure`). By
`torusLatticeGaloisContinuity` there is a finite-dimensional intermediate field
`L` such that every `σ` fixing `L` pointwise acts trivially on `X_*(T_E)`. The
Galois action on `π₁(G)`, the quotient of `X_*(T_E)` by the image of
`X_*(T_sc,E)`, is descended from this action
(`Choice.galoisRepresentation_projection`), so such a `σ` also acts trivially on
`π₁(G)`. If `σ` and `τ` agree on `L`, then `τ⁻¹σ` fixes `L`, so `σ` and `τ` act
in the same way. The operator of `σ` therefore depends only on the embedding
`σ|_L : L →ₐ[k] E`. There are finitely many such embeddings (`AlgHom.fintype`),
so the range is contained in the range of a function on a finite type.

## Permuted bases for an induced torus

`IsInducedTorus.exists_permuted_character_basis_of_isSepClosure`: an induced
torus `Z` has a finite basis of `X^*(Z_E)` permuted by all of `E ≃ₐ[k] E`. The
definition `IsInducedTorus` supplies a finite Galois splitting field `E'` and a
basis of `X^*(Z_{E'})` permuted by `Gal(E'/k)`. Choose an embedding
`e : E' →ₐ[k] E` (`IsSepClosed.lift`). Restriction of characters along `e` is
bijective (`characterLattice.field_restriction_bijective`) and carries the
action of `τ ∈ Aut_k(E)` to that of `τ.restrictNormal E'`
(`characterLattice.restriction_galois`). The transported basis is therefore
permuted.

`IsInducedTorus.exists_permuted_cocharacter_basis_of_isSepClosure`: the same
holds for `X_*(Z_E)`. The lattice pairing of the split torus `Z_E` is perfect
(`IsSplitTorus.isPerfPair_latticePairing`). Take the dual basis
`Langlands.PermutationBasis.pairedBasis` for the flipped pairing. Each `σ` maps
the character basis by an injective, hence bijective, self-map of the finite
index type. The pairing is Galois invariant (`latticePairing_galoisRepresentation`),
so `pairedBasis_permutation` shows that `σ` permutes the dual basis by the same
permutation.

`IsInducedTorus.exists_permuted_fundamentalGroup_basis`: the actual
`π₁(Z) = fundamentalGroup k Z.toGrp E _` has a basis permuted by the Galois
action `fundamentalGroupGalois`. The torus comparison
`torusFundamentalComparison : π₁(Z) → X_*(Z_E)` is bijective and Galois
equivariant (`torusFundamentalComparison_proof`, KP Fact 11.3.5). The cocharacter
basis is transported along its inverse.

## `inducedCentralTorusInertiaInjectivity`

Fix the data of the statement and write `j = fundamentalGroupMap k E Z.toGrp H _ hH i`.
`Normal k E` follows from `IsSepClosure` (Mathlib's `IsSepClosure.isGalois`).

1. `j` is injective. This is the first conjunct of
   `centralTorusFundamentalExactness` applied with `hZ.isTorus`.
2. `j` is Galois equivariant. This is the `.2.2.1` component of
   `algebraicFundamentalGroupMap` at the chosen presentations.
3. The selected map satisfies `IsFundamentalInertiaMap`:
   `m (proj_M x) = proj_N (j x)` (`fundamentalInertiaMapStatement`).
4. Apply `Langlands.CoinvariantsNorm.injective_of_finite_range` to the
   restrictions of both Galois representations to `relativeInertia k K E`.
   - The range of the restricted action on `π₁(H)` is a subset of the finite
     range from `fundamentalGroupGalois_finite_range`.
   - Torsion-freeness of `π₁(Z)_I` is
     `Langlands.CoinvariantsNorm.eq_zero_of_smul_eq_zero_of_permuted` for the
     permuted basis of `π₁(Z)`, restricted to inertia.

The premises `IsConnectedReductive G`, `IsClosedSubgroup i`, `IsCentral i` and
the fppf quotient premise are used only through `centralTorusFundamentalExactness`.
