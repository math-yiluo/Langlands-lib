# Galois descent of torus points with prescribed character values

## Statement

`Langlands.GroupScheme.exists_rationalPoint_characterValue_eq_of_equivariant` is a theorem
over an arbitrary universe `u`. Let `k` and `L` be fields with a `k`-algebra structure on `L`
and `IsGalois k L`. No finite-degree assumption is made. Let `T` be a commutative group
scheme over `Spec k`, and write `T_L` for its base change along `algebraBaseMap k L`
(`Spec L → Spec k`). Assume `T_L` is a split torus: `IsSplitTorus` of
`(GroupScheme.baseChange (algebraBaseMap k L)).obj T.toGrp`. Let
`φ : characterLattice T_L →+ Additive Lˣ` be a homomorphism. Assume it is equivariant for
the canonical Galois action `characterLattice.galoisRepresentation k L T` on characters: for
every `σ : L ≃ₐ[k] L` and every character `χ`, the value of `φ` at `σ · χ` is `σ` applied to
the value of `φ` at `χ`, as elements of `L`. Then there is a `k`-point
`h : Lie.AffinePoints T.toGrp k` such that, for every character `χ` of `T_L`,
`Lie.characterValue χ (rationalBaseChangePoint k L T h) = φ χ`. Here
`rationalBaseChangePoint k L T h` is `h` viewed as an `L`-point of `T_L`.

This is the existence half of the classical description of `T(k)`: when `T` splits over `L`,
evaluation identifies `T(L)` with `Hom(X^*(T_L), Lˣ)`, and Galois descent identifies `T(k)`
with the Galois-fixed points. Uniqueness of `h` is true but is not stated. The theorem's
binders are those of the proposition `TorusEquivariantCharacterValueDescentStatement`
proposed in Task 5959 (not published). This module proves the result directly as an
ordinary theorem, for use in the proof of
`QuasiSplitAdjointSimpleRootTransitivityStatement`.

## Auxiliary declarations (namespace `EquivariantCharacterValueDescent`)

- `galoisTestInverse σ` is the coefficient map `σ⁻¹`. It is an `L`-algebra map from the
  twisted test algebra `Lie.GaloisTestAlgebra σ L` to `L`. This is the same map as the
  private `galoisTestInverse` of `Langlands.GroupScheme.Lie.RootOrbitCharacterAction`.
- `inverseConjugate σ s` is the `L`-point of `T_L` obtained by applying `galoisTestInverse σ`
  to the published twisted point `Lie.galoisTestPoint k L σ L T.toGrp s`.
- `affineBaseChangeEquiv_inverseConjugate`: under the Library equivalence
  `Lie.affineBaseChangeEquiv k L T.toGrp L` between `L`-points of `T_L` and `L`-points of `T`,
  `inverseConjugate σ s` goes to `GaloisPoint.conjugate k L T.toGrp σ⁻¹` of the image of `s`.
  This is the coefficient action of `σ⁻¹`. The proof uses
  `Lie.affineBaseChangeEquiv_naturality` and `Lie.affineBaseChangeEquiv_galoisTestPoint`. Both
  sides are then the same coefficient map applied to the same point.
- `characterValue_inverseConjugate`: the value of `χ` at `inverseConjugate σ s` is `σ⁻¹`
  applied to the value of the transported character `σ · χ` at `s`. It follows from
  `CoordinateWeights.characterValue_affineMap` (character values are natural in the
  coefficient algebra) and the published `Lie.characterValue_galoisRepresentation`.
- `characterValue_eq_pointCharacters`: the affine character value is the Library's
  `characterLattice.pointCharacters` evaluation transported along
  `Γ(Spec L) ≅ L` (`Scheme.ΓSpecIso`). It holds by definition.
- `eq_of_characterValue_eq`: if `T_L` is split, two `L`-points with the same value at every
  character are equal. The proof combines the previous identity with injectivity of
  `characterLattice.pointCharacters` (`pointCharacters_bijective`).
- `exists_characterValue_eq`: if `T_L` is split, every `φ : characterLattice T_L →+ Additive Lˣ`
  is the evaluation at some `L`-point. The point is the preimage, under the Library equivalence
  `characterLattice.pointCharactersEquiv`, of `φ` transported to the global units of `Spec L`.

## Proof of the main theorem

1. `T` is affine: `T.toGrp` is a torus in the sense of `IsTorus`, with `L` as splitting field.
   The Library theorem `SplittingAssembly.isAffine_of_isTorus` gives `IsAffine T.toGrp.X.left`.
   The descent API needs this.
2. `exists_characterValue_eq` gives `t ∈ T_L(L)` with `χ(t) = φ χ` for all `χ`.
3. For every `σ`, `inverseConjugate σ t = t`. By `characterValue_inverseConjugate`, the value
   of `χ` there is `σ⁻¹(φ(σ · χ)) = σ⁻¹(σ(φ χ)) = φ χ`, by equivariance. Then
   `eq_of_characterValue_eq` applies.
4. Let `x` be the image of `t` under `Lie.affineBaseChangeEquiv`. Applying step 3 to `σ⁻¹` and
   `affineBaseChangeEquiv_inverseConjugate` gives `conjugate σ x = x` for every `σ`. So `x`
   lies in `GaloisPoint.fixedSubgroup k L T.toGrp`.
5. The Library's `GaloisPoint.algebraicFixedEquiv`, valid for any Galois extension, gives the
   point `h = (algebraicFixedEquiv k L T.toGrp).symm ⟨x, _⟩`. Its extension
   `GaloisPoint.extend` is `x`.
6. `affineBaseChangeEquiv_rationalBaseChangePoint` and injectivity of
   `Lie.affineBaseChangeEquiv` give `rationalBaseChangePoint k L T h = t`. Step 2 then gives
   the conclusion.

## Provenance

Kaletha and Prasad, *Bruhat–Tits Theory: A New Approach* (2023), use this computation of the
rational points of a torus that splits over a Galois extension in the proof of Lemma 6.4.10
(printed pp. 227–228). Borel, *Linear Algebraic Groups*, 2nd ed. (1991), §8 and AG §14 treat
the Galois action on characters and Galois descent of rational points as background. The
Lean proof above follows its own route through the Library's point/character equivalence and
affine Galois descent.
