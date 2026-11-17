# Naturality of the actual torus Kottwitz homomorphisms

`Langlands.Geometry.Building.Kottwitz.torusKottwitzNaturality` proves the
published proposition
`Langlands.Geometry.Building.Kottwitz.TorusKottwitzNaturalityStatement.{u}`
at arbitrary universe `u`.

This is a derived consequence of the norm characterization in
Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Proposition
11.1.1 and its proof, printed pp. 421–422 / PDF pp. 452–453 (registered
source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`).
The book invokes torus functoriality in the proofs of Lemma 11.1.3,
printed p. 422 / PDF p. 453, and Lemma 11.5.1, printed p. 430 / PDF p. 461.
The authors' corrections of 1 November 2024 concern section 11.7 in this
chapter and leave these passages unchanged.

## Scope and equation

Write `K = UnramifiedClosure F` and `E = SeparableClosure F`.
For every nonarchimedean local field `F`, the coefficient field `k` maps to
`K` and `E` in a scalar tower, with `Normal k K`. For actual commutative
group schemes `S,T` over `Spec k`, proofs that both are tori, every actual
morphism `f : S ⟶ T`, and every `x : torusKPoints F k S`, the theorem proves
the statement's equation

```text
(torusKottwitz F k T hT
    (affinePointsTarget S.toGrp (CommGroupScheme.groupHom f)
      (CommAlgCat.of k (UnramifiedClosure F)) x)).toAdd =
  torusInertiaMap k (SeparableClosure F) f (UnramifiedClosure F)
    (torusKottwitz F k S hS x).toAdd
```

Thus the selected map of `T`, applied after `f`, equals the map on inertia
coinvariants applied after the selected map of `S`. These are the actual
norm-characterized `torusKottwitz` maps of `TorusMap`. The targets are
integral geometric cocharacter inertia coinvariants, including torsion.
The theorem retains precisely the published field and torus hypotheses;
it adds no splitness, rank, characteristic or `IsSepClosure k E` hypothesis.

## Implemented proof

The new Lean proof introduces the quantified data and applies the published
`torusKottwitz_natural_of_existence` from `TorusNormNaturality`, supplying
the published theorem `torusKottwitzExistence` from `TorusMapProof`.
The latter proves `TorusKottwitzExistenceStatement.{u}`. In particular it
supplies the norm laws of the selected maps and surjectivity of the source
relative norm at every finite Galois splitting field. No existence premise
remains in the resulting theorem.

The reused naturality proof implements the following norm argument.

1. `exists_commonFiniteGaloisSplittingField_inside` in
   `CentralSurjectionZeroSurjectivity` supplies a common finite Galois
   splitting field `L/K` inside `E` for the two tori after base change to
   `K`. `IsSplitTorus.baseChange_fieldTower_iff` in
   `Langlands.GroupScheme.Torus.BaseChange` identifies these splitness
   witnesses with those for direct base change from `k` to `L`.
2. Surjectivity of the source relative norm lifts `x` to an `L`-coefficient
   point. `baseChangeCoeffEquiv` expresses this lift as a rational point
   of `S_L`.
3. `relativeNorm_natural` in `TorusNormNaturality` commutes the actual
   morphism with the relative finite Galois norm.
   `baseChangeCoeffEquiv_map` identifies the induced point map under the
   rational/coefficient point comparison. The two selected norm laws
   then express both sides using the normalized split valuation at `L`.
4. `torusInertiaMap_projection` in `TorusInertiaFunctoriality` commutes
   the inertia map with projection of a geometric cocharacter.
   `splitValuation_natural` in `TorusNormNaturality` commutes the split
   valuation with the base change of `f`.
   `extendGeometricCocharacters_natural` in the same module commutes
   extension of cocharacters to `E` with postcomposition by `f_E`;
   its proof uses `towerBaseChangeIso_natural` for the comparison of
   iterated and direct base change.

These squares show equality on source norms, which exhaust the source
points. The new theorem packages this existing argument as the exact
unconditional Library statement. Its proof uses torus existence and the
torus norm argument; it has no reductive Kottwitz existence or
functoriality dependency. The target's Lean/Markdown pair and its imported
files are unchanged.
