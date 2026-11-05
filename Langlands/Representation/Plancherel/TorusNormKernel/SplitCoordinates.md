# Regular functions on a split torus through its coordinate characters

Author: Worker 1505.

This is a derived helper for the
[torus norm-kernel compactness proof](../TorusNormKernelCompactnessProof.md).
Declarations are in the namespace `Langlands.Plancherel.TorusNormKernel`.
Let `E` be a field with a topology. All point sets carry the published
`rationalPointTopology`.

- `continuous_rationalPointAlgebraHom X a`: for an affine `X` over `Spec E`
  and a global section `a`, the function `p ↦ rationalPointAlgebraHom E X p a`
  is continuous. It is evaluation at `a` composed with the published
  homeomorphisms `rationalPointHomeomorph` and `affineSchemePointHomeomorph`.
- `isoRationalPointsHomeomorph e`: an isomorphism `e : G ≅ H` of affine group
  schemes over `Spec E` gives a homeomorphism of rational points. Its function
  is postcomposition with `e.hom` (`isoRationalPointsHomeomorph_apply`).
  Continuity in both directions is the published `continuous_rationalPointMap`.

Assume now that `E` is a topological ring and `I` is a finite index type.

- `splitCoordinatesHomeomorph I`: the rational points of
  `splitTorus (Spec E) I` are homeomorphic to `I → Eˣ`. This composes the
  published `rationalPointsAffineHomeomorph` with
  `splitTorus.affinePointsHomeomorph`, the same construction as
  `SplitTorus.coordinatesHomeomorph`, here for an arbitrary topological ring.
  `splitCoordinatesHomeomorph_apply` identifies coordinate `i` with the value of
  the projection character, via `rationalCharacterEval_eq_affineUnitsEquiv`.
- `splitCharacter e i`: for `e : T ≅ splitTorus (Spec E) I`, the rational
  character `e.hom ≫ Pi.π _ i` of `T`.
- `exists_continuous_of_splitCharacters e a`: for affine `T` and every global
  section `a` of `T`, there is a continuous `Φ : (I → Eˣ) → E` with
  `rationalPointAlgebraHom E T.X s a = Φ (fun i => rationalCharacterEval (splitCharacter e i) s)`
  for every rational point `s`. Take
  `Φ = (evaluation at a) ∘ h.symm`, where `h` is the composite homeomorphism
  `isoRationalPointsHomeomorph e` followed by `splitCoordinatesHomeomorph I`.
  The coordinates of `h s` are the values of the split characters, by
  `rationalCharacterEval_characterRestrict`.

Provenance: internal derived infrastructure from the published point-topology
and split-torus coordinate API. It cites no literature.
