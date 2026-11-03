# Proof of the cyclic weight filtration statement

This module proves `Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement`
(`Rational.WeightSemigroupStatement`, Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd
ed., Lemma 3.3.8). Declarations are in namespace `Langlands.GroupScheme.RelativeRoot`.

## Statements

- `isAffineHom_affineCoordinates`: the corepresented model
  `groupScheme (AffineCoordinates.functor G) (AffineCoordinates.corepresentation G)` of an
  affine group `G` over a field is affine over the base.
- `cyclicWeightFiltration : CyclicWeightFiltrationStatement.{u}`. Let `k` be a field, `G` a
  smooth affine group over `k`, `S` a split torus acting on `G` by `b`, `a ≠ 0` a character of
  `S` and `r > 0`. Then:
  - `weightFiltration b a r` is normalized by `weightFiltration b a 1`;
  - every representative `j : H ⟶ G` of `weightFiltration b a r` has a group scheme `V`, a
    morphism `q : H ⟶ V` and actions `c` of `S` on `V` and `d` of `S` on `H`. The morphism `q`
    is an fppf quotient by `(weightFiltration b a (r + 1)).comap j`, and `c` has a unique
    weight vector structure of weight `r • a`. Moreover, `d` lifts `b` along `j`, and `q`
    intertwines `d` with `c` on all test schemes.

## Proof

Fix the data of the statement:
- a field `k` and a smooth affine group `G`;
- a split torus `S` with action `b` and splitting `φ : S.toGrp ≅ splitTorus I`;
- `a ≠ 0` and `r > 0`.

`G.X.left` is affine (`isAffine_of_isAffineHom`). The model is
`AffineCoordinates.functor G` with its corepresentation and the isomorphism
`AffineCoordinates.groupSchemeIso G`. The model is affine over the base by
`isAffineHom_affineCoordinates`. Its coordinate algebra is formally smooth and of finite type
(`AffineCoordinates.formallySmooth_algebra`, `finiteType_algebra`, from Worker 1239's bridge
`Rational.TorusActionBridge`). The conclusion is `cyclicWeightFiltration_of_model`
(`Rational.CyclicWeightQuotientAssembly`) for this model.

`isAffineHom_affineCoordinates` holds because the model's structure morphism is the
structure morphism of `Spec` of the coordinate algebra (`algSpec_obj_hom`), and a morphism
between affine schemes is affine.

## Provenance

The proved statement is the Library's formalization of Conrad–Gabber–Prasad, *Pseudo-reductive
groups*, 2nd ed., Lemma 3.3.8 (printed pp.111-112), as fixed by the task contract. The proof
route is internal to this formalization: explicit weight subgroups of the coordinate ring,
their polynomial structure, maximality by the graded vanishing theorem and tangent rigidity,
and an explicit vector-group quotient. The modules are by Worker 1224 and Worker 1239.
