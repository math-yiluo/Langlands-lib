# Points of an affine group read in its corepresented model

Author: Worker 1423.

Helper module for the proof of
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement`.
All declarations are in namespace `Langlands.GroupScheme.Dynamic.GradedCoordinates`.
`G` is an affine group scheme over a field `k`. Its corepresented model is
`AffineCoordinates.functor G`, with corepresentation `AffineCoordinates.corepresentation G`
and isomorphism `AffineCoordinates.groupSchemeIso G`.

## Declarations

- `modelPoint G A : G.affinePoints A →* (AffineCoordinates.functor G).obj A`: the point
  `x ≫ ψ⁻¹` of the model, read by the Library's `affinePointsEquiv`. `modelPoint_naturality`,
  `modelPoint_injective` and `modelPoint_surjective` hold.
- `mem_weightSubgroupFunctor_iff`: an affine point lies in the Library's
  `weightSubgroupFunctor e ψ φ b P` exactly when its model point lies in
  `weightSubgroup e (modelAction e ψ φ b) P`. This uses `pointsEquiv_eq_affinePointsEquiv`
  and `map_mem_weightSubgroup`.
- `modelAction_act_modelPoint`: the model torus action on model points is the original
  action, transported (`AutomorphicAction.transport_act`).
- `toBase A`: the structure map of `Spec A` to the identity test object; `toBase_naturality`.
- `constantFamily G g₀ A`: the model point of `toBase A ≫ g₀` for a rational point `g₀`;
  `constantFamily_naturality`.
- `constantFamily_fixed`: if `g₀` lies in the Library's `torusCentralizer i`, the constant
  family is fixed by the model action of `AutomorphicAction.conjugation i`
  (`conjugation_act`).
- `cocharModelAction G χ`, `idExponent`: the model action of conjugation through a cocharacter
  `χ`, with `𝔾_m` split by the Library's `splitTorus.gmIso`, and the exponent vector of the
  identity character. `idExponent_ne_zero` holds.
- `mem_weightFiltration_iff_modelPoint`, `mem_unipotent_iff_modelPoint`: for smooth `G`,
  membership of an affine point in `weightFiltration (conjugation χ) (𝟙 _) r`, and in
  `Dynamic.unipotent χ`, read in the model. These use
  `weightFiltration_eq_weightSubgroupFunctor_cyclicTail` and
  `dynamicUnipotent_eq_weightFiltration`.

## Provenance

Internal plumbing between published constructions; no new mathematics.
