# The adjoint determinant on a dynamic unipotent Lie algebra in graded coordinates

Author: Worker 1423.

Helper module for the proof of
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentVectorFiltrationStatement`.
All declarations are in namespace `Langlands.GroupScheme.Dynamic.GradedCoordinates`.

Throughout, `G` is a smooth affine group over a field `k`, `χ` a cocharacter,
`iU : U ⟶ G` represents `Dynamic.unipotent χ` (`hU`), and `x` are graded polynomial
coordinates of positive weights `d i` on the first cyclic weight subgroup of the model, as in
`Rational.CyclicWeightCoordinates`.

## Declarations

- `aeval_inr`: evaluating a polynomial at a vector of pure infinitesimals `ε w` in `k[ε]` gives
  `coeff 0 p + ε ∑_j coeff (single j 1) p * w j`. The proof is by induction on `p`.
- `dualTest k`, `baseTest k`, `unipotentCut G χ`, `unipotentCorep G χ`: the test algebras
  `k[ε]` and `k`, and the cut functor of the first cyclic weight subgroup of
  `cocharModelAction G χ` with its corepresentation.
- `lieCutPoint G χ hU y`: the cut point of the model point of `y ≫ iU` for a dual-number point
  `y` of `U`. It lies in the first cyclic weight subgroup by `mem_unipotent_iff_modelPoint`. It
  is multiplicative (`lieCutPoint_mul`), natural (`lieCutPoint_affineMap`), and for a Lie kernel
  element its reduction is trivial (`lieCutPoint_reduction`).
- `fst_coord_lieCutPoint`: the coordinates of the cut point of a Lie kernel element have zero
  constant part.
- `lieCoord G χ hU x`: the infinitesimal parts of these coordinates. It is additive
  (`lieCoord_add`, by the Library's `snd_coord_mul`) and `k`-linear (`lieCoord_smul`, via
  `epsilonScale_snd`), injective (`lieCoord_injective`) and surjective
  (`lieCoord_surjective`, using representability by `iU`). `lieCoordEquiv` is the resulting
  linear equivalence `Additive (lieKernel U k) ≃ₗ[k] (Fin n → k)`.
- `mem_torusCentralizer_of_centralizer`: the image `m ≫ iZ` of a rational point of a
  representative of `Dynamic.centralizer χ` commutes with `χ`
  (`torusCentralizer_gm_eq_dynamicCentralizer`).
- `lieCutPoint_act`: the Library's `centralizerAdjointAction hZ hU` at the constant dual-number
  point of `m` corresponds to `cutConj` for `constantFamily G (m ≫ iZ)`
  (`centralizerAdjointAction_act_comp`).
- `centralizerMatrix G χ hx hbij hZ m`: the conjugation matrix `conjMatrix` of that constant
  family.
- `lieCoord_differential`: in Lie coordinates, the differential
  `(centralizerAdjointAction hZ hU).differential (toBase (baseTest k) ≫ m)` is multiplication by
  `centralizerMatrix`. This combines `coord_cutConj`, `aeval_inr`, and the vanishing constant
  term of the weighted homogeneous `conjPoly`.
- `det_differential`: the determinant of that differential is `det (centralizerMatrix …)`
  (`LinearMap.det_conj`, `LinearMap.det_toLin'`).
- `rationalPointEquiv_eq_toBase`: the Library's `rationalPointEquiv` is precomposition with
  `toBase` (maps to the terminal object agree).
- `rationalCharacterEval_determinantCharacter`: the rational adjoint determinant character at
  `m` equals the determinant of that differential. This combines
  `rationalCharacterEval_eq_affineUnitsEquiv` with the Library's
  `determinantCharacter_affinePoints`.

## Provenance

Internal. The identification of `Lie(U_G(λ))` with the positive weight part of `Lie(G)` is
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed., Proposition 2.1.8(1). Here the Lie
algebra is only used through explicit coordinates.
