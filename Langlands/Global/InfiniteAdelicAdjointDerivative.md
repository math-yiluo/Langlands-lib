# The derivative of the adjoint determinant along an identity tangent vector

Module `Langlands.Global.InfiniteAdelicAdjointDerivative`, namespace
`Langlands.Global.InfiniteAdelicGroupPoints`. The setting is that of
`InfiniteAdelicTangentKernel` and `InfiniteAdelicCharacterDerivative`.

## Declarations

- `adjointTangentMatrix F hsmooth j X`: for an affine, locally finite-type group scheme `P`
  over `F`, a morphism `j : G ⟶ P` and a tangent vector `X` at the identity of `G(F_∞)`, it is
  the matrix over `F_∞` of `ε`-coefficients of the coordinate matrix of `Ad_P`. That coordinate
  matrix (`AutomorphicAction.coordinateMatrix` of the conjugation action, in the Library's
  coordinates `Lie.finiteCoordinates P`) is taken at the image under `j` of `tangentPoint X`
  in `P(F_∞[ε])`.
- `regularDerivative_adjointDeterminant`: `D_X (det Ad_P ∘ j) = tr (adjointTangentMatrix j X)`.
  Proof:
  - the value of `det Ad_P ∘ j` at `tangentPoint X` is the unit `characterUnits`
    (`characterUnits_val_eq_evaluation`);
  - by `Lie.adjointDeterminantCharacter_affinePoints` this unit is the determinant of the
    adjoint action on the dual-number Lie kernel of `P` over `F_∞[ε]`, and by
    `coordinateMatrix_det` it is the determinant of the coordinate matrix;
  - that matrix reduces to the identity, since by `coordinateMatrix_naturality` its reduction is
    the coordinate matrix at the reduced point, which is the identity;
  - `det_eq_of_map_fst_eq_one` (module `DualNumberDeterminant`) gives `1 + ε · tr`;
  - by `affinePointEvaluation_tangentPoint_snd` the `ε`-part of the value is `D_X`.
- `mfderiv_halfModulus_one_eq_trace`: the derivative at the identity along `X` of the
  normalizing factor `m ↦ j(m)^{-ρ_P}` is
  `-1/2 · Σ_v mult(v) · Re (tr (adjointTangentMatrix j X))_v`. This combines
  `mfderiv_halfModulus_one` with the previous theorem.

- `adjointTangentMatrix_eq_kernelDifferential`: `adjointTangentMatrix j X` is the tangent
  matrix `kernelDifferential` of the coordinate adjoint representation of `P` at
  `Lie j (B X)`. Here `B X = tangentKernel X` and `Lie j = Lie.targetMapLinear j F_∞`, and the
  point `j(tangentPoint X)` is the dual-number point of `Lie j (B X)`. This is
  `coordinateMatrix_conjugation_snd` (module `AdjointTangentBracket`).
- `trace_adjointTangentMatrix`: `tr (adjointTangentMatrix j X)` is the trace over `F_∞` of
  `ad (Lie j (B X))` on the Lie algebra `Additive (lieKernel P F_∞)` of `P` over `F_∞`, by
  `trace_toEnd_eq_trace_kernelDifferential`.
- `mfderiv_halfModulus_one_eq_trace_ad`: the derivative at the identity along `X` of
  `m ↦ j(m)^{-ρ_P}` is `-1/2 · Σ_v mult(v) · Re (tr_{F_∞} ad (Lie j (B X)))_v`.

The bracket on `Additive (lieKernel P F_∞)` is the Library's `instAffineKernelLieRing`, made a
local instance through `kernelLieRingOfField` and `kernelLieAlgebraOfField`.

## Provenance

Internal. The infinitesimal form of `det Ad` is Jacobi's formula `det(1 + εN) = 1 + ε tr N`,
and the differential of `Ad` is `ad` (Milne, *Algebraic Groups* (2022), §10d). Since
`mult(v) = [F_v : ℝ]`, the sum `Σ_v mult(v) · Re (tr_{F_∞} T)_v` is the real trace of an
`F_∞`-linear map `T`. The module states the sum form and does not prove this identity.
