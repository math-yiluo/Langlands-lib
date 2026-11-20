# Conjugate self-duality of the automorphic `GL(1)` realization of a Hecke character

Module `Langlands.Automorphic.RankOneHeckeConjugateSelfDual`. Author: Worker 5086
(Task 7783). These are internal helper results and cite no source. The module sets
`autoImplicit false` and `backward.isDefEq.respectTransparency false`. It declares the
function-space `AddCommGroup` instances locally. Several proofs about the line use
`set_option maxHeartbeats 2000000`.

Throughout, `E` is a CM field, `χ : HeckeCharacter E` and
`hχ : ∀ x, χ (ideleClassComplexConj x) = (χ x)⁻¹`. This is the published
`Harris.IsConjugateInverse χ`, written out.

## Determinant scalars under conjugation (namespace `RankOneHecke`)

- `adelicConj_pair`: the published adelic conjugation `adelicConj` is the pair of the infinite
  and finite conjugations.
- `adelicDeterminant_adelicConj`: `χ(det(c g)) = χ(det g)⁻¹` for every adelic matrix `g`. The
  determinant commutes with the ring automorphism, and `hχ` applies to the class of `det g`.
- `adelicDeterminant_ofFinite_finiteConj` and `_ofInfinite_infiniteConj` are the same identity
  for finite and for archimedean matrices.
- `matrixConj` is entrywise conjugation of archimedean matrices, a continuous real-linear map.
  `matrixConj_apply` and `matrixConj_one` are its basic facts.
- `characterDifferential_lieConj`: the derivative of `χ ∘ det` at `1` is odd under the CM
  involution `lieConj` of the Lie algebra. In the coordinate extension `Ec` of
  `χ ∘ det` the product `Ec (conj M) · Ec M` equals `1` near `1` by the previous identity.
  Differentiating it at `1`, where `Ec 1 = 1`, gives `D(lieConj X) + D(X) = 0`.

## The pairing on the line

- `constant_isSmoothVector`, `constant_isFiniteVector` and
  `constant_isContragredientFunctional`: every functional on the constant line is smooth and
  compact-finite. The finite action on constants is trivial and the dual is finite-dimensional.
  `twist_isContragredientFunctional` transfers this to the twisted line by the published
  `isContragredientFunctional_comp_heckeDeterminantTwistEquiv_symm`.
- `lineScalar χ` reads the scalar of a vector of the line, and `lineVector χ` is the basis
  vector `χ ∘ det`. The lemmas `lineScalar_twist`, `eq_twist_lineScalar`, `eq_lineScalar_smul`
  and `lineScalar_lineVector` give the coordinate identities.
- `lineScalar_finite`, `lineScalar_compact` and `lineScalar_lie`: the finite and compact
  operators multiply the scalar by `χ(det)`, and the real Lie operator multiplies it by the
  derivative of `χ ∘ det`. These use the published `heckeDeterminantTwistEquiv_finite`,
  `_compact` and `lieAction_heckeDeterminantTwistEquiv`. The constant line has trivial actions.
- `linePairing χ` is the bilinear form `B(y, x) = φ(y) φ(x)`, with `φ = lineScalar χ`.
  `linePairing_finite`, `_compact` and `_lie` give its invariance in the form required by the
  published `IsConjugateSelfDual`: `B(g^c y, g x) = B(y, x)` for finite and compact `g`, and
  `B(X^c y, x) + B(y, X x) = 0` for Lie elements. These follow from the three identities
  above. `linePairing_flip_injective` and `linePairing_flip_surjective` show that `B`
  identifies the line with its dual.
- `twist_isConjugateSelfDual`: the twisted constant line is conjugate self-dual.
- `cuspidal_isConjugateSelfDual χ hχ`: `(cuspidal χ).isoClass.IsConjugateSelfDual`, by the
  published `isoClass_isConjugateSelfDual_iff`.
