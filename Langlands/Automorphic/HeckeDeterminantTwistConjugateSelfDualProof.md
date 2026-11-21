# Conjugate self-duality under the actual Hecke determinant twist

`Langlands.Automorphic.heckeDeterminantTwistConjugateSelfDual` proves the exact
[Library statement](HeckeDeterminantTwistDualitySupercuspidalStatement.md#conjugate-self-duality).
The proof is for an arbitrary operator realization `S` of `GL_n` over a CM
number field and any Hecke character `ν` with `ν.complexConj = ν⁻¹`. It uses no
irreducibility, cuspidality, or unitarity hypothesis.

Write `T = S.heckeDeterminantTwist ν` and let `e` be the underlying linear
equivalence of `S.heckeDeterminantTwistEquiv ν`, multiplication by `ν ∘ det`
on the actual functions. From a conjugate contragredient pairing `B` on `S`,
`LinearMap.compl₁₂` gives the pairing `B'(y, x) = B(e⁻¹ y, e⁻¹ x)` on `T`.

- **Finite and compact invariance.** Evaluating the character equality at
  each idele class gives pointwise conjugate inversion. The published
  `RankOneHecke.adelicDeterminant_ofFinite_finiteConj` and
  `RankOneHecke.adelicDeterminant_ofInfinite_infiniteConj` use determinant
  equivariance to give inverse character values on conjugate matrices.
  For the compact operators, `compactConj_val` identifies conjugation on the
  underlying infinite adelic matrices. The finite and compact covariance
  formulas for `e` then give two scalar factors whose product is one, so
  bilinearity reduces the two required equalities to the invariance of `B`.
- **Lie invariance.** On a real Lie generator, `envelopingShift_generator`
  and the complexification formula identify the scalar shift with the
  derivative `D` of the infinite determinant character. The proof reuses
  `RankOneHecke.characterDifferential_lieConj`: in the real matrix chart at
  the identity, the product of the character at a matrix and its conjugate
  is identically one near the identity. The product rule, evaluated on
  the real Lie direction `X`, gives `D(lieConj X) + D(X) = 0`. The
  `RankOneHecke` identities used here are stated for every `n` despite their
  namespace. Applying `lieAction_heckeDeterminantTwistEquiv` to each argument
  supplies precisely these shifts. Their two contributions to the Lie
  invariance equation for `B'` cancel, leaving the equation for `B`.
- **The partial pairing.** At `x` the functional `B'(·, x)` is the old
  partial functional at `e⁻¹ x` precomposed with `e⁻¹`. The `_symm`
  functional-transport lemma makes it smooth for the finite adeles and
  finite for the standard compact group. The linear equivalence preserves
  injectivity of the partial pairing. Conversely, precompose a
  contragredient functional on `T` with `e`; the forward transport lemma
  makes it a contragredient functional on `S`. Its old pairing witness `x`
  then gives the witness `e x` on `T`. This proves surjectivity onto the
  full space of contragredient functionals, not just nondegeneracy.

This is a derived Library compatibility for the determinant untwisting step
in Harris's Proposition 4.8, as explained in the statement note. It concerns
only the conjugate-self-duality target, not the adjacent supercuspidality target.
