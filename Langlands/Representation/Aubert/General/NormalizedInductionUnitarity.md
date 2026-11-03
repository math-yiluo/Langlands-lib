# Positive forms on normalized induction from compact quotients

This internal construction equips the actual smooth normalized induction with
an invariant positive definite Hermitian form. The ambient group is locally
compact, Hausdorff and nonarchimedean. Its modular character is assumed trivial.
The actual subgroup `P` is closed, `P \ G` is compact, and `P = M ⋉ U` is an
actual semidirect decomposition with `U` closed. The modular character of `P`
is assumed equal to the restricted Haar modulus of conjugation on `U`.

The generic constructor `Induction.integralInvariantPositiveForm_of_pos`
integrates an algebraic inner product core on the actual covariant function
space. It assumes the measure is positive on every open neighborhood of `1`
and that every translated coefficient pairing is integrable with unchanged
integral. Hermitian symmetry, nonnegativity and sesquilinearity follow from
the corresponding integral identities. To prove definiteness, choose a point
where a nonzero induced function is nonzero. After translating this point to
`1`, the real diagonal pairing is positive on an open neighborhood of `1`;
the measure hypothesis makes its integral strictly positive. Translation
invariance contradicts a zero diagonal integral.

`normalizedInduction_pairing_covariant` applies the actual normalized function
covariance, invariance of the inducing form and conjugate linearity in the
first argument. The half modulus is positive real; its square is the full
restricted modulus, by `closedHalfCharacter_mul_self`.

`compactQuotientNormalizedInductionForm` chooses the measure supplied by
`Induction.exists_compactQuotient_measure`, applies the modular-character
identity to the coefficient covariance and invokes the generic constructor.
The result is a form on the actual `normalizedInductionFunctor` object.
`normalizedInductionFunctor_obj_isUnitarizable_of_compactSpace` records the
corresponding preservation of existence of a form.

The construction is derived from the published compact quotient Bruhat measure
and integral identities, together with the definitions of normalized induction
and invariant positive forms. It requires neither admissibility nor finite
length, and does not construct rational quotient compactness or the parabolic
modular-character identity. Those remain separate geometric inputs. It does
not prove the rational rank-one self-association theorem.

The group and carrier universes `uG` and `uV` are independent; the induced
carrier has universe `max uG uV`. No continuity of the Levi projection is used
to construct this form. The proof uses
`Induction.exists_eval_ne_zero`, `Induction.pairing_isLocallyConstant`,
`InnerProductSpace.Core.normSq_eq_zero`,
`integral_pos_iff_support_of_nonneg`,
`normalizedInductionFunctor_covariant`,
`closedHalfCharacter_mul_self` and
`Induction.exists_compactQuotient_measure`. The last theorem constructs compactly
supported Bruhat densities, normalizes their subgroup averages, and proves the
scalar right-translation identity by Haar integration. This route uses no
Langlands classification, representation-character independence, geometric
lemma, adjointness or cuspidal-support theorem. Other duality declarations in
the imported modules are not used by these constructions.
