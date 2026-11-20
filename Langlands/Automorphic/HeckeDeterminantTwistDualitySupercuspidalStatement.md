# Conjugate self-duality and supercuspidality under Hecke determinant twists

`Langlands.Automorphic.HeckeDeterminantTwistConjugateSelfDualStatement`
preserves conjugate self-duality on actual operator realizations over
CM fields when the twisting Hecke character is conjugate-inverse.
The equation `ν.complexConj = ν⁻¹` is pointwise conjugate inversion by
`HeckeCharacter.complexConj_apply`.
`Langlands.Automorphic.HeckeDeterminantTwistSupercuspidalStatement`
preserves supercuspidality at a supplied place of an actual cuspidal
spectral presentation under a twist by any Hecke character. It retains
the independent presentation carrier universe.

## Conjugate self-duality

Pull the bilinear form back in both arguments along the inverse of
`OperatorRealization.heckeDeterminantTwistEquiv`. In the finite and
compact invariance equations, the two scalar factors multiply to
one. The determinant commutes with arithmetic conjugation by
`AdelicGL.determinant_adelicEquiv`, and `ν` takes inverse values on
conjugate idele classes.

For Lie invariance, the shift on a real generator is the derivative
at the identity of the smooth infinite determinant character.
Use `ArchimedeanGL.envelopingShift_generator` and
`OperatorRealization.lieAction_heckeDeterminantTwistEquiv`.
In the matrix chart at the identity, the real path `1 + t X` is
invertible for small `t`, and its conjugate is `1 + t lieConj X`.
The product of the two character values is identically one near
zero. The product rule gives opposite scalar shifts on `X` and
`lieConj X`, so the sum in the Lie invariance equation is preserved.

The linear equivalence preserves injectivity of the partial pairing.
The lemmas
`isContragredientFunctional_comp_heckeDeterminantTwistEquiv` and
`isContragredientFunctional_comp_heckeDeterminantTwistEquiv_symm`
transport the smooth and compact-finite functional conditions in
both directions, giving the required image of the partial pairing.
For a cuspidal class, use `isoClass_isConjugateSelfDual_iff` at its
actual representative.

## Supercuspidality

`CuspidalSpectralPresentation.heckeDeterminantTwistLocalComponentEquiv`
compares the component of the twisted presentation with the actual
twist of the old component. The local twisting character is smooth
and trivial on determinant-one matrices. Use the local twist
equivalence and the preservation of irreducibility and
admissibility to compare the canonical p-adic classes.
`GeneralLinear.isSupercuspidal_twist_iff` gives the Jacquet-vanishing
condition, and `LocalRealization.IsSupercuspidal.of_isoClass_eq`
transfers it to the component of the twisted presentation. The
cuspidal class corollary uses `hasSupercuspidalComponent_iff` to
choose a presentation at the supplied representative.

## Provenance

The output properties come from Harris's Proposition 4.8, printed
pp. 201–203. Henniart, §2.2, printed p. 444, specifies the twist by
an idele-class quasicharacter composed with determinant. The
preservation assertions here are derived for the Library's actual
operator and local realization definitions by the pairing and
Jacquet-module arguments above.
[Harris 1998](https://arxiv.org/abs/math/9611226), [Henniart 2000](https://doi.org/10.1007/s002229900033)
