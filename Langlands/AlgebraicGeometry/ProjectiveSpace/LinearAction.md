# Actual scheme action of linear coordinate equivalences

For every commutative ring `R : Type u`, natural number `n`, and linear
equivalence `e` of `Fin (n+1) → R`, `linearAction R n e` is an actual scheme
endomorphism of the published `ProjectiveSpace R n`. Apply Mathlib's `Proj.map`
to `gradedLinearSubstitution R n e.toLinearMap`, using its proved
irrelevant-ideal image condition. No field or nontrivial-ring hypothesis is
required.

`linearAction_refl` identifies the action of the identity linear equivalence
with the identity scheme morphism. `linearAction_comp` proves

```text
linearAction R n e ≫ linearAction R n f = linearAction R n (e.trans f).
```

Thus the action first applies `e` and then `f`, as on coordinate vectors.
Polynomial substitution reverses composition, and the contravariant `Proj.map`
composition theorem reverses it again. Their identity and composition
theorems give these equalities of scheme morphisms. In particular,
`linearActionIso R n e` has hom `linearAction R n e` and inverse
`linearAction R n e.symm`. The two composites are identity scheme morphisms
by the corresponding linear-equivalence identities.

`linearAction_comp_toSpec` proves that the action commutes with the published
structure morphism to `Spec R`. Its proof uses the affine open cover associated
with the graded substitution. On each cover member, the `Proj.map` chart
formula and the chart's structure-map formula reduce the required equality
to equality of ring maps from `R` into a degree-zero homogeneous localization.
Both maps send a coefficient `r` to the same fraction `r/1`, since polynomial
substitution fixes coefficients. Extensionality of the affine cover then
gives equality of the global scheme morphisms.

`linearAction_mem_iff` describes the underlying point map exactly: a polynomial
`x` belongs to the homogeneous prime of `linearAction R n e p` if and only if
its substitution by `e` belongs to the homogeneous prime of `p`. This is the
prime pullback in the actual `Proj.map` construction. Consequently,
`linearAction_linearForm_mem_iff` says that incidence with the polynomial of
a coordinate functional `ℓ` transforms to incidence with the polynomial of
`ℓ.comp e.toLinearMap`. The proof uses the published substitution formula on
degree-one polynomials.

`linearSubstitution_smul_id_homogeneous` proves that substituting the scalar
linear map `a • LinearMap.id` into a homogeneous polynomial of degree `d`
multiplies it by `a^d`. This holds for every scalar, including nonunits.
The proof uses weighted-homogeneous induction: it is immediate for zero
and sums, and the sum of exponents of a degree-`d` monomial gives the
power `a^d` after substitution of `a • X_i` into each variable.

For a scalar unit `a : Rˣ`, `linearAction_smulOfUnit_apply` proves equality
of every actual image point with its original point. Equality of homogeneous
ideals can be checked on homogeneous elements. On each such element the
substitution factor `a^d` is a unit, so it preserves prime membership.

`homogeneousLocalization_scalar_map` supplies the structure-sheaf calculation.
For any scalar `a` and any multiplicative subset `P` such that scalar
substitution maps `P` into itself, its induced map on the degree-zero
homogeneous localization is the identity. Represent a localization element
by a numerator and denominator of the same degree. Their substituted
values both acquire the factor `a^d`; cross multiplication proves equality
of the fractions. No cancellation or nonzero-ring hypothesis is needed.

`linearAction_smulOfUnit` proves equality of the scalar-unit action with
the identity as scheme morphisms, including the structure sheaf. Scheme
morphism extensionality reduces this to the point-map equality and the
maps on sections. A section is a dependent family of homogeneous local
fractions. At each point, the previously proved point equality identifies
the source and target prime, and the homogeneous-localization calculation
makes the induced local map the identity. Thus the corresponding sections
are equal on every open subset.

This unit has internal provenance. It combines the existing graded
substitution and irrelevant-ideal proof with Mathlib's projective-spectrum
functor, its affine chart formulas, its coefficient structure morphism,
weighted-homogeneous polynomial induction and homogeneous local fractions.
It does not compare rational points with vector-space projectivization,
establish faithfulness modulo scalars, prove a torsion estimate, or prove the
ordinary fine-representability statement.
