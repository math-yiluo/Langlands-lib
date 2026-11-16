# The actual determinant dual on finite parabolic representing models

This internal comparison module connects the actual coherent parabolic Lie
determinant dual with the finite quotient-family positivity proposition.
It works in every universe `u`.

For any base map `b : S' ⟶ S`, `ParabolicRepresentative.pushBase` retains
the very same representative group over the parameter scheme. It composes
its inclusion with the standard ambient isomorphism between the iterated
and direct group pullbacks. Parabolicity is preserved by this isomorphism,
and `baseChangeEquiv_range` identifies the represented subgroup with the
canonical image under `baseChangeEquiv`.

`parabolicLieDeterminantDualBaseChangeIso` compares the value of the original
coherent determinant dual restricted along `b` with the value of the coherent
determinant dual of the pulled-back group. It applies the existing determinant
dual comparison to the pushed representative. The representative's underlying
group is unchanged, so its Lie determinant dual is definitionally the one
attached to the original chosen representative of the pulled-back family.
This construction allows arbitrary schemes and arbitrary base maps.

`parabolicLieDeterminantDualUniversalBaseChangeIso` specializes that comparison
to the universal family of any supplied representing scheme. The representation
on the restricted original presheaf is transported by the canonical
`parabolicPresheafBaseChangeIso`. Thus both compared bundles are actual line
bundles on the same scheme, attached to the same family under that identification.
The ampleness equivalence follows by transporting global sections and their
generation loci along the resulting underlying module-sheaf isomorphism,
using the established `IsAmple.of_iso`.

On an affine base `Spec R`, a finite family of actual relative parabolics
with `HasUniformParabolicFieldTypes j` supplies the existing finite quotient
representation. `finiteAffineParabolicRepresentation_universal` proves that
the representing equivalence sends the identity parameter to exactly
`finiteAffineParabolicFamily hG j hj`. This is the identity restriction law
for the actual coproduct family used to define the quotient chart.
Consequently, `finiteAffineParabolicDeterminantDual_universal` identifies
the coherent universal bundle with exactly the dual of the chosen actual
quotient-family representative's Lie determinant.

The final three lemmas assume the still separate proposition
`FiniteAffineParabolicDeterminantDualAmpleStatement.{u}`. They apply it to
this precise family to obtain ampleness on the finite quotient representer,
then obtain intrinsic ampleness of the coherent bundle, and transport that
ampleness to every supplied representer using the existing
`PresheafLineBundle.isAmple_iff_universal`. These implications introduce no
noetherian, splitting, constant-rank or nonempty-index premise.

All constructions are derived from the actual representative, ambient
comparison, finite quotient representation and coherent bundle APIs.
The geometric positivity proposition is a hypothesis of the ampleness
implications, not a result proved here. This module supplies neither its
geometric proof nor effective descent nor the host arbitrary-base smooth
proper representability theorem.
