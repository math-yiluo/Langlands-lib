# Connectedness of the actual two-power torsion closure

This derived intermediate result proves
`Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureConnectedStatement.{u}`:
for every algebraically closed characteristic-zero field `K : Type u` and every
actual bundled abelian scheme `A` over `Spec K`, the Zariski closure of the actual
section-defined `twoPowerTorsionLocus A` is connected, including nonemptiness.
The universe `u` is arbitrary. It does not assert density or construct a closed
subgroup scheme.

The implemented route uses a topological observation. A Noetherian space has
open connected components. Its connected-component quotient is therefore a
compact discrete space, hence finite. A continuous surjective self-map induces
a surjection on this finite set and consequently a bijection. Suppose it fixes
a point and every point of a dense subset maps to that fixed point after some
number of iterations. Injectivity on connected components then places every
point of the dense subset in the fixed point's component. That component is
closed, so it is the whole space.

For such an algebraically closed characteristic-zero field, the actual abelian
scheme is Noetherian because it is proper and of finite type over the field.
Its torsion closure is a Noetherian subspace. The preceding
multiplication-invariance proof supplies the continuous surjective self-map
given by multiplication by two on this closure. The underlying point of the
identity section is fixed. Evaluating the actual section group law shows that
the `n`-fold iterate of multiplication by two sends a section to its `2^n`-th
power. Thus every actual two-power torsion point eventually maps to the
identity. These points are dense in their own closure by definition, so the
topological observation applies.

The result is internal to the density development, motivated by Edixhoven, van
der Geer and Moonen, *Abelian Varieties*, Chapter V, section 3, Theorem (5.30),
printed page 84 / PDF page 88, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`. Its proof route is a
finite-component argument and assumes no numerical torsion count or
polarization.
