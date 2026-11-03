# Kernel difference and cancellation through finite homomorphisms

This derived helper unit constructs the actual kernel difference of two group-scheme
homomorphisms and proves cancellation through a finite homomorphism. The motivation is the
uniqueness argument in Milne, *Algebraic Groups* (2017), Proposition 18.8, printed p. 389 /
PDF p. 405. The accompanying existence proof is outside this unit. The complete official
Milne errata retained on 2026-11-02 corrects the codomain of the lift in that proposition;
this construction makes no choice of lift.

For any base scheme `S : Scheme.{u}`, homomorphisms `a b : C ⟶ H`, and `q : H ⟶ G`
such that `a ≫ q = b ≫ q`, `kernelDifference q a b hab` is an actual morphism
`C.X ⟶ (kernel q).X` over `S`. Its composite with the kernel inclusion is the quotient
`a.hom.hom / b.hom.hom`. It need not be a group homomorphism. Its construction uses
the published `kernelPointsEquiv` for the test scheme `C.X`; the identities
`kernelDifference_comp` and `kernelDifference_one` prove the quotient formula and
preservation of the identity. These definitions and identities are internal consequences
of the represented kernel pullback and group-object laws.

`finiteTargetHom_ext_algClosed` concerns schemes over an algebraically closed field
`k : Type u`. The target is finite over `k`; the source is reduced, preconnected, and
locally of finite type over `k` through the first map. Two morphisms over `k` that agree
at a single source point agree as scheme morphisms. To prove this, Mathlib's
`IsLocallyArtinian.of_locallyQuasiFinite` makes the finite target locally Artinian and
hence discrete. Both underlying continuous maps are locally constant and thus constant
on the preconnected source. The supplied one-point equality gives equality everywhere.
Mathlib's `AlgebraicGeometry.ext_of_apply_eq`, applied to the full source, then proves
equality of actual scheme morphisms; the finite target supplies separatedness and local
finite type. No reducedness condition is imposed on the target.

`finiteTargetOverHom_eq_one_algClosed` applies this rigidity to maps from group schemes,
using their identity point. `finiteKernel_cancel_algClosed` then applies it to
`kernelDifference`: if the full kernel is finite and the source is reduced,
preconnected, and locally of finite type, two homomorphisms with the same composite
are equal. The quotient takes the identity to the identity, so it is one; composition
with the kernel inclusion and the group division law recover equality of the original
homomorphisms.

`finiteHom_cancel` works over every field `k : Type u`. Its source `C` is smooth,
affine over `k`, and connected, and `q : H ⟶ G` is finite as a scheme morphism.
Pull back along `Spec (AlgebraicClosure k) ⟶ Spec k`. Finiteness survives this
pullback and gives a finite scheme-theoretic kernel of the pulled-back homomorphism.
The published geometric-connectedness theorem preserves connectedness of `C`;
smoothness survives base change and the published smooth-reduced theorem supplies
reducedness. The preceding algebraically closed cancellation theorem now applies.
The field extension is faithfully flat, so Mathlib's faithful pullback functor
reflects equality of the underlying morphisms over `k`.

Finally, `IsCentralIsogeny.cancel_of_connectedReductive` obtains the source hypotheses
from `IsConnectedReductive C` and finiteness from `IsCentralIsogeny q`. This is the
uniqueness input for the simply connected central-cover universal property. The
stronger cancellation result does not use centrality, flatness, surjectivity, or
semisimplicity. All fields, including imperfect fields and positive characteristic,
and arbitrary universe `u` are retained. Equality is equality of actual scheme
morphisms and therefore holds on every test scheme, including nonreduced tests.
