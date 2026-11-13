# The four Deligne sheaf data before admissibility

Drinfeld (1976), §2 A, printed p.109 (PDF p.3), final paragraph, and the
opening of printed p.110 (PDF p.4), describe the sheaf data η, T, u and r.
This module combines the actual flat lattice sheaf, line-component sheaf
and rational frame already constructed, and adds the actual homogeneous
O[Π]-linear map u with its local generation condition. Conditions (a)–(c)
remain to be imposed; these are preliminary data, not Deligne points.

For a scheme S with an actual homomorphism φ:O→Γ(S,top),
`structuralOSheafFunctor` restricts any actual O_S-module sheaf to its
O-module sheaf. It uses the restriction maps from the top open and the
actual homomorphism φ. Thus the coefficients used on every open are the
structural coefficients; no independent O-action is supplied.

`SheafPreDatum` contains a framed flat graded O[Π]-sheaf η and actual
line-component T-sheaf with Π^d=φ(π). The map u is an actual O-linear
sheaf morphism that commutes with Π. Its homogeneous component maps are
required to agree with this same map under the actual inclusions.
Consequently the degree and operator compatibility are attached to u,
and the component maps are not independent maps with unrelated images.
The implementation proves the corresponding section formulas.

The `locallyGenerates` condition says that every T-section, near each
point of its open domain, belongs to the O_S-linear span of actual images
of η-sections. This is the local finite-linear-combination formulation of
the source's epimorphism η⊗_O O_S→T. The implementation records this
explicit local-span condition. It does not construct a tensor sheaf over
O_S or assert a comparison theorem with a separate categorical tensor
epimorphism predicate.

`NilpSheafPreDatum` specializes the construction to Spec B for an actual
object B of `Nilp O π`, using the canonical global-section isomorphism
of Spec B. Nilpotence of the structural uniformizer is proved from B's
existing property. The field F is an O-algebra field; the intended
application takes O to be the integer ring and F its fraction field.

The provenance is derived from the cited source using the previously
constructed concrete sheaves and explicit section conditions. There is
no representing or universal object as input. This module constructs no
admissibility conditions (a)–(c), isomorphism-class Nilp-point functor,
change-of-base operation, PGL action, representability or generic fibre.
