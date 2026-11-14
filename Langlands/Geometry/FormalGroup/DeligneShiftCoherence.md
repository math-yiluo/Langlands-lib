# Zero, addition and inverse comparisons for actual integer Deligne shifts

This module constructs natural zero, addition and cancellation isomorphisms
for the integer shifts of actual framed lattices and all four preliminary
Deligne sheaf data. Every integer shift is an equivalence with inverse the
opposite shift. The resulting maps on preliminary isomorphism classes satisfy
the zero and addition laws, are bijections, and form an additive action of
the integers.

The source objects are those of Drinfeld, *Coverings of p-adic Symmetric
Regions* (1976), Section 2 A, printed pp.109–110 (PDF pp.3–4), registered as
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
Drinfeld specifies the cyclically graded flat coefficient lattice, invertible
tangent summands, homogeneous locally generating map `u`, and rational
degree-zero frame there. The integer shifts are the constructed operations
of `DeligneIntegerShift`; their comparisons and equivalences in this module
are internal derived infrastructure, not additional theorems stated in the
article.

## Parameters and scope

All types and sheaf categories use the common universe `u`. The lattice
construction uses a commutative ring `O`, a positive integer `d` expressed
by `[NeZero d]`, an element `π : O`, a topological space `X`, and a field `F`
with an `O`-algebra structure. Framed shifts and their comparisons require
`hπ : algebraMap O F π ≠ 0`. For all four data, `X` is the underlying
topological space of a scheme `S` and `φ : O →+* Γ(S, ⊤)` supplies its
structural scalars. The auxiliary graded-sheaf comparisons work on a general
site with a sheaf of commutative rings and a scalar section.

The algebraic constructions need no local-field, nilpotence or flatness
assumption on `F` over `O`. The original lattice's flatness remains part of
the imported lattice object. Shift parameters are arbitrary integers.
The target quotient is `SheafPreDatum.IsoClass`, the actual quotient by
existence of an isomorphism preserving all four preliminary data.

Raw shifts have the previously computed `π^k` correction in the literal
normalized determinant condition. This module supplies no action on
admissible classes and no normalized `GL` or `PGL` action. It does not
construct base change, an exterior-subsheaf comparison, a representing
object or a universal object. Those obligations remain separate.

## Actual splittings and the frame criterion

`LatticePiSheaf.rationalInclusionSplitMono` applies the actual rationalization
functor to the homogeneous projection and splitting equation already
constructed in `DeligneLatticeBaseChange`. Its retraction is the
rationalization of `M.projection i`, and functoriality carries
`M.inclusion i ≫ M.projection i = 𝟙 _` to the required equation.
The instance `rationalInclusion_isSplitMono` consequently makes every
rational homogeneous inclusion monic. This uses preservation of a specific
splitting by a functor, without assuming preservation of arbitrary
monomorphisms by tensor product.

`LatticePiSheaf.Hom.rationalInclusion` rationalizes the genuine homogeneous
inclusion square for every lattice morphism.
`FramedLatticePiSheaf.frame_iff_total` uses this square and cancellation of
the target's split monic inclusion to characterize frame preservation:
the degree-zero frame square holds if and only if the total rational
frame square holds.

`FramedLatticePiSheaf.isoOfTotalFrame` lifts a genuine lattice isomorphism
once its forward total-frame square is proved. The criterion supplies the
forward framed map. Its inverse frame square follows by composing that
equation with the rationalized inverse component and using the lattice
isomorphism's inverse equation. Thus the inverse framed map is derived
from the actual lattice isomorphism.

## Constructed comparisons

The grading convention is that new degree `i` is old degree `i+k`. The
total sheaves and their Pi operators are unchanged.
`GradedPiSheaf.shiftIntZeroIso` and `shiftIntAddIso` use identity maps on
the total Pi sheaf and verify homogeneity by the integer-to-cyclic-degree
identities. `LatticePiSheaf.shiftIntZeroIso` and `shiftIntAddIso` use
identity total maps and actual equality transports on component sheaves.
Their inclusion squares follow from `component_eqToHom_inclusion`, and
their inverse equations follow from extensionality on total lattice maps.

For a framed lattice `M`, write `P` for its actual total rational Pi
automorphism. The imported total-frame formula is

```
frameToTotal(shiftInt M k) = frameToTotal(M) ≫ (P^k).hom.
```

`frameToTotal_comp_totalId` states explicitly that rationalizing the total
identity does not change the total frame.
`FramedLatticePiSheaf.shiftIntZeroIso` and `shiftIntAddIso` lift the lattice
comparisons through `isoOfTotalFrame`. Their total-frame checks reduce
respectively to `P^0 = 1` and
`(P^k).hom ≫ (P^l).hom = (P^(k+l)).hom`. The latter uses the reversed
composition convention in the automorphism group and commutativity of
integer addition.

`FramedLatticePiSheaf.shiftIntCancelIso k l h`, for `h : k+l=0`, lifts
the existing lattice cancellation isomorphism. Its frame equation uses
the same power law followed by `h` and the zero power. Forward and inverse
total maps are identities for all three comparisons.

`SheafPreDatum.shiftIntZeroIso`, `shiftIntAddIso` and `shiftIntCancelIso`
combine the framed comparisons with their genuine graded tangent
comparisons. Preservation of total `u` follows because both total maps
are identities. The imported category then also gives preservation of
the specified homogeneous restrictions of `u`. The tangent line objects
and local generation remain those of the constructed integer shifts.
The inverse equations use extensionality on the actual eta and tangent
maps.

## Naturality, equivalences and classes

In both `FramedLatticePiSheaf` and `SheafPreDatum`, the declarations
`shiftIntZeroNatIso`, `shiftIntAddNatIso` and `shiftIntCancelNatIso`
assemble these comparisons into natural isomorphisms. Naturality reduces
by extensionality to composing the unchanged total maps with identities.
The declaration `shiftIntEquivalence k` takes shift by `k` as its functor
and shift by `-k` as its inverse. Its unit is the inverse cancellation
comparison and its counit the cancellation comparison in the other
order. The required triangle equation reduces to the identity equation
on the actual total sheaves.

`SheafPreDatum.IsoClass.shiftInt_zero` and `shiftInt_add` use quotient
induction and the corresponding genuine four-data isomorphisms. They
give

```
shiftInt 0 q = q,
shiftInt l (shiftInt k q) = shiftInt (k+l) q.
```

`SheafPreDatum.IsoClass.shiftIntEquiv k` has inverse shift by `-k`,
with both inverse equations derived from these class laws.
`shiftIntAddAction` packages the class maps as an `AddAction ℤ`; its
addition axiom uses the class addition law and commutativity of integer
addition. This is a named action structure and does not install a global
instance. All conclusions concern the actual preliminary classes defined
by the four-data category.
