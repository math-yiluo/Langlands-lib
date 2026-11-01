# Mixed point and base pullback of actual Harris polarized Lie classes

This module constructs the mixed point-comparison and base-pullback square for
the actual polarized Harris dimension-and-positive-Lie classes. The result is an
equality of natural transformations over the original Harris level category.
It also constructs the diagonal pullback and, on a connected locally Noetherian
target base, its canonical geometric-point version.

The motivating original is Harris and Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), III.1, printed pp.89–91 / PDF pp.97–99,
especially p.91. It is registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
Those pages define the positive Lie condition, polarized compatible-level
quadruples, their isogeny relation and the canonical independence of their
geometric point. The present mixed square is derived infrastructure for that
functorial construction, using the existing rational-isomorphism quotient.
It does not supply the source's representability or finite-etale conclusions.

## Inputs and actual objects

All arithmetic types and schemes have universe zero. The arithmetic inputs are
the central simple unitary datum `D` over a totally real number field `E`, a
totally complex quadratic extension `F/E`, its algebra `A`, signature charts
`C`, and an imaginary quadratic CM number field `L` mapping into `F`. The
source's imaginary quadratic field, CM field, real field and algebra are
respectively `L`, `F`, `E` and `A`. No additional CM-section condition on the
charts is required here. The positive auxiliary left involution, actual Hodge
form and level functor are those already constructed from `D` and `C`. In
particular, the level category is `HarrisLevel D`, for the original opposite
Harris finite-adelic group.

The bases are actual schemes `S` and `T`, with an arbitrary morphism
`b : T ⟶ S` and a structure map `p : S ⟶ Spec F`; the target structure is
`b ≫ p`. Both bases are quasi-separated. The explicit tensor/Picard inputs
are tensor-pullback comparison invertibility, composition, unit,
associativity, left-unitor and symmetry coherence, Picard-zero pullback,
the Mumford-bundle Picard-zero statement and Picard-zero universal base change.
The finite Weil transition and torsion finite-etale statements and rational
profinite-integer/finite-adele comparison remain explicit too.

On both bases every positive torsion index is invertible and the corresponding
roots-of-unity schemes are finite etale. The ordered-pair additivity inputs for
dual maps are `addS` and `addT`. The family `dualData` supplies dual-scheme,
geometric, inverse-Poincare, evaluation and dual-endomorphism-additivity data
for each source object's own actual abelian-scheme pullback along `b`. It
cannot supply a different output abelian scheme, polarized action, level orbit
or quotient map. This file does not establish existence or choice-independence
of that family. The published full integral dual-naturality and
polarization-base-change theorems are supplied internally by name.

Initially, `s` and `t` are field-valued points of `T`, and `epath` is an
isomorphism between their finite-etale fibre functors. The endpoint fields
may differ. Finiteness of fibres of every finite-etale cover is supplied at
`s`, `t`, `s ≫ b` and `t ≫ b`. No connectedness, local Noetherianness,
algebraic closedness, flatness or reducedness is required for the path square.

The actual representatives and relation are unchanged. A representative
contains a positive polarized abelian scheme, its faithful rational action,
and a monodromy-fixed compatible Weil level orbit. The relation contains an
equivariant rational isomorphism with inverse, a rational unit satisfying the
dual-pullback polarization multiplier equation, and the orbit equation.
The restricted class image has one representative satisfying both geometric
dimension `[E : ℚ] * n²` and the original positive Lie condition. The latter
concerns rank `n` local freeness of the actual positive Lie tensor sheaf and
equality of its two `E` actions. No determinant or trace replacement is made.

## Mixed square and diagonal

`levelDataBaseChange_pointMapRepresentative` proves that the following routes
give equal actual polarized level representatives: change the source
presentation along `pathPushforward b hsb htb epath` and then pull back at `t`,
or pull back at `s` and then change the target presentation along `epath`.
The polarized first component is identical in both routes: point comparison
does not change the object on which `dualData` is evaluated. Sigma
extensionality reduces the orbit component to the proved actual
`weilAdelicLevelBaseChange_transport` square.

`ambientClassBaseChange_pointMap` descends this equality by induction on the
existing quotient. Its two constituent maps already preserve precisely that
quotient relation; no new equivalence relation is imposed.
`classBaseChange_pointMap` then uses subtype extensionality to obtain the
same square on the joint dimension-and-positive-Lie image. The existing
point comparison retains the identical satisfying representative; the existing
pullback actually pulls back that witness and proves both conditions for it.
No dimension invariance under arbitrary rational isomorphism is assumed.

`classTowerBaseChange_pointTransport` gives the square for the entire original
Harris class tower, whose values are in `Type 1`. With `P_s` denoting pointed
pullback at `s`, `M_T(epath)` target point comparison and `M_S(b_*epath)`
source point comparison, its equation is

`M_S(b_*epath).hom ≫ P_t = P_s ≫ M_T(epath).hom`.

`classTowerBaseChangeAlongPath` constructs the diagonal as the right-hand
route. Its component formula is proved, and
`classTowerBaseChangeAlongPath_eq` identifies it with the left-hand route.
`classTowerBaseChangeAlongPath_path_independent` is equality of the entire
natural transformation for any two paths with these endpoints. This follows
from the existing point-comparison path independence, which uses
monodromy-fixed orbit classes rather than fixed frame representatives.
The arrow formula explicitly records naturality for every original Harris
transporter, including inclusions and both existing Hecke legs.

`classTowerBaseChangeAlongPath_inclusion` proves the square with inclusion
into the ambient polarized tower. The ambient route is the actual pointed
ambient quotient pullback followed by ambient point comparison.
`classTowerBaseChangeAlongPath_forgetDimensionLieAction` proves the square
with the existing joint action-class presheaf map for the actual arrow
`Over.mk (b ≫ p) ⟶ Over.mk p`. Point comparison leaves that action class
unchanged, and pointed pullback is already known to agree with this
presheaf's map. These give the equation by associativity of natural
transformation composition.

## Canonical geometric version and scope

For connected locally Noetherian `T` and algebraically closed endpoint
fields, `classTowerGeometricBaseChange` chooses a path from the proved
`geometricPathExists s t hs ht` and applies the diagonal. Its source is the
class tower at `s ≫ b` on `S`, and its target is the tower at `t` on `T`.
`classTowerGeometricBaseChange_eq_path` identifies it with the diagonal
for every supplied path, removing dependence on the auxiliary choice.
`classTowerGeometricBaseChange_eq_transport` writes it as pointed pullback
at `s` followed by the existing canonical geometric-point comparison on `T`.
Its ambient inclusion square, joint action-presheaf square and all-transporter
formula are proved.

When `S` is also connected and locally Noetherian,
`classTowerGeometricBaseChange_eq_pushed_transport` writes the same map as
canonical comparison from `s ≫ b` to `t ≫ b` on `S`, followed by pointed
pullback at `t`. The proof chooses a path on `T`, applies the mixed square,
and uses equality of canonical source comparison with comparison along its
pushed path. It does not assume that the two bases' chosen paths coincide.

The provenance is derived from the proved actual Weil orbit square, the
constructed polarized representative and quotient pullbacks, the original
Harris level functor, the joint representative-image restriction and proved
geometric path existence. This is a pullback with the fixed supplied dual
family. It asserts neither injectivity nor surjectivity of the resulting
maps on polarized moduli classes. It does not yet prove coherence of
successive base pullbacks or independence of the dual family, construct an
unpointed varying-base polarized moduli presheaf, compare its rational
relation with geometric-isogeny equivalence on arbitrary schemes, prove the
source's trace equivalence, construct representing scheme levels or
canonical models, or descend coefficient systems. These remain obligations
of the broader geometry task.
