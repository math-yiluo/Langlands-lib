# Point independence of actual polarized Weil level classes

This derived construction transports actual polarized Weil level data along an
isomorphism of finite-etale fibre functors. It retains the identical polarized
abelian scheme, descends through the existing rational-isogeny relation, and
constructs a path-independent isomorphism of the compact-open transporter
class towers. Its namespace is
`Langlands.Shimura.PEL.PolarizedWeilLevel`.

The original motivation is Harris and Taylor, *The Geometry and Cohomology of
Some Simple Shimura Varieties* (2001), III.1, printed p.91 / PDF p.99,
registered as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The source asserts canonical independence of the geometric point for its
polarized compatible-level quadruples. This generic module implements the
point comparison for the actual polarized quotient already defined in
`PolarizedWeilLevelClasses`. It does not yet impose the source's dimension,
positive Lie condition, or particular Harris arithmetic datum.

## Inputs and actual objects

Fix `S : Scheme.{u}` with quasi-separated underlying space, a rational algebra
`D : Type v` with a ring involution, a rational `D`-module `V : Type w` with
compatible scalar tower, and a rational bilinear form `ψ`. No dimension,
alternation, nondegeneracy, or number-field hypothesis is added. The actual
polarized object, fixed level orbit, and quotient types are exactly those of
`PolarizedWeilLevelClasses`; no new object or equivalence relation replaces
them. In particular each object contains an actual faithful rational action,
constructed Picard dual and evaluation data, an actual geometric polarization,
and its involution compatibility equation.

The named tensor comparison, composition, unit, associativity, unitor and
symmetry statements, Picard-zero stability, Mumford-bundle Picard-zero and
Picard-zero universal base-change statements remain explicit inputs. So do
finite Weil transition compatibility, the rational profinite-integer/finite-
adele comparison, torsion finite-etaleness, invertibility on `S` of every
positive torsion order, finite-etaleness of the corresponding roots of unity,
and ordered-pair additivity for dual maps. This module supplies no proofs or
existence theorem for those inputs. The existing proved rational Weil
functoriality and geometric transport theorems are supplied internally by the
imported actual level-isogeny API.

The first constructions use field-valued points `s,t,r` of `S`, with finiteness
of the fibres of every finite-etale cover at each point. They require an
actual natural isomorphism `p : fiberFunctor s hs ≅ fiberFunctor t ht`.
Algebraic closedness, connectedness, and local Noetherianness are needed only
in the final canonical geometric comparison section. The level index is the
existing `FiniteAdelicScalarExtensionLevel D V ψ`.

## Construction and laws

`pointMapData p K` changes only the compatible fixed level orbit by the
existing `weilAdelicCompactOpenLevelTransport`; its first projection remains
the identical actual polarized object. The representative identity,
composition and path-independence laws follow from that actual transport by
dependent-pair extensionality. Path independence uses monodromy-fixed orbits;
it does not assert path independence for arbitrary frames.

`pointMapData_related` keeps the same rational unit, equivariant invertible
rational morphism, and dual-pullback multiplier equation witnessing the source
relation. The proved `weilAdelicLevelIsogeny_transport` square says that the
actual isogeny action on compatible orbits commutes with the actual path
transport. Applying this square to the source relation proves the target
relation. Thus `classPointMap` is a constructed quotient map, with its
definitional formula on `Quotient.mk` representatives. Quotient induction
proves its identity, composition and path-independence laws.

`classPointEquiv` uses transport along `p.symm` as its inverse. The two inverse
laws follow from the composition and identity laws. The theorem
`pointMapData_mapData` obtains commutation with every compact-open transporter
arrow from the actual Weil tower naturality law. Quotient descent assembles
these equivalences into `classPointTowerIso`. Its hom and inverse components
are the forward and reverse quotient maps. The natural isomorphism is
path-independent, respects identities and composition, and becomes its
inverse when the path is reversed. Naturality covers all existing transporter
arrows, including level inclusions and the existing Hecke legs whenever those
arrows are defined.

`forgetAction_classPointMap` shows that the underlying actual rational action
class is unchanged. The equality
`forgetActionNatTrans_classPointTowerIso` packages this as the commuting
forgetful square of whole towers, with the existing `ULift` for universes.

For a connected, locally Noetherian `S` and algebraically closed endpoint
fields, `classGeometricPointTowerIso` uses the proved
`geometricPathExists` and a choice of path. The path-independence theorem
proves equality with the isomorphism from every supplied path. The resulting
canonical comparisons satisfy identity, composition and reversal laws
without a chosen path appearing in those equations. Existence of a path is
proved by the imported finite-etale geometric-path theorem, not assumed as
new output data.

## Scope and provenance

This is a fixed-base, full-adelic construction. It does not construct a
varying-base unpointed polarized moduli presheaf or establish compatibility
with base-scheme pullback. It asserts no representability, scheme levels,
nonemptiness, finite-etale covering theorem, or coefficient descent. The
source dimension and positive Lie condition and original Harris level group
remain for specialization. The provenance is derived: retain actual objects,
use the proved path/isogeny square to descend the existing source-motivated
relation, and inherit tower laws by representative and quotient
extensionality. No arbitrary output schemes or class maps are supplied.
