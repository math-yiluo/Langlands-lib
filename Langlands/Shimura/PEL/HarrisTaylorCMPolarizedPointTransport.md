# Point independence of the normalized CM polarized Harris tower

Author: Worker 57.

This derived construction restricts the existing actual polarized point
comparison to the normalized CM determinant-and-numerical class image. It
constructs an isomorphism of the original Harris class towers, proves its path
laws and compatibility with forgetting to joint CM action classes, and obtains
a canonical comparison at geometric points of a connected locally Noetherian
base. The namespace is `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Parameters and existing class image

All arithmetic types, endpoint fields and schemes have universe zero. The
arithmetic inputs are a totally real number field `E`, its quadratic CM number
field extension `F`, the central simple unitary datum `D` with algebra `A`, an
imaginary quadratic CM number field `L` mapping into `F`, a displayed embedding
`τ₀ : L →+* ℂ`, and charts `C` on exactly
`harrisCMSection E (algebraMap L F) τ₀`. The actual map `p : S ⟶ Spec F`
induces the single reflex structure `D.harrisTaylorReflexStructure C p`.
It uses the existing explicitly conjugated normalized reflex map, with its
inherited sign and positive auxiliary left involution. No independent reflex
structure is supplied.

The source and target are exactly `HarrisNumericalWeilLevel.isoClassTower` at
this CM section and induced reflex structure. Their index is the existing
`HarrisLevel D`, through `hodgeLevelFunctor D C`. Thus the original opposite
Harris finite-adelic group, compact-open transporters, subgroup forgetting and
Hecke legs remain in use.

There are two subtype layers over the actual polarized rational-isomorphism
quotient. The inner `HarrisIsoClass` imposes the determinant class condition
through the actual rational action class. The outer numerical image requires
one actual representative with both the positive determinant object condition
and the numerical object condition. The imported normalized CM comparison
identifies the latter image with one determinant-compatible representative of
geometric relative dimension `[E : ℚ] * n²`: the normalized determinant already
implies its full central trace. Dimension is still existential on a satisfying
representative, with no claim of invariance under every rational isomorphism.
The actual abelian schemes, polarizations, dual geometry, invertible rational
action morphisms and level-orbit relation are the existing ones.

The tensor comparison, composition, unit coherence, associativity, unitor
comparison and symmetry propositions, Picard-zero pullback, Mumford membership
and universal base-change propositions remain explicit. So do finite Weil
transition compatibility, the rational profinite-integer/finite-adele
comparison, torsion finite-etaleness, invertibility of every positive full-tower
order on `S`, finite-etaleness of the corresponding roots-of-unity schemes,
quasi-separatedness of `S` and positive ordered-pair dual additivity. None of
these propositions is proved here. No Lie base-change naturality input is
needed for this fixed-base construction.

## Supplied paths and restriction

Initially `s`, `t` and `r` are field-valued points, with finite fibres for every
finite-etale cover at the points used, and `path` is an actual isomorphism
`fiberFunctor s hs ≅ fiberFunctor t ht`. This portion requires neither
algebraic closedness of the fields nor connectedness or local Noetherianness
of `S`.

The existing `HarrisTaylorLieWeilLevel.pointMapRepresentative` changes only the
compatible monodromy-fixed level orbit and retains the identical actual
polarized object. Its `ambientPointTowerIso` supplies the existing actual
quotient comparison at every original Harris level. This module reuses both
constructions without replacing the raw quotient or its maps.

`determinantClassPointMap` restricts that ambient comparison through the inner
determinant subtype. The proof uses `forgetAction_classPointMap` to identify
the exact same underlying rational action class; the source determinant proof
therefore supplies the target proof. Its value and satisfying-representative
formulas are definitional.

`classCondition_pointMap` takes the one witness of the outer numerical image
and transports only its level orbit. The actual polarized object, determinant
proof and numerical proof remain the same. The equality with the target class
follows from the inner representative formula. `classPointMap` restricts the
map through this second subtype; its value and representative formulas are
also proved by reflexivity.

`classPointEquiv` uses the reversed path as inverse. Both inverse laws follow
by applying subtype extensionality twice and using the existing actual
polarized quotient inverse laws. `classPointTowerIso` assembles these
component equivalences into a natural isomorphism with values in `Type 1`.
Its naturality proof reduces through the two subtype layers to actual ambient
tower naturality for every original transporter.

The forward and reverse component formulas, independence from the supplied
path, identity, composition and reversal laws are proved. Double subtype
extensionality reduces the path laws to the imported actual quotient path
laws. Path independence ultimately uses monodromy-fixed level orbits; it
asserts no path independence for arbitrary frames.

`forgetCMAction_classPointMap` proves that the joint normalized CM action
class is unchanged. Its proof uses surjectivity of the existing satisfying-
representative constructor and computes on the identical polarized object.
`forgetCMActionNatTrans_classPointTowerIso` packages this as an equality of
natural transformations from the entire source Harris tower to the constant
joint action-class tower.

## Canonical geometric comparison and scope

For `[ConnectedSpace S]` and `[IsLocallyNoetherian S]`, with algebraically
closed endpoint fields, `classGeometricPointTowerIso` chooses a path using the
proved `geometricPathExists` and applies the constructed restricted tower
comparison. Finite endpoint fibres remain explicit arguments. Equality with
the comparison along every supplied path follows from path independence.
The resulting canonical comparisons satisfy identity, composition and
reversal laws without a chosen path in their statements. Their compatibility
with the joint CM action-class forgetful transformation is proved as well.

The provenance is internal: restrict already constructed actual point maps
through the existing two class-image subtypes using the same witness, inherit
laws by subtype extensionality, and use proved geometric path existence.
The inherited source context is Harris and Taylor, *The Geometry and Cohomology
of Some Simple Shimura Varieties* (2001), III.1, printed pp.89–91 / PDF
pp.97–99, especially the canonical point independence on p.91, registered as
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
The imported paired modules retain the original arithmetic and geometric
citations; this module makes no new identification of geometric isogenies
with all invertible rational morphisms.

This fixed-base result supplies neither compatibility with varying-base
pullback nor an unpointed polarized moduli functor. It asserts no universal
availability of the named geometric inputs, nonemptiness, representability,
scheme levels, canonical models or coefficient descent. Those constructions
remain obligations of the larger task.
