# Base change of morphisms of Deligne's four sheaf data

This module constructs pullback of actual morphisms and isomorphisms of
the preliminary `eta,T,u,r` data. It is derived infrastructure for
Drinfeld, *Coverings of p-adic Symmetric Regions* (1976), Section 2 A,
printed p.109 (PDF p.3), final paragraph, continuing on printed p.110
(PDF p.4). Proposition 2.4 on printed p.110 concerns compatibility with
data attached to special formal modules; that comparison is not asserted
here. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.

All declarations are in `Langlands.DeligneFormalSpace`. Fix a commutative
ring `O`, a positive integer `d`, an element `pi : O`, and an `O`-algebra
field `F`. Lattice inverse image uses an arbitrary continuous map
`f : X -> Y`. The four-data construction uses an arbitrary scheme map
`f : S' -> S` and a homomorphism `phi : O -> Gamma(S,top)`.
Flatness of `f`, nilpotence of `pi`, and local-field hypotheses are not
required. Thus this construction also applies to the schemes in the
intended Nilp setting.

## Graded and framed lattice morphisms

`inverseImageLatticeScalarIso_naturality` and its `inv` version give the
two naturality squares of the actual comparison between ordinary inverse
image and restriction from `O[Pi]` to `O`.

`LatticePiSheaf.inverseImageMap` applies ordinary inverse image to the
actual coefficient-linear total map and the maps of homogeneous
components. The original inclusion square and naturality of that scalar
comparison prove the pulled inclusion square. Its source and target are
the previously constructed actual inverse-image flat graded lattices.
`inverseImageFunctor` proves the identity and composition laws by the
corresponding laws of coefficient-sheaf inverse image and
`Hom.ext_total`. Hence all component maps, including the degree-one
operator compatibility already derived for lattice morphisms, belong to
the same actual total map.

`FramedLatticePiSheaf.inverseImageMap` uses this lattice map. Each pulled
frame is the composite of the inverse constant-sheaf comparison,
inverse image of the original frame, and the rationalization comparison.
Naturality of the latter comparison and the original frame square give
the new frame square. This retains the full given rational frame in
degree zero. `inverseImageFunctor` obtains its identity and composition
laws from the lattice functor and the extensionality of framed morphisms.

## Structural tangent morphisms

`GradedPiSheaf.pullbackMap` applies actual structural pullback to the total
module-sheaf map. Functoriality carries its Pi square to the pulled Pi
square. A section in a pulled homogeneous component is, by construction,
in the actual sectionwise range of the pulled inclusion. The image of a
range witness under the pulled original homogeneous map witnesses that
the total pulled map lands in the corresponding target range. The
original component-inclusion square, mapped by structural pullback,
proves this equality. Homogeneity is therefore proved for the actual
range subsheaves used in the object construction.

`GradedPiSheaf.pullbackFunctor` proves the identity and composition laws
using structural pullback and extensionality first for graded morphisms
and then for Pi-sheaf morphisms. In particular the pulled tangent maps
preserve both the actual grading and the distinguished operator, and
therefore their induced coefficient-quotient actions.

## All four data and their preliminary isomorphism classes

`SheafPreDatum.pullbackMap_u` proves the square with the actual
`pullbackU` of the object construction. Naturality of the inverse lattice
scalar comparison moves the lattice map past that inverse. Functoriality
of ordinary inverse image then permits the original total `u` square to
be used. Naturality of `structuralPullbackComparison` moves the pulled
tangent map past the canonical ordinary-to-structural comparison. The
result is exactly the required square for the constructed pulled `u`.
No assertion that this canonical comparison is an isomorphism is used.

`SheafPreDatum.pullbackMap` assembles the pulled framed lattice map,
graded structural tangent map, and this total `u` square.
The existing `Hom.uComponent_naturality` applies to this actual morphism,
so its homogeneous maps also preserve the restrictions of `u` into the
constructed range components.
`SheafPreDatum.pullbackFunctor` has the previously constructed
`D.pullback f` as its object map, with global scalars
`pulledGlobalScalar f phi`. Its identity and composition laws follow
from the framed-lattice and graded-tangent functors and extensionality
of four-data morphisms.

`SheafPreDatum.pullbackIso` is the image of a genuine categorical
isomorphism under this functor, including its inverse and both inverse
equations. `SheafPreDatum.IsoClass.pullback` descends the actual object map
to preliminary isomorphism classes using this construction.
`pullback_mk` records its value on a represented class.

These are functors on data for each fixed base map, and well-defined maps
on preliminary isomorphism classes. Compatibility between different base
maps, the identity-base and composite-base isomorphisms, transport of
admissibility conditions (a)–(c), and the admissible Nilp point functor
remain open. So do the integral determinant comparison, the normalized
PGL action, the comparison with special formal modules, representability,
and a generic fibre. No representing or universal object is an input.
