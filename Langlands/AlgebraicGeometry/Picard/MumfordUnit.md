# The unit equation for the actual Mumford map

This derived module constructs an actual rigidified trivialization of the
parameter-zero pullback of the Library's Mumford family. It also proves the
unit equation for the already constructed scheme map. All bases and all test
schemes are allowed, including nonreduced schemes. Quasi-separatedness is not
needed for this unit calculation.

## Inputs and constructions

Fix a base scheme `S`, an abelian scheme `A/S`, the canonical pullback-tensor
preservation proof `preservation`, a line bundle `L` rigidified at the unit,
an ordinary inverse `M`, and the specified module evaluation
`L ⊗ M ≅ O_A`. For each `T : Over S`, the point `1 : T ⟶ A.X` is the unit
section composed with the structure map of `T`.

`mumfordZeroParameterCarrierIso` trivializes the underlying module of
`relativePullback (1 : T ⟶ A.X)` applied to
`mumfordBundle A preservation L M evaluation`.
`mumfordZeroParameterIso` adjusts that trivialization to give an isomorphism
of the actual rigidified line bundles. Its target is the canonically
rigidified structure sheaf on `T ×_S A`, with section `(id_T,e_A)`.

The further lemmas `mumfordSchemeMap_zero` and `mumfordSchemeMap_unit` retain
exactly the explicit Picard-zero pullback stability, Mumford-family
Picard-zero, and universal-family existence inputs needed to use the
constructed classifier. The first says on every test scheme that zero maps
to the pullback of `dualOrigin`. The second is exactly the unit conjunct of
`MumfordSchemeMapHomomorphism`, including the canonical map from the chosen
monoidal terminal object to `Over.mk (identity S)`.

## Implemented proof

The helper `unitPoint_left` identifies the underlying zero-point morphism.
`mumfordZeroParameter_addition` proves that addition restricted along the
zero parameter is the second projection. It uses multiplication of actual
scheme-valued points in `Over S`, the first and second projection equations,
and the left unit law.

Write `h` for the map `T ×_S A → A ×_S A` induced by the zero parameter,
`p : T ×_S A → S` for the structure map, and `q : T ×_S A → A` for the
second projection. The ordinary module of the Mumford family is
`(m*L ⊗ p1*M) ⊗ p2*M`. Canonical pullback-tensor and composition comparisons
identify its pullback along `h` with
`(q*L ⊗ O_(T ×_S A)) ⊗ q*M`:

- `h ≫ m = q` identifies the first factor.
- `h ≫ p1 = p ≫ e_A` identifies the middle factor with `p*(e_A*M)`.
  `RigidifiedModule.inverseTrivialization` trivializes `e_A*M`, using precisely
  the supplied evaluation and the rigidification of `L`.
- `h ≫ p2 = q` identifies the last factor.

The right tensor unitor removes the middle factor. The inverse canonical
tensor comparison and the pullback of the supplied evaluation then produce
the ordinary trivialization. `RigidifiedLineBundle.trivialIsoOfCarrierIso`
adjusts it along the relative section to respect the actual rigidification;
it does not assume that an arbitrary ordinary isomorphism is already
compatible.

For the scheme equation, apply injectivity of `dualPointClass` on `T`.
`mumfordSchemeMap_points` identifies the first class with the zero-parameter
pullback just trivialized, and `dualPointClass_origin` identifies the second
with the trivial class. The rigidified isomorphism supplies equality in the
compatible-isomorphism quotient. Finally, `MonObj.one_eq_one` identifies the
unit morphism with the zero point of the monoidal terminal object.

## Provenance and limits

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision dated March 14, 2021, Construction 1.3.2.7, printed p.75
(PDF p.103), asserts that the Mumford classifier sends the unit to the dual
unit. Registered source: `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
Lan uses the second factor as parameter; the Library fixes the first factor.
The proof here is an internal tensor calculation for that fixed convention,
and works without a quasi-separatedness assumption.

The March 14, 2021 errata were read at PDF pp.1 and 8–9, including the
quasi-separated scheme convention and corrections to the rigidity argument.
Registered errata: `lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`.
The proof uses neither that rigidity argument nor any geometry of the dual.
It establishes no multiplication equation, no representability theorem,
and no Mumford Picard-zero theorem. Those remain distinct obligations.
