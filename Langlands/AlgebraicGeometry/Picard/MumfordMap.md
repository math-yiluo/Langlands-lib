# The scheme morphism classifying the Mumford family

`Langlands.AbelianScheme.mumfordSchemeMap` constructs the scheme morphism
associated to the actual rigidified Mumford family:

`A.X ⟶ dualScheme A hA`

in `Over S`. It uses the universal property of the chosen Poincare
family. The morphism is not supplied as an input.

## Inputs and construction

The base `S` is any scheme and `A` is an abelian scheme over it.
The arguments retain the explicit inputs of `mumfordBundle`: a proof
of `pullbackTensorComparisonIsIsoStatement`, a rigidified line bundle
`L` on `A`, an ordinary inverse line bundle `M`, and an actual
evaluation isomorphism `L tensor M ≅ O_A`.
There are two additional proposition proofs:

- `square : MumfordBundlePicardZeroStatement.{u}` supplies the exact
  theorem-of-the-square consequence for this constructed family.
- `hA : HasDualScheme A` supplies existence of a parameter scheme
  with an actual universal rigidified Picard-zero family on all test
  schemes over `S`.

`mumfordPicardZeroClass` takes the compatible-isomorphism class of
`mumfordBundle A preservation L M evaluation` and equips it with the
Picard-zero condition obtained by specializing `square`.
`mumfordSchemeMap` applies `dualClassify` to this actual class at the
parameter scheme `A.X`. The chosen map is the unique witness to the
universal property, not a choice from an unconstrained collection of
morphisms.

The underlying Mumford bundle is
`(m*L tensor p1*M) tensor p2*M`, rigidified along `(id,e)` in the
parameter-first convention. This is the positive-translation convention
for the associated morphism: over a field the underlying fibre class
is represented by `t_a*L tensor L⁻¹`.
The module proves the classification of the actual parameter pullback;
it does not implement a separate translation-formula comparison.

## Implemented properties

`mumfordSchemeMap_spec` specializes `dualClassify_spec` and proves that
pulling back the Poincare family along the constructed map gives
exactly the compatible-isomorphism class of the Mumford bundle.

`mumfordSchemeMapPullbackIso` uses `dualClassifyPullbackIso` to exhibit
an actual isomorphism of rigidified line bundles between this
Poincare pullback and the constructed family.

`mumfordSchemeMap_unique` turns any such rigidified isomorphism for a
candidate map into equality of compatible-isomorphism classes and
applies `dualClassify_unique`. It proves uniqueness of the scheme
morphism, without asserting uniqueness of line-bundle isomorphisms.

`mumfordSchemeMap_points` holds for every test scheme `T/S` and
`a : T ⟶ A.X`, including nonreduced tests. It proves that
`a ≫ mumfordSchemeMap` classifies the actual rigidified parameter
pullback of the Mumford bundle along `a`.
The proof combines the already proved rigidified pullback composition
coherence with `mumfordSchemeMap_spec`; the remaining class equality
is definitional.

## Source and scope

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision dated March 14, 2021, Construction 1.3.2.7, printed p.75
(PDF p.103), applies the universal property of the dual to `D₂(L)`
to obtain the associated morphism. Registered source:
`lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The author's errata dated March 14, 2021, registered
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9 in this development.

This implementation is the formal universal-property step of that
construction, with the Library's first-coordinate parameter convention.
Its arbitrary-base scope is conditional on the explicit actual
representability and Picard-zero proofs. It does not prove a
representability theorem over a broader base than the source.

The result is presently a scheme morphism over `S`. The unit and
group-law identities, abelian-scheme geometry of the dual, inverse
existence, and Picard-zero membership itself are not proved here.
In particular no unproved group-homomorphism structure is bundled into
the definition. An arbitrary ordinary line bundle must first be
normalized as in `LineBundleNormalization` before being supplied as
the rigidified argument.
