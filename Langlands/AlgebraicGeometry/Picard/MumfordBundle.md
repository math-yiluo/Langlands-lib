# The rigidified Mumford bundle

`Langlands.AbelianScheme.mumfordBundle` constructs the actual Mumford line
bundle on the self-product of an abelian scheme over any base scheme.
The family is parameter-first: its projection is
`p1 : A ×_S A → A`, with section `j = (id,e)`. Its underlying bundle is

`(m*L tensor p1*M) tensor p2*M`,

where `m` is addition, `L` is rigidified along the unit section, and `M`
is a supplied inverse with a supplied evaluation isomorphism
`L tensor M ≅ O_A`. The resulting object belongs to the existing
category `RigidifiedFamily A A.X`. In particular its carrier is an
actual locally free rank-one module sheaf and its rigidification is an
actual isomorphism `O_A ≅ j*Λ(L)`.

## Inputs and scope

The arguments are an arbitrary `S : Scheme.{u}`, `A : AbelianScheme S`,
a proof of `pullbackTensorComparisonIsIsoStatement.{u}`, a
`RigidifiedLineBundle (unitSection A)`, an ordinary `LineBundle A.X.left`,
and the displayed evaluation between their module sheaves.
The comparison proof makes the canonical pullback-tensor maps invertible;
it is not an arbitrary tensor operation or an assumed final rigidification.
The line bundle `M` and evaluation remain explicit inputs. This module
does not prove that every line bundle has an inverse.

No quasi-separatedness, dual representability, Picard-zero membership,
or theorem of the square is needed for this construction. In particular,
the module does not yet assert `IsPicardZeroFamily` for the result,
construct its classifying morphism, or prove additivity of that morphism.
An ordinary unrigidified bundle can first be treated by the separate
`LineBundle.normalize` construction, with its own inverse and evaluation
inputs, before supplying the normalized bundle here.

## Geometry and implemented rigidification

`mumfordProduct` is the actual chosen pullback of `A.X.hom` with itself,
equipped with its structure map to `S`. `mumfordFirst` and
`mumfordSecond` are its two projections in `Over S`.
`mumfordAddition` is the underlying scheme morphism of their product
in the group of `A`-valued points. Thus it uses the existing group law
on `A`, rather than receiving an addition morphism as extra data.

`mumfordSection` is the existing relative section at the test scheme
`A.X`; `mumfordSectionOver` views it as a morphism in `Over S`.
The first projection of this section is the identity. Its second
projection is the constant identity point, obtained by restricting the
unit section along `A.X.hom`. These equations are proved by the
pullback projection identities and the terminal-object identity.
`mumfordSection_addition` then proves `j ≫ m = id` by distribution of
precomposition over the pointwise group law and the right-unit law.

The rigidification is built in two steps:

1. `mumfordAdditionRestrictionIso` uses pullback composition, the
   just-proved section equation, and identity pullback to identify
   `j*m*L` with `L`. Tensoring this isomorphism with the identity of `M`
   and composing with the supplied evaluation gives
   `j*m*L tensor M ≅ O_A`. `mumfordFirstFactor` applies
   `LineBundle.normalize` to the morphism `p1`, its section `j`, the
   bundle `m*L`, and this evaluation. It constructs
   `m*L tensor p1*M` with its rigidification.
2. `RigidifiedLineBundle.rigidifyInverse` gives `M` its
   evaluation-induced rigidification along `e`. Pullback along the
   commuting square `j ≫ p2 = A.X.hom ≫ e` gives a rigidified `p2*M`
   in the same family. `mumfordBundle` tensors it with the first factor
   using the existing rigidified tensor construction.

`mumfordBundle_forget` proves by reflexivity that forgetting the
rigidification yields exactly the parenthesized three-factor formula.
The local rank-one proofs come from actual pullback and tensor of line
bundles. All rigidification data are constructed by these operations.

## Original source and derived provenance

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
thesis revision dated March 14, 2021, Construction 1.3.2.7, printed p.75
(PDF p.103), defines `D₂(L)` by the same three-factor formula for a
rigidified invertible sheaf and equips it with rigidification along
`(e,id)` when the second coordinate is the parameter.
The registered source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
The author's errata dated March 14, 2021, registered
`lan-2008-pel-thesis-errata-2021`, SHA-256
`18e66df9fefa6c3d6c2ee799ec8d5c208263a22a51847032d85ccbeb6947861d`,
were checked at pp.1 and 8–9 in this development.

The Library uses the first coordinate as parameter, so its section is
`(id,e)`. Exchanging the coordinates in the source formula preserves
addition since the abelian scheme is commutative and exchanges the two
inverse factors, which can be reordered by tensor symmetry.
This explains the convention; this module does not provide a separate
coordinate-exchange isomorphism theorem.

The implementation is derived from the explicit formula and the section
identities. It supplies the rigidification by pullback, evaluation and
tensor isomorphisms, without invoking the deeper classification and
homomorphism assertions that follow the formula in Lan.
Lan's general quasi-separatedness convention is unnecessary for these
explicit operations, so no relative representability theorem is being
extended beyond its source hypotheses.
