# Galois actions with continuous orbits

This module defines continuity of a Galois action on a module over a
topological field without assuming that the module is finite-dimensional. It
proves that on a finite-dimensional space the condition makes the
representation continuous in the sense of the published
`Langlands.GaloisRepresentation.IsContinuous`. All declarations are in
namespace `Langlands.Shimura.ContinuousGaloisAction`. The module imports only
`Langlands.Shimura.ContinuousGaloisAction`, so generic work can use it without
the Shimura-variety geometry.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5, printed p. 313, considers `λ`-adic representations of
`Gal(F̄/F)`. These are continuous actions on finite-dimensional vector spaces
over a `λ`-adic field. Some spaces built from cohomology, such as the
`λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ` of a CM Shimura variety, are not
known to be finite-dimensional when they are defined. To state their
continuity before finiteness is known, we need a version of continuity that
does not use a topology on the endomorphism ring. This module provides one:
every orbit map `g ↦ g · x` is continuous. Here the space carries the module
topology over the topological coefficient field (Mathlib's
`moduleTopology`). For a finite-dimensional space this is the product
topology of `L^n` in any basis.

The module proves only the forward implication for finite-dimensional spaces.
The converse (continuity of the representation implies continuous orbits) is
not proved here.

## Definitions

Let `K` be a field, `L` a field with a topology and
`M : Action (ModuleCat L) (Field.absoluteGaloisGroup K)`, an `L`-linear action of
`Gal(K̄/K)`.

- `HasContinuousOrbits M : Prop`: when `M.V` carries
  `moduleTopology L M.V`, the map `g ↦ (M.ρ g).hom x` from
  `Field.absoluteGaloisGroup K` to `M.V` is continuous for every `x : M.V`.

## Results

- `isContinuous_finiteRepresentation_of_hasContinuousOrbits M hM`: if `L` is a
  topological ring and `M.V` is finite over `L`, then `HasContinuousOrbits M`
  implies `IsContinuous (finiteRepresentation M)`. Here `finiteRepresentation M`
  is the published finite-dimensional representation of
  `Langlands.Shimura.ContinuousGaloisAction`. `IsContinuous` refers to the
  module topology on `Module.End L M.V`.

## Proof outline

Choose a basis `b` of `M.V` over `L`, and let `e` be the linear equivalence
`LinearMap.toMatrix b b` from `Module.End L M.V` to square matrices over `L`.
Both sides carry their module topologies. The matrix space is a finite product
of copies of `L`, and its product topology is its module topology. Every
linear map between spaces with the module topology is continuous
(`IsModuleTopology.continuous_of_linearMap`), so `e.symm` is continuous. The
`(i, j)` entry of `e (M.ρ g)` is the `i`-th coordinate of `g · b j`. This is
the composition of the continuous orbit map of `b j` with the continuous
linear coordinate functional `b.coord i`. So `g ↦ e (M.ρ g)` is continuous
into the product, and the representation `g ↦ e.symm (e (M.ρ g))` is
continuous.

## Provenance

This is an internal formulation of the continuity that Harris (1999), §5,
printed p. 313, requires of `λ`-adic representations. Such a representation is
a continuous action on a finite-dimensional `λ`-adic vector space. By the
result above, the orbit condition implies this continuity in the finite-dimensional
case. Its use here is to state continuity of cohomology spaces before their
finite dimensionality is known. The finite-dimensional comparison is proved.
No statement of Harris is formalized.
