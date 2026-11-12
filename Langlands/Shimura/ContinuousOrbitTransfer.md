# Transfer of continuous orbits and unramifiedness along equivariant linear maps

This module proves that two properties of a Galois action pass along
equivariant linear maps. The first is continuity of the orbit maps,
`HasContinuousOrbits` from `Langlands.Shimura.ContinuousOrbitGaloisAction`. The
second is unramifiedness at a finite place along a closure embedding,
`IsUnramifiedAlong` from `Langlands.Shimura.DecompositionGroupAction`. All
declarations are in namespace `Langlands.Shimura.ContinuousGaloisAction`.

## Motivation and scope

The `λ`-adic cohomology of a Shimura variety carries a Galois action that is
continuous for the `λ`-adic topology but not smooth. The spaces built from it
(fixed vectors after extension of scalars, isotypic parts, multiplicity spaces
of Hecke-linear or intertwining maps) are related to it by equivariant linear
maps, not by isomorphisms. The lemmas below move continuity and unramifiedness
along such maps, so that the Galois representations on these spaces can be
built from properties of the cohomology. Continuity is stated with plain linear
maps and an equivariance hypothesis, so source and target may live in different
universes.

## Setting

`F` is a field and `Γ = Field.absoluteGaloisGroup F`. `L` is a field, with a
topology where continuity is involved. `A` and `B` are objects of
`Action (ModuleCat L) Γ`, possibly in different universes. A linear map
`f : A.V →ₗ[L] B.V` is *equivariant* if `f (g · x) = g · f x` for all `g` and
`x`. A family `f : J → (A.V →ₗ[L] B.V)` is *jointly injective* if `x = 0`
whenever `f j x = 0` for all `j`. In the unramified section `F` is a number field,
`L` is a commutative ring, `v` is a finite place of `F`, and `ι` is a closure
embedding at `v`.

## Results

### Continuous orbits

- `hasContinuousOrbits_of_surjective f hf hsurj hA`: if `A` has continuous orbits
  and `f : A.V → B.V` is a surjective equivariant linear map, then `B` has
  continuous orbits.
- `exists_finset_forall_eq_zero f hinj`: if `A.V` is finite over `L` (here `L` is
  only a field), a jointly injective family `f : J → (A.V →ₗ[L] B.V)` has a
  finite jointly injective subfamily indexed by a `Finset J`. Equivariance is not
  needed.
- `hasContinuousOrbits_of_forall_eq_zero f hf hinj hB`: if `A.V` is finite over
  `L`, `B` has continuous orbits, and `f` is a jointly injective family of
  equivariant linear maps, then `A` has continuous orbits.
- `hasContinuousOrbits_of_injective f hf hinj hB`: the special case of one
  injective equivariant linear map.
- `hasContinuousOrbits_baseChangeAction hKL hA`: let `K` and `L` be topological
  fields with `Algebra K L` and `algebraMap K L` continuous. If an action `A` over
  `K` has continuous orbits, so does its extension of scalars
  `LatticeGaloisRepresentation.baseChangeAction (L := L) A` on `L ⊗[K] A.V`.

### Unramifiedness

- `isUnramifiedAlong_of_surjective f hf hsurj hA`: if `A` is unramified at `v`
  along `ι` and `f` is a surjective equivariant linear map, then `B` is
  unramified at `v` along `ι`.
- `isUnramifiedAlong_of_forall_eq_zero f hf hinj hB`: if `B` is unramified at `v`
  along `ι` and `f` is a jointly injective family of equivariant linear maps,
  then `A` is unramified at `v` along `ι`. No finiteness is needed.
- `isUnramifiedAlong_of_injective f hf hinj hB`: the special case of one
  injective equivariant linear map.

## Proof outline

All topologies are module topologies, and every linear map between modules
with their module topologies is continuous
(`IsModuleTopology.continuous_of_linearMap`).

- Surjective maps: write `y = f x`. By equivariance, the orbit map of `y` is
  `f` composed with the orbit map of `x`.
- Finite subfamily: `A.V` is Artinian, so among the finite intersections of
  kernels `⋂_{j ∈ s} ker (f j)` there is a minimal one
  (`IsArtinian.set_has_minimal`). Adding one more index `j` cannot make it
  smaller, so it lies in `ker (f j)` for every `j`. By joint injectivity it is
  zero.
- Jointly injective families: take a finite jointly injective subfamily `s`.
  The map `E : A.V → (s → B.V)`, `x ↦ (f j x)_j`, is injective, so it has a
  linear left inverse `r` (`LinearMap.exists_leftInverse_of_injective`). By
  equivariance, the orbit map of `x` is `r` composed with the product of the
  orbit maps of the `f j x`. This product is continuous into the finite product,
  whose topology is the module topology.
- Extension of scalars: by induction on tensors. The orbit map of `c ⊗ x` is the
  orbit map of `x` followed by `y ↦ c ⊗ y`. This map is semilinear along the
  continuous `algebraMap K L`, hence continuous
  (`IsModuleTopology.continuous_of_linearMapₛₗ`). The orbit map of a sum is the
  sum of the orbit maps, and addition is continuous.
- Unramifiedness: an inertia element `g` fixes `f x` because it fixes `x` and
  `f` is equivariant. For a jointly injective family, `g · x - x` is killed by
  every `f j`, because `f j (g · x) = g · f j x = f j x`.

## Provenance

These are standard facts of linear algebra and topology. They are formulated
here for use with the `λ`-adic Galois representations of Harris (1999), *Galois
properties of cohomological automorphic forms on GL(n)*, §5, printed p. 313,
which are continuous and unramified at all but finitely many places. No
statement of Harris is formalized in this module.
