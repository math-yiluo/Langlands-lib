# Restriction of Galois actions to decomposition groups

This internal construction restricts objects of a category with an action of
the absolute Galois group `Gal(K̄/K)` of a field `K` to the absolute Galois
group of an extension `E`, along a specified embedding of algebraic closures.
Two embeddings give restrictions that are naturally isomorphic through the
action of the element of `Gal(K̄/K)` relating them. At a finite place `v` of
a number field `K` this gives the restriction to the absolute Galois group of
the actual completion `K_v`, the decomposition group at `v`. Unramifiedness is
the triviality of the action of the actual inertia subgroup and does not
depend on the embedding. For unramified actions every geometric Frobenius
lift acts by one endomorphism. All declarations are in namespace
`Langlands.Shimura.DecompositionGroupAction`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, describes the action of the
decomposition group `Gal(F̄_w/F_w)` at a place `w` on a Galois-stable part
of the cohomology of a Shimura variety. Part (ii) of that theorem and
formula (5.6) use the action of a geometric Frobenius at almost all
unramified places. The cohomology constructed in the Library carries
actions of `Gal(K̄/K)` as objects of Mathlib's `Action V Gal(K̄/K)` for
categories `V` of smooth representations or Hecke modules. This module
provides the decomposition group restriction and the Frobenius
endomorphisms for such objects, for any category `V`.

The published `Langlands.GaloisRepresentation.IsUnramifiedAt` and
`Langlands.GaloisRepresentation.action_eq_of_residueAction_eq` of
`Langlands.Galois.CompatibleFamily` treat finite-dimensional
representations. The declarations here are their analogues for `Action`
categories, with the closure embedding specified. No topology on the Galois
groups and no continuity of actions is considered. No statement of Harris
is formalized.

## Inputs

Let `V` be a category. Mathlib provides `Action V G`, the restriction
functor `Action.res V f` along a monoid homomorphism `f`, `Action.mkIso`,
the automorphism `M.ρAut c` of an action, and `Functor.mapAction`.

The published module `Langlands.Galois.ClosureRestriction` provides, for
fields `K → E` and `ι : AlgebraicClosure K →ₐ[K] AlgebraicClosure E`, the
continuous restriction homomorphism `restrictionAlongClosure ι` from
`Field.absoluteGaloisGroup E` to `Field.absoluteGaloisGroup K` with
`restrictionAlongClosure_commutes`, and for two embeddings `ι κ` the element
`closureChange ι κ` of `Field.absoluteGaloisGroup K` with
`closureChange_intertwines`. For a field homomorphism `f` it provides
`ClosureEmbedding f`, the `K`-algebra maps of algebraic closures for the
algebra structure of `f`, and Mathlib's selected lift
`chosenClosureEmbedding f`.

The published module `Langlands.Galois.CompatibleFamily` provides, for a
finite place `v` of a number field `K`, `LocalGroup v`, the absolute Galois
group of the actual completion `Global.FiniteCompletion K v`; the reduction
`localResidueAction v` to automorphisms of the residue field of the
algebraic closure; the actual inertia subgroup `localInertia v`, its kernel;
the predicate `IsGeometricFrobeniusLift v g`; and
`residueAction_eq_of_geometricFrobenius`. The published module
`Langlands.Galois.FrobeniusLift` provides the chosen lift
`geometricFrobeniusLift v` with `geometricFrobeniusLift_spec`.

## Conjugate restrictions

Let `H` be a monoid and `G` a group.

- `resConjugateIso V f₁ f₂ c hc`: for `f₁ f₂ : H →* G` and `c : G` with
  `hc : ∀ h, c * f₂ h = f₁ h * c`, the natural isomorphism
  `Action.res V f₂ ≅ Action.res V f₁` whose component at `M` is the action of
  `c`. `resConjugateIso_hom_app_hom` and `resConjugateIso_inv_app_hom` state
  that the components act by `M.ρ c` and `M.ρ c⁻¹`, by `rfl`.
- `ρ_eq_id_iff_of_conj M h`: if `c * b = a * c`, then `a` acts trivially on
  `M` if and only if `b` does, since the kernel of `M.ρ` is normal.
- `mapActionResIso V F f`: for a functor `F : V ⥤ W`, mapping actions
  through `F` commutes with restriction along `f`; the components are
  identities (`mapActionResIso_hom_app_hom`).

## Restriction along an embedding of algebraic closures

Let `K → E` be fields and `ι κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure E`.

- `alongClosure V ι` is `Action.res V` along `restrictionAlongClosure ι`, a
  functor from `Action V (Field.absoluteGaloisGroup K)` to
  `Action V (Field.absoluteGaloisGroup E)`. `alongClosure_obj_V`,
  `alongClosure_obj_ρ` and `alongClosure_map_hom` state by `rfl` that it
  keeps underlying objects and morphisms, and that `g` acts as
  `restrictionAlongClosure ι g`.
- `alongClosureChangeIso V ι κ : alongClosure V κ ≅ alongClosure V ι` is
  `resConjugateIso` for `closureChange ι κ` and `closureChange_intertwines`.
  Its components act by `M.ρ (closureChange ι κ)` and its inverse by
  `M.ρ (closureChange ι κ)⁻¹`.

## Decomposition groups at finite places

Let `K` be a number field, `v` a finite place of `K` and
`ι κ : ClosureEmbedding (NumberField.FinitePlace.embedding v)`, using the
algebra structure on the completion given by its embedding.

- `localRestriction v ι : LocalGroup v →* Field.absoluteGaloisGroup K` is
  `restrictionAlongClosure ι`. `localRestriction_commutes` states that
  `ι ((localRestriction v ι g) x) = g (ι x)`, and
  `localRestriction_chosen_apply` that for `chosenClosureEmbedding` it is the
  published `Field.absoluteGaloisGroup.map` of the embedding, by `rfl`.
- `localClosureChange v ι κ` is `closureChange ι κ`, and
  `localClosureChange_intertwines` is `closureChange_intertwines`.
- `atFinitePlace V v ι` is `Action.res V (localRestriction v ι)`, a functor
  from `Action V (Field.absoluteGaloisGroup K)` to `Action V (LocalGroup v)`.
  `atFinitePlace_obj_V`, `atFinitePlace_obj_ρ` and `atFinitePlace_map_hom`
  describe it by `rfl`, and `atFinitePlace_eq_alongClosure` states that it
  is `alongClosure V ι`, by `rfl`.
- `atFinitePlaceChangeIso V v ι κ : atFinitePlace V v κ ≅ atFinitePlace V v ι`
  is `resConjugateIso` for `localClosureChange v ι κ`; its components act by
  `M.ρ (localClosureChange v ι κ)` (`atFinitePlaceChangeIso_hom_app_hom`).

## Unramified actions and Frobenius

- `IsUnramifiedAlong V v M ι` holds if every element of `localInertia v` acts
  by the identity on `(atFinitePlace V v ι).obj M`.
- `IsUnramifiedAt V v M` is `IsUnramifiedAlong` for
  `chosenClosureEmbedding`.
- `isUnramifiedAlong_iff M ι κ`: `IsUnramifiedAlong` does not depend on the
  embedding. It is `ρ_eq_id_iff_of_conj` with
  `localClosureChange_intertwines`. `isUnramifiedAt_iff_along M ι` follows.
- `IsUnramifiedAlong.of_iso e hM`: unramifiedness transfers along an
  isomorphism `e : M ≅ N` of actions, using that `e.inv` commutes with the
  actions.
- `IsUnramifiedAlong.ρ_eq_of_residueAction_eq hM hres`: if `M` is
  unramified along `ι` and `localResidueAction v g = localResidueAction v h`,
  then `g` and `h` act by the same endomorphism, because `g * h⁻¹` lies in
  `localInertia v`. This is the argument of the published
  `action_eq_of_residueAction_eq`.
- `geometricFrobenius V v M ι : M.V ⟶ M.V` is the action of
  `geometricFrobeniusLift v` on `(atFinitePlace V v ι).obj M`.
- `geometricFrobenius_eq_of_lift hM hg`: if `M` is unramified along `ι` and
  `g` satisfies `IsGeometricFrobeniusLift v g`, then `g` acts by
  `geometricFrobenius V v M ι`. It combines `ρ_eq_of_residueAction_eq` with
  `residueAction_eq_of_geometricFrobenius` and `geometricFrobeniusLift_spec`.
- `geometricFrobenius_naturality p ι`: a morphism `p : M ⟶ N` of actions
  intertwines the Frobenius endomorphisms.
- `geometricFrobenius_conj M ι κ`: the Frobenius endomorphisms along `κ`
  and `ι` are conjugate by `M.ρ (localClosureChange v ι κ)`. It is the
  commutativity of the component of `atFinitePlaceChangeIso` at the chosen
  Frobenius lift.

## Proof outline

The restrictions are Mathlib's `Action.res`; the change-of-embedding
isomorphisms are built with `NatIso.ofComponents` and `Action.mkIso` from
the intertwining identity of the published `closureChange`. The
unramifiedness and Frobenius results are computations with the monoid
homomorphism `M.ρ`, its normal kernel and the commutativity squares of
morphisms of actions.

## Provenance

This is an internal construction. It transfers the published
finite-dimensional notions of `Langlands.Galois.CompatibleFamily` and
`Langlands.Galois.ClosureRestriction` to objects of `Action` categories.
Harris (1999), Theorem 5.7 and formula (5.6) on printed p. 313, is
motivation only.
