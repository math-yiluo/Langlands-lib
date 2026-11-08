# Hecke multiplicity spaces of fixed vectors as continuous Galois representations

This internal construction defines Hecke multiplicity spaces of smooth
representations with a commuting group action and makes them into
continuous Galois representations. Let `X` be a smooth representation of a
group `G` with a commuting action of a group `Γ`, let `H` be a subgroup of
`G`, and let `T` be a module over the Hecke algebra `LevelHeckeAlgebra R H`
of `H`. The Hecke multiplicity space `Hom_{H(H)}(T, X^H)` consists of the
Hecke-linear maps from `T` to the `H`-fixed vectors of `X`. It is a module
over the coefficient ring `R`, and `Γ` acts on it by composition. Suppose
that `Γ` is a topological group acting smoothly on `X`, meaning that every
vector is fixed by an open subgroup of `Γ`, and that `T` is finitely
generated over the Hecke algebra. Then the action on the multiplicity space
is smooth. For `Γ = Gal(K̄/K)` and a multiplicity space that is
finite-dimensional over a topological field `L`, it is therefore an object of
`Langlands.GaloisRepresentation.Objects K L`. At a finite place `v` of a
number field `K` where the `H`-fixed vectors are unramified, its Euler
polynomial is the reversed characteristic polynomial of composition with
the Hecke-linear Frobenius endomorphism of the fixed vectors. The
declarations are in namespace
`Langlands.Shimura.HeckeMultiplicityGaloisRepresentation`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, printed p. 312, writes `H^{n-1}(S_K(N), W)[π]` for the
`JL(π_f)`-isotypic component of the cohomology at the level `K(N)`. Theorem
5.7 on printed p. 313 describes the Galois representation on it, and part
(ii) characterizes it by its Frobenius characteristic polynomials at almost
all unramified places, through formula (5.6). At a fixed level, the
cohomology is a module over the Hecke algebra of the level, and the vectors
of `JL(π_f)` fixed by the level form a module over the same algebra.
Formulas (5.2), (5.3) and (5.5) on printed pp. 312-313 use spaces of
intertwining maps of representations. This module provides the Hecke-module
form of such spaces of intertwining maps. For an arbitrary module `T` over
the Hecke algebra, it gives the space of Hecke-linear maps into the fixed
vectors, with its Galois action, as a continuous Galois representation with
Euler polynomials.

The Hecke algebra need not be commutative; `T` is an arbitrary module over
it. Smoothness of the action on `X`, finite generation of `T`, finite
dimension of the multiplicity space and unramifiedness of the fixed vectors
are hypotheses. No irreducibility of `T` and no relation between `T` and an
automorphic representation is assumed or proved. No statement of Harris is
formalized.

## Inputs

- The published `Langlands.fixedVectors ρ H`, the `H`-fixed vectors, with
  `fixedVectorsMap`.
- From the published `Langlands.Shimura.LevelHeckeAlgebra`:
  `LevelHecke.LevelHeckeAlgebra R H`, an `R`-algebra, acting on
  `fixedVectors ρ H` compatibly with `R` (`IsScalarTower`), and
  `LevelHecke.fixedVectorsMap_heckeAct`, which says that intertwiners commute
  with the Hecke action.
- From the published `Langlands.Shimura.LevelHeckeAction`:
  `LevelHecke.fixedVectorsActionFunctor`.
- From `Langlands.Shimura.IsotypicGaloisAction` (candidate
  `06482d9c-709f-449e-bd42-538102e24d51`, accepted and awaiting
  publication): `galoisRepresentation X`.
- From `Langlands.Shimura.ContinuousGaloisAction` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication): `toObjects`, `hasEulerPolynomialAt_toObjects_iff` and
  `hasEulerPolynomialAt_toObjects_iff_along`. From
  `Langlands.Shimura.FrobeniusPolynomial` (same candidate):
  `frobeniusEulerPolynomial`.
- From `Langlands.Shimura.FixedVectorGaloisRepresentation` (candidate
  `7a622629-80be-4029-b7ca-0e6bc08e7a87`, accepted and awaiting
  publication): `heckeFrobenius H X v ι`, the geometric Frobenius
  endomorphism of the Hecke module of `H`-fixed vectors as a Hecke-linear
  map.
- From the published `Langlands.Shimura.DecompositionGroupAction`:
  `IsUnramifiedAt`, `IsUnramifiedAlong` and `geometricFrobenius`.

## Hecke multiplicity spaces

Let `R` be a commutative ring, `G` a group with a topology, `H` a subgroup
of `G` and `T` a module over `LevelHeckeAlgebra R H`.

- `fixedVectorsHeckeMap H f`: for a morphism `f : A ⟶ B` of smooth
  representations, `fixedVectorsMap (SmoothRep.hom f) H` as a Hecke-linear
  map between the `H`-fixed vectors. `coe_fixedVectorsHeckeMap_apply` gives
  its underlying vector.
- `heckeMultiplicityFunctor H T : SmoothRep R G ⥤ ModuleCat R` sends `A` to
  `T →ₗ[LevelHeckeAlgebra R H] fixedVectors A.representation H`. The
  `R`-module structure comes from the `R`-module structure of the fixed
  vectors, which commutes with the Hecke action. A morphism `f` acts by
  composition with `fixedVectorsHeckeMap H f`
  (`heckeMultiplicityFunctor_map_apply`).
- `heckeMultiplicityActionFunctor H T Γ` is
  `(heckeMultiplicityFunctor H T).mapAction Γ`, from
  `Action (SmoothRep R G) Γ` to `Action (ModuleCat R) Γ`.
- `heckeMultiplicityRepresentation H T Γ X` is the associated linear
  representation of `Γ`. By `heckeMultiplicityRepresentation_apply`, `γ`
  sends `φ` to `(fixedVectorsHeckeMap H (X.ρ γ)).comp φ`.
- `isSmooth_heckeMultiplicityRepresentation H T hX`: if `Γ` has a topology,
  `T` is finitely generated over `LevelHeckeAlgebra R H`, and
  `galoisRepresentation X` is smooth, then
  `heckeMultiplicityRepresentation H T Γ X` is smooth.

## Continuous Galois representations

Let `K` and `L` be fields, `T` a module over `LevelHeckeAlgebra L H` and
`X : Action (SmoothRep L G) (Field.absoluteGaloisGroup K)`.

- An instance: if the multiplicity space is finite-dimensional over `L`, so
  is the space of `(heckeMultiplicityActionFunctor H T _).obj X`.

Assume now that `T` is finitely generated over the Hecke algebra, that the
multiplicity space is finite-dimensional over `L`, that `L` has a topology,
and let `hX` be a proof that `galoisRepresentation X` is smooth.

- `heckeMultiplicityObjects H T X hX : Objects K L` is
  `ContinuousGaloisAction.toObjects` of the multiplicity action, with the
  smoothness given by `isSmooth_heckeMultiplicityRepresentation`.
- `heckeMultiplicityObjects_representation_apply`: `g` sends `φ` to
  `(fixedVectorsHeckeMap H (X.ρ g)).comp φ`.
- `heckeMultiplicityObjects_rank`: the rank is the dimension of the
  multiplicity space over `L`.

Let `K` be a number field, `v : Global.FinitePlace K` and `ι` a closure
embedding at `v`.

- `hasEulerPolynomialAt_heckeMultiplicityObjects_iff`: the representation
  has Euler polynomial `P` at `v` if and only if the multiplicity action is
  unramified at `v` (`IsUnramifiedAt (ModuleCat L) v`) and its
  `FrobeniusPolynomial.frobeniusEulerPolynomial v` is `P`.
- `isUnramifiedAlong_heckeMultiplicity H T X hu`: if the `H`-fixed vectors
  `(fixedVectorsActionFunctor L _ H).obj X` are unramified at `v` along `ι`,
  so is the multiplicity action.
- `geometricFrobenius_heckeMultiplicity_apply ι φ`: the geometric Frobenius
  endomorphism of the multiplicity action along `ι` sends `φ` to
  `(heckeFrobenius H X v ι).comp φ`.
- `hasEulerPolynomialAt_heckeMultiplicityObjects_of_isUnramifiedAlong hu`:
  if the `H`-fixed vectors are unramified at `v` along `ι`, the Euler
  polynomial at `v` is the reverse of the characteristic polynomial of the
  geometric Frobenius endomorphism of the multiplicity action along `ι`.

## Proof outline

`fixedVectorsHeckeMap` is Hecke-linear by
`LevelHecke.fixedVectorsMap_heckeAct`, and composition with it is
`R`-linear because a Hecke-linear map between fixed vectors commutes with
the scalars of `R` (`LinearMap.map_smul_of_tower`). The functor laws hold by
`rfl`. For smoothness, let `φ` be a Hecke-linear map. Choose a finite set
`t` spanning `T` over the Hecke algebra (`Module.Finite.fg_top`), choose for
each `u` an open subgroup fixing `φ u`, and intersect these subgroups over
`t`. An element `γ` of the intersection sends `φ` to a Hecke-linear map
agreeing with `φ` on `t`. The two maps are therefore equal
(`LinearMap.ext_on`). An inertia element acts trivially on the fixed
vectors, and therefore trivially on every Hecke-linear map into them, by
composition. The description of the Frobenius endomorphism holds by `rfl`.
The remaining statements unfold to results of
`Langlands.Shimura.ContinuousGaloisAction`.

## Provenance

This is an internal construction on top of the Hecke algebras and fixed
vectors of `Langlands.Shimura.LevelHecke` and the bridge
`Langlands.Shimura.ContinuousGaloisAction`. Harris (1999), printed p. 312,
Theorem 5.7 and formulas (5.2)-(5.6) on printed pp. 312-313, is motivation
only.
