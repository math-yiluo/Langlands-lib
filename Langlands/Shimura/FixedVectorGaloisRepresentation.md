# Fixed vectors of smooth Galois actions as continuous Galois representations

This internal construction makes the fixed vectors of
`Langlands.Shimura.LevelHecke` into continuous Galois representations. Let
`X` be a smooth representation of a group `G` with a commuting action of a
topological group `Γ`, and suppose that this action is smooth, meaning that
every vector is fixed by an open subgroup of `Γ`. Then for every subgroup `H`
of `G`, the induced action of `Γ` on the `H`-fixed vectors of `X` is smooth.
For `Γ = Gal(K̄/K)`, `H`-fixed vectors that are finite-dimensional over a
topological field `L` are then an object of
`Langlands.GaloisRepresentation.Objects K L`. At a finite place `v` of a
number field `K` where `X` is unramified, its Euler polynomial is the
reversed characteristic polynomial of the geometric Frobenius endomorphism
of the fixed vectors. On the module of `H`-fixed vectors over the Hecke
algebra of `H`, the geometric Frobenius endomorphism is Hecke-linear, and
the Euler polynomial is the reversed characteristic polynomial over `L` of
this Hecke-linear map. The declarations are in namespace
`Langlands.Shimura.FixedVectorGaloisRepresentation`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, part (i), concerns the representation
of `Gal(F̄/F)` on `H^{n-1}(S_K(N), W)[π]`, the cohomology of the Shimura
variety at the level `K(N)`. Part (ii) characterizes it by Frobenius
characteristic polynomials at almost all unramified places, through formula
(5.6). For a smooth representation `X` of the finite-adelic group, the
vectors fixed by a compact open subgroup are the generic form of such
cohomology at a fixed level. This module connects these fixed vectors, with
their Galois action and their structure of modules over the Hecke algebra of
`Langlands.Shimura.LevelHeckeAlgebra`, to the continuous Galois
representations `Langlands.GaloisRepresentation.Objects` and the predicate
`HasEulerPolynomialAt`.

Smoothness of the action of `Γ` on `X` and finite dimension of the fixed
vectors are hypotheses. The subgroup `H` is arbitrary; no compactness or
openness is assumed. The module proves no smoothness, finiteness or
unramifiedness of any particular action. No statement of Harris is
formalized.

## Inputs

- `Langlands.IsSmooth ρ` (`Langlands/Representation/Smooth/Definitions.lean`)
  and the fixed vectors `Langlands.fixedVectors ρ H`, the `R`-submodule of
  vectors fixed by every element of `H`, with `fixedVectorsMap`.
- From the published `Langlands.Shimura.LevelHeckeAction`:
  `LevelHecke.fixedVectorsActionFunctor R Γ H`, the `H`-fixed vectors of
  objects of `Action (SmoothRep R G) Γ`, with the induced action of `Γ`.
  `LevelHecke.fixedVectorsFunctor R H` is the underlying functor.
- From the published `Langlands.Shimura.LevelHeckeAlgebra` and
  `Langlands.Shimura.LevelHeckeModule`: `LevelHecke.LevelHeckeAlgebra R H`,
  an `R`-algebra acting on `fixedVectors ρ H` compatibly with `R`
  (`IsScalarTower`), and `LevelHecke.heckeModuleActionFunctor R Γ H`, the
  `H`-fixed vectors as modules over this algebra with the action of `Γ`.
- From `Langlands.Shimura.IsotypicGaloisAction` (candidate
  `06482d9c-709f-449e-bd42-538102e24d51`, accepted and awaiting
  publication): `galoisRepresentation X`, the representation of `Γ` on the
  space of `X`.
- From `Langlands.Shimura.ContinuousGaloisAction` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication): `toObjects`, `hasEulerPolynomialAt_toObjects_iff` and
  `hasEulerPolynomialAt_toObjects_iff_along`. From
  `Langlands.Shimura.FrobeniusPolynomial` (same candidate):
  `frobeniusEulerPolynomial`.
- From `Langlands.Shimura.IsotypicDecompositionAction` (candidate
  `65e8e325-c197-47a1-ab0b-91df2848f8b4`, accepted and awaiting
  publication): `IsUnramifiedAlong.mapAction`.
- From the published `Langlands.Shimura.DecompositionGroupAction`:
  `localRestriction`, `IsUnramifiedAt`, `IsUnramifiedAlong` and
  `geometricFrobenius`. `GaloisRepresentation.geometricFrobeniusLift v` is
  the published chosen geometric Frobenius lift.

## Smoothness

Let `R` be a commutative ring and `G` a group with a topology. Let `H` be a
subgroup of `G`, `Γ` a group with a topology and
`X : Action (SmoothRep R G) Γ`.

- `isSmooth_fixedVectors H hX`: if `galoisRepresentation X` is smooth, so
  is the representation
  `((Rep.ActionToRep R Γ).obj ((fixedVectorsActionFunctor R Γ H).obj X)).ρ`
  of `Γ` on the `H`-fixed vectors.

## The Frobenius endomorphism of Hecke modules

Let `K` be a number field, `v : Global.FinitePlace K` and `ι` a closure
embedding at `v` (`ClosureEmbedding (NumberField.FinitePlace.embedding v)`).
Let `X : Action (SmoothRep R G) (Field.absoluteGaloisGroup K)`.

- `heckeFrobenius H X v ι` is the geometric Frobenius endomorphism at `v`
  along `ι` (`DecompositionGroupAction.geometricFrobenius`) of the Hecke
  module `(heckeModuleActionFunctor R _ H).obj X`, as a
  `LevelHeckeAlgebra R H`-linear endomorphism of `fixedVectors X.V.representation H`.
- `coe_heckeFrobenius_apply`: on a fixed vector `x` it is the action on `X`
  of `localRestriction v ι (geometricFrobeniusLift v)` applied to `x`.
- `heckeFrobenius_smul`: it commutes with every element of the Hecke
  algebra.

## Continuous Galois representations

Let `K` and `L` be fields, `G` a group with a topology, `H` a subgroup of
`G` and `X : Action (SmoothRep L G) (Field.absoluteGaloisGroup K)`.

- An instance: if `fixedVectors X.V.representation H` is finite-dimensional
  over `L`, so is the space of `(fixedVectorsActionFunctor L _ H).obj X`.

Assume now that `fixedVectors X.V.representation H` is finite-dimensional,
that `L` has a topology, and let `hX` be a proof that
`galoisRepresentation X` is smooth.

- `fixedVectorsObjects H X hX : Objects K L` is
  `ContinuousGaloisAction.toObjects` of `(fixedVectorsActionFunctor L _ H).obj X`,
  with the smoothness given by `isSmooth_fixedVectors`.
- `fixedVectorsObjects_representation_apply`: `g` acts by
  `fixedVectorsMap (SmoothRep.hom (X.ρ g)) H`.
- `fixedVectorsObjects_rank`: the rank is
  `Module.finrank L (fixedVectors X.V.representation H)`.

Let `K` be a number field and `v : Global.FinitePlace K`.

- `hasEulerPolynomialAt_fixedVectorsObjects_iff`: `fixedVectorsObjects H X hX`
  has Euler polynomial `P` at `v` if and only if
  `(fixedVectorsActionFunctor L _ H).obj X` is unramified at `v`
  (`IsUnramifiedAt (ModuleCat L) v`) and its
  `FrobeniusPolynomial.frobeniusEulerPolynomial v` is `P`.
- `isUnramifiedAlong_fixedVectors H X hu`: if `X` is unramified at `v` along
  `ι` (`IsUnramifiedAlong (SmoothRep L G) v X ι`), so are its `H`-fixed
  vectors.
- `isUnramifiedAlong_fixedVectors_isotypic H X τ hu`: for a representation
  `τ` of `G` on an `L`-module, if the `H`-fixed vectors of `X` are unramified
  at `v` along `ι`, so are the `H`-fixed vectors of the `τ`-isotypic part
  `(isotypicActionFunctor τ _).obj X`.
- `hasEulerPolynomialAt_fixedVectorsObjects_of_isUnramifiedAlong hu`: if the
  `H`-fixed vectors are unramified at `v` along `ι`, the Euler polynomial at
  `v` is the reverse of the characteristic polynomial of
  `geometricFrobenius (ModuleCat L) v ((fixedVectorsActionFunctor L _ H).obj X) ι`.
- `hasEulerPolynomialAt_fixedVectorsObjects_of_isUnramifiedAt hu`: if the
  `H`-fixed vectors are unramified at `v`, the Euler polynomial at `v` is
  their `FrobeniusPolynomial.frobeniusEulerPolynomial v`.
- `geometricFrobenius_fixedVectors_eq_restrictScalars ι`: the geometric
  Frobenius endomorphism of the fixed vectors along `ι` is
  `(heckeFrobenius H X v ι).restrictScalars L`.
- `hasEulerPolynomialAt_fixedVectorsObjects_heckeFrobenius hu`: if the
  `H`-fixed vectors are unramified at `v` along `ι`, the Euler polynomial at
  `v` is `((heckeFrobenius H X v ι).restrictScalars L).charpoly.reverse`.

The unramifiedness hypotheses of the Euler-polynomial results concern the
fixed vectors, not `X`: a smooth representation of an adelic group with a
Galois action, such as a colimit of cohomology over shrinking levels, is
typically ramified at many places even when its fixed vectors under a given
level are not.

## Proof outline

An open subgroup of `Γ` fixing the vector `x.1` of `X` fixes the fixed
vector `x`, because the fixed vectors form a submodule. Unramifiedness of
the fixed vectors of `X` is `IsUnramifiedAlong.mapAction` for
`fixedVectorsFunctor L H`. For the isotypic part, a fixed vector `x` of the
isotypic part has underlying vector `x.1.1` in `X`, which is again
`H`-fixed; an inertia element acts on `x` through its action on `x.1.1`,
which is trivial by hypothesis. The geometric Frobenius endomorphisms of the
fixed vectors and of the Hecke module are both given by the action of the
same Galois element on the same vectors, so their comparison holds by
`rfl`. The remaining statements unfold to the corresponding results of
`Langlands.Shimura.ContinuousGaloisAction`, or hold by `rfl`.

## Provenance

This is an internal construction connecting the fixed vectors and Hecke
modules of `Langlands.Shimura.LevelHecke` with
`Langlands.Shimura.ContinuousGaloisAction`. Harris (1999), Theorem 5.7 and
formula (5.6) on printed p. 313, is motivation only.
