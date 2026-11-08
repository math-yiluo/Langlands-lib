# Smooth Galois actions as continuous Galois representations

This internal construction connects smooth Galois actions on
finite-dimensional spaces with the continuous Galois representations
`Langlands.GaloisRepresentation.Objects`. A smooth representation of a
topological group on a finitely generated module is trivial on an open
subgroup. It is therefore locally constant, and continuous for every
topology on the endomorphisms. A smooth action of `Gal(K̄/K)` on a
finite-dimensional space over a topological field `L` is thus an object of
`Langlands.GaloisRepresentation.Objects K L`. At a finite place of a number
field `K`, its unramifiedness and its Frobenius Euler polynomial are those of
`Langlands.Shimura.DecompositionGroupAction` and
`Langlands.Shimura.FrobeniusPolynomial`. The declarations are in namespace
`Langlands.Shimura.ContinuousGaloisAction`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 (ii) and formula (5.6) on printed p. 313, characterizes
Galois representations by their Frobenius characteristic polynomials at
almost all unramified places. The published objects
`Langlands.GaloisRepresentation.Objects` and the predicate
`HasEulerPolynomialAt` express this matching for continuous representations.
This module lets Galois actions in the categorical form
`Action (ModuleCat L) (Field.absoluteGaloisGroup K)` or
`Rep L (Field.absoluteGaloisGroup K)` be used there, when they are smooth.

Smoothness, meaning that every vector is fixed by an open subgroup, is a
strong hypothesis. It holds for actions that factor through a finite
quotient of `Gal(K̄/K)`. It fails for λ-adic representations with infinite
image, which this module does not cover. No smoothness of any particular
action is proved here; it is a hypothesis of every construction. No
statement of Harris is formalized.

## Inputs

- `Langlands.IsSmooth ρ` (`Langlands/Representation/Smooth/Definitions.lean`):
  every vector is fixed by some open subgroup, that is, lies in
  `Langlands.fixedVectors ρ U` for some `U : OpenSubgroup G`.
- `Langlands.FiniteRepresentation L G`
  (`Langlands/Weil/Representation/Basic.lean`): the full subcategory of
  `Rep L G` on finite-dimensional spaces, with `representation`, `rank`,
  `Equiv` and `equivOfIso`.
- From `Langlands.GaloisRepresentation`
  (`Langlands/Galois/CoefficientRepresentation.lean`,
  `CompatibleFamily.lean`, `FrobeniusLift.lean`): `IsContinuous A`
  (continuity of `A.representation` for the module topology on
  `Module.End L A`), `Objects K L`, `Classes K L`,
  `characteristicPolynomial`, `eulerPolynomial`, `classEulerPolynomial`,
  `atFinitePlace`, `IsUnramifiedAt`, `frobeniusEulerPolynomial`,
  `HasEulerPolynomialAt` and `hasEulerPolynomialAt_iff`.
- From `Langlands.Shimura.DecompositionGroupAction`: `localRestriction`,
  `IsUnramifiedAt`, `IsUnramifiedAlong`, `isUnramifiedAt_iff_along` and
  `geometricFrobenius`.
- From `Langlands.Shimura.FrobeniusPolynomial`: `frobeniusEulerPolynomial`
  and `frobeniusEulerPolynomial_eq_along`.

`Field.absoluteGaloisGroup K` carries Mathlib's Krull topology.

## Smooth representations on finitely generated modules

Let `R` be a commutative ring, `G` a group with a topology, `V` a finitely
generated `R`-module and `ρ : Representation R G V`.

- `exists_openSubgroup_le_ker hρ`: if `ρ` is smooth, some open subgroup
  `U` of `G` satisfies `U ≤ ρ.ker`. This needs no compatibility between the
  topology and the group structure.
- `isLocallyConstant_of_isSmooth hρ`: if moreover left multiplication by
  each element is continuous (`SeparatelyContinuousMul G`), then `ρ` is
  locally constant.
- `continuous_of_isSmooth hρ`: under the same hypotheses, `ρ` is continuous
  for every topology on `Module.End R V`.

## Smooth Galois actions

Let `K` and `L` be fields and
`M : Action (ModuleCat L) (Field.absoluteGaloisGroup K)` with `M.V`
finite-dimensional over `L`. Write `hM` for a proof that the representation
`((Rep.ActionToRep L _).obj M).ρ` is smooth.

- `finiteRepresentation M` is `(Rep.ActionToRep L _).obj M` as an object of
  `FiniteRepresentation L (Field.absoluteGaloisGroup K)`. By
  `finiteRepresentation_representation_apply`, `g` acts by `(M.ρ g).hom`.
  By `finiteRepresentation_rank`, its rank is `Module.finrank L M.V`.

Now let `L` carry a topology.

- `isContinuous_finiteRepresentation M hM`: `finiteRepresentation M`
  satisfies `IsContinuous`.
- `toObjects M hM : Objects K L` is `finiteRepresentation M` with this
  continuity proof, and `toObjects_val` records its underlying
  representation.
- `characteristicPolynomial_toObjects` and `eulerPolynomial_toObjects`: at
  `g`, the characteristic polynomial is `(M.ρ g).hom.charpoly` and the Euler
  polynomial is its reverse.
- `toClass M hM : Classes K L` is the isomorphism class of `toObjects M hM`.
  `classEulerPolynomial_toClass` computes its Euler polynomial at `g` as
  `(M.ρ g).hom.charpoly.reverse`.
- `toObjectsEquivOfIso hM hN e`: an isomorphism `e : M ≅ N` of actions gives
  an equivalence `FiniteRepresentation.Equiv` of the underlying
  representations. Hence `toClass_eq_of_iso hM hN e`: isomorphic smooth
  actions have the same class.

## Finite places

Let `K` be a number field and `v : Global.FinitePlace K`.

- `atFinitePlace_toObjects_representation_apply`: the restriction
  `GaloisRepresentation.atFinitePlace v (toObjects M hM)` sends
  `g : LocalGroup v` to `M.ρ (localRestriction v ι g)` for Mathlib's chosen
  closure embedding `ι`.
- `isUnramifiedAt_toObjects_iff`: `GaloisRepresentation.IsUnramifiedAt` of
  `toObjects M hM` at `v` is equivalent to
  `DecompositionGroupAction.IsUnramifiedAt (ModuleCat L) v M`.
- `frobeniusEulerPolynomial_toObjects`: the published
  `GaloisRepresentation.frobeniusEulerPolynomial (toObjects M hM) v` is
  `FrobeniusPolynomial.frobeniusEulerPolynomial v M`.
- `hasEulerPolynomialAt_toObjects_iff`: `toObjects M hM` has Euler
  polynomial `P` at `v` if and only if `M` is unramified at `v` and
  `FrobeniusPolynomial.frobeniusEulerPolynomial v M = P`.
- `hasEulerPolynomialAt_toObjects_iff_along ι`: the same, along any closure
  embedding `ι`, with `IsUnramifiedAlong` and the reverse of the
  characteristic polynomial of `geometricFrobenius (ModuleCat L) v M ι`.

## Smooth linear representations

Let `A : Rep L (Field.absoluteGaloisGroup K)` be finite-dimensional over
`L`.

- An instance records that the space of the associated action
  `(Rep.RepToAction L _).obj A` is finite-dimensional.
- `repToObjects A hA`: for a proof `hA` that `A.ρ` is smooth, this is
  `toObjects` of the associated action. `repToObjects_val_obj` states that
  its underlying representation is `A` itself.
- `hasEulerPolynomialAt_repToObjects_iff`: for a number field `K`,
  `repToObjects A hA` has Euler polynomial `P` at `v` if and only if the
  associated action is unramified at `v` with Frobenius Euler polynomial
  `P`.

## Proof outline

For `exists_openSubgroup_le_ker`, choose a finite generating set `s` of
`V` and an open subgroup fixing each of its elements. The finite
intersection of these subgroups fixes the span of `s`, which is all of `V`.
Local constancy follows because `ρ` is constant on each coset `g U`. The
coset is open since left multiplication by `g⁻¹` is continuous. A locally
constant map is continuous. Continuity of `finiteRepresentation M` unfolds
`IsContinuous` to continuity of `M.ρ` composed with
`ModuleCat.endRingEquiv`. This composite is definitionally the representation
`((Rep.ActionToRep L _).obj M).ρ`, so `continuous_of_isSmooth` applies.
The statements at finite places hold by `rfl`, or follow from
`hasEulerPolynomialAt_iff`, `isUnramifiedAt_iff_along` and
`frobeniusEulerPolynomial_eq_along`.

## Provenance

This is an internal construction connecting
`Langlands.GaloisRepresentation` with
`Langlands.Shimura.DecompositionGroupAction` and
`Langlands.Shimura.FrobeniusPolynomial`. Smoothness is the published
`Langlands.IsSmooth`. Harris (1999), Theorem 5.7 (ii) and formula (5.6) on
printed p. 313, is motivation only.
