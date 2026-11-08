# Smooth multiplicity spaces as continuous Galois representations

This internal construction makes the multiplicity spaces of
`Langlands.Shimura.IsotypicGaloisAction` into continuous Galois
representations. Let `τ` be a representation of a group `G` that is finitely
generated over the group algebra. Let `X` be a smooth representation of `G`
with a commuting action of a topological group `Γ`, and suppose that this
action is smooth, meaning that every vector is fixed by an open subgroup of
`Γ`. Then two further actions of `Γ` are smooth: the restricted action on
the `τ`-isotypic part of `X`, and the action on the multiplicity space
`Hom_G(τ, X)` by composition. For `Γ = Gal(K̄/K)`, a multiplicity space that
is finite-dimensional over a topological field `L` is then an object of
`Langlands.GaloisRepresentation.Objects K L`. At a finite place `v` of a
number field `K` where `X` is unramified, its Euler polynomial is the
Frobenius Euler polynomial of the multiplicity space. The declarations are
in namespace `Langlands.Shimura.MultiplicityGaloisRepresentation`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, Theorem 5.7 on printed p. 313, describes Galois representations that
occur in isotypic parts of the cohomology of Shimura varieties. Part (ii)
characterizes them by their Frobenius characteristic polynomials at almost
all unramified places, through formula (5.6). Formulas (5.2), (5.3) and
(5.5) on printed pp. 312-313 use spaces of intertwining maps of
representations. This module connects the multiplicity spaces with Galois
action of `Langlands.Shimura.IsotypicGaloisAction` to the continuous Galois
representations `Langlands.GaloisRepresentation.Objects` and the predicate
`HasEulerPolynomialAt`, when the action on `X` is smooth.

Smoothness of the action of `Γ` on `X` is a hypothesis of every result.
Finite generation of `τ` over the group algebra and finite dimension of the
multiplicity space are hypotheses too. The module proves no smoothness,
finiteness or unramifiedness of any particular action. No statement of
Harris is formalized.

## Inputs

- `Langlands.IsSmooth ρ` (`Langlands/Representation/Smooth/Definitions.lean`):
  every vector lies in `Langlands.fixedVectors ρ V` for some open subgroup
  `V`.
- From `Langlands.Shimura.IsotypicGaloisAction` (candidate
  `06482d9c-709f-449e-bd42-538102e24d51`, accepted and awaiting
  publication): `galoisRepresentation X`, the representation of `Γ` on the
  space of `X : Action (SmoothRep R G) Γ`, with `galoisRepresentation_apply`
  and `galoisRepresentation_commutes`; `isotypicGaloisRepresentation τ Γ X`
  on the `τ`-isotypic part; `multiplicityActionFunctor τ Γ` and
  `multiplicityRepresentation τ Γ X` on `τ.IntertwiningMap X.V.representation`.
- From `Langlands.Shimura.IsotypicDecompositionAction` (candidate
  `65e8e325-c197-47a1-ab0b-91df2848f8b4`, accepted and awaiting
  publication): `IsUnramifiedAlong.multiplicity`.
- From `Langlands.Shimura.ContinuousGaloisAction` (candidate
  `5c2f38db-a736-4706-aa12-6de9f8bf0b33`, accepted and awaiting
  publication): `toObjects`, `hasEulerPolynomialAt_toObjects_iff` and
  `hasEulerPolynomialAt_toObjects_iff_along`. From
  `Langlands.Shimura.FrobeniusPolynomial` (same candidate):
  `frobeniusEulerPolynomial`.
- From the published `Langlands.Shimura.DecompositionGroupAction`:
  `IsUnramifiedAt`, `IsUnramifiedAlong` and `geometricFrobenius`.
- From the published `Langlands.Cohomology.HyperextHomLocalization`:
  `HyperextScalarExtension.exists_finset_eq_top_of_finite_asModule`. If `τ`
  is finitely generated over `R[G]`, there is a finite set `t` of vectors
  such that every `G`-stable submodule containing `t` is everything.

## Smoothness

Let `R` be a commutative ring and `G` a group with a topology. Let `U` be an
`R`-module and `τ : Representation R G U`. Let `Γ` be a group with a topology
and `X : Action (SmoothRep R G) Γ`, and let `hX` be a proof that
`galoisRepresentation X` is smooth.

- `isSmooth_isotypicGaloisRepresentation τ hX`: the restricted
  representation `isotypicGaloisRepresentation τ Γ X` on the `τ`-isotypic
  part is smooth.
- `isSmooth_multiplicityRepresentation τ hX`: if
  `[Module.Finite (MonoidAlgebra R G) τ.asModule]`, the representation
  `multiplicityRepresentation τ Γ X` on `Hom_G(τ, X)` is smooth.

## Continuous Galois representations

Let `K` and `L` be fields and `G` a group with a topology. Let `U` be an
`L`-module, `τ : Representation L G U` and
`X : Action (SmoothRep L G) (Field.absoluteGaloisGroup K)`.

- An instance: if `τ.IntertwiningMap X.V.representation` is
  finite-dimensional over `L`, so is the space of
  `(multiplicityActionFunctor τ _).obj X`.

Assume now `[Module.Finite (MonoidAlgebra L G) τ.asModule]`,
`[Module.Finite L (τ.IntertwiningMap X.V.representation)]`, a topology on
`L`, and `hX : IsSmooth (galoisRepresentation X)`.

- `multiplicityObjects τ X hX : Objects K L` is
  `ContinuousGaloisAction.toObjects` of `(multiplicityActionFunctor τ _).obj X`,
  with the smoothness given by `isSmooth_multiplicityRepresentation`.
- `multiplicityObjects_representation_apply`: `g` sends an intertwining map
  `φ` to `(SmoothRep.hom (X.ρ g)).comp φ`.
- `multiplicityObjects_rank`: the rank is
  `Module.finrank L (τ.IntertwiningMap X.V.representation)`.

Let `K` be a number field and `v : Global.FinitePlace K`.

- `hasEulerPolynomialAt_multiplicityObjects_iff`: `multiplicityObjects τ X hX`
  has Euler polynomial `P` at `v` if and only if the action
  `(multiplicityActionFunctor τ _).obj X` is unramified at `v`
  (`IsUnramifiedAt (ModuleCat L) v`) and its
  `FrobeniusPolynomial.frobeniusEulerPolynomial v` is `P`.
- `hasEulerPolynomialAt_multiplicityObjects_of_isUnramifiedAlong hu`: if `X`
  is unramified at `v` along a closure embedding `ι`
  (`IsUnramifiedAlong (SmoothRep L G) v X ι`), the Euler polynomial at `v`
  is the reverse of the characteristic polynomial of
  `geometricFrobenius (ModuleCat L) v ((multiplicityActionFunctor τ _).obj X) ι`.
- `hasEulerPolynomialAt_multiplicityObjects_of_isUnramifiedAt hu`: if `X` is
  unramified at `v`, the Euler polynomial at `v` is
  `FrobeniusPolynomial.frobeniusEulerPolynomial v` of the multiplicity
  action.

## Proof outline

For the isotypic part, an open subgroup fixing a vector `x.1` of `X` fixes
`x`, because the isotypic part is a subtype. For the multiplicity space,
let `φ : Hom_G(τ, X)`. Take the finite set `t` of
`exists_finset_eq_top_of_finite_asModule`, choose for each `u` an open
subgroup fixing `φ u`, and intersect these subgroups over `t`. For `γ` in
the intersection, the vectors `u` with `γ • φ u = φ u` form an `R`-submodule
(`LinearMap.eqLocus`). It is `G`-stable because `φ` intertwines and the
actions of `G` and `Γ` on `X` commute. It contains `t`, so it is everything,
and `γ` fixes `φ`. The remaining statements unfold to the corresponding
results of `Langlands.Shimura.ContinuousGaloisAction`, by `rfl` or by
`IsUnramifiedAlong.multiplicity`, which carries unramifiedness from `X` to
its multiplicity spaces.

## Provenance

This is an internal construction connecting
`Langlands.Shimura.IsotypicGaloisAction` with
`Langlands.Shimura.ContinuousGaloisAction`. Harris (1999), Theorem 5.7 and
formulas (5.2)-(5.6) on printed pp. 312-313, is motivation only.
