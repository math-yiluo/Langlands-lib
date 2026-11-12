# Continuous Galois representations on fixed-level isotypic parts and multiplicity spaces

This internal construction makes three spaces, built from a smooth
representation with a commuting Galois action, into continuous Galois
representations with Euler polynomials. The Galois action is assumed to be
continuous, not smooth. The spaces are the fixed vectors of an isotypic part,
the multiplicity space of intertwining maps, and the Hecke multiplicity space
of Hecke-linear maps. All declarations are in namespace
`Langlands.Shimura.ContinuousIsotypicGaloisRepresentation`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5, printed p. 312, writes `H^{n-1}(S_K(N), W)[π]` for the
`JL(π_f)`-isotypic component of the cohomology at level `K(N)`. Printed p. 313
considers `λ`-adic representations of `Gal(F̄/F)` and their local factors
(5.6), built from the eigenvalues of a geometric Frobenius. Kottwitz (1992),
*On the λ-adic representations associated to some simple Shimura varieties*,
§1, printed p. 655, uses the space `W^i(π_f) = Hom_{H_K}(π_f^K, H^i(S_K, F))`
of Hecke-linear maps.

The `λ`-adic cohomology of a Shimura variety carries a Galois action that is
continuous for the `λ`-adic topology but not smooth. So the published smooth
constructions (`Langlands.Shimura.FixedVectorGaloisRepresentation`,
`Langlands.Shimura.HeckeMultiplicityGaloisRepresentation`) do not apply to it.
This module gives the continuous counterparts. Continuity is assumed only for
the `H`-fixed vectors `X^H`, as continuous orbit maps
(`ContinuousGaloisAction.HasContinuousOrbits`). Each space below maps to `X^H`
by an equivariant linear map or a jointly injective family of such maps. The
transfer lemmas of `Langlands.Shimura.ContinuousOrbitTransfer` then give
continuity, and unramifiedness wherever `X^H` is unramified. The results are
generic: no Shimura variety appears.

## Setting

`F` is a field and `Γ = Field.absoluteGaloisGroup F`. `M` is a field, with a
topology making it a topological ring where Galois representations are built.
`G` is a group with a topology and `H : Subgroup G`.
`X : Action (SmoothRep M G) Γ` is a smooth representation of `G` over `M` with
a commuting action of `Γ` by intertwiners. `X^H` denotes
`(fixedVectorsActionFunctor M Γ H).obj X`, the Galois action on
`fixedVectors X.V.representation H`. `τ : Representation M G U` is a
representation of `G` on an `M`-module `U`; no smoothness or irreducibility of
`τ` is assumed. `T` is a module over the published level Hecke algebra
`LevelHecke.LevelHeckeAlgebra M H`. The main example is `τ^H` with the
published module structure `LevelHecke.instModuleFixedVectors`.

## Definitions and results

### Finite-dimensional actions with continuous orbits

For `A : Action (ModuleCat M) Γ` with `A.V` finite over `M`:

- `continuousOrbitsObjects A hA : Langlands.GaloisRepresentation.Objects F M`
  is `LatticeGaloisRepresentation.ofContinuous A` applied to the continuity
  proved by `isContinuous_finiteRepresentation_of_hasContinuousOrbits` from
  `hA : HasContinuousOrbits A`. Its representation is `g ↦ (A.ρ g).hom`, and its
  rank is `Module.finrank M A.V`.
- For a number field `F` and a finite place `v`:
  `hasEulerPolynomialAt_continuousOrbitsObjects_iff` says that `P` is the Euler
  polynomial at `v` iff `A` is unramified at `v` with Frobenius Euler polynomial
  `P`. `hasEulerPolynomialAt_continuousOrbitsObjects_iff_along ι` states the same
  along any closure embedding `ι` at `v`, with `P` the reversed characteristic
  polynomial of the geometric Frobenius endomorphism
  `DecompositionGroupAction.geometricFrobenius` along `ι`.
  `hasEulerPolynomialAt_continuousOrbitsObjects_of_isUnramifiedAlong` is the
  resulting statement for an action unramified along `ι`.

### Fixed vectors of an isotypic part (Harris's `H^{n-1}(S_K(N), W)[π]`)

- `isotypicFixedVectorsι τ H X` is the morphism of Galois actions from the
  `H`-fixed vectors of the `τ`-isotypic part
  (`(fixedVectorsActionFunctor M Γ H).obj ((isotypicActionFunctor τ Γ).obj X)`)
  to `X^H`, induced by the published inclusion `isotypicActionι`. It is the
  identity on underlying vectors (`coe_isotypicFixedVectorsι_apply`), injective
  (`isotypicFixedVectorsι_injective`) and equivariant
  (`isotypicFixedVectorsι_comm`).
- An instance: if `X^H` is finite-dimensional, so are the `H`-fixed vectors of
  the isotypic part.
- `hasContinuousOrbits_isotypicFixedVectors`: continuous orbits pass from a
  finite-dimensional `X^H` to the `H`-fixed vectors of the isotypic part.
- `isotypicFixedVectorsObjects τ H X hX : Objects F M`, for `X^H`
  finite-dimensional with continuous orbits (`hX`). A Galois element acts by its
  action on `X` (`coe_isotypicFixedVectorsObjects_representation_apply`).
- `hasEulerPolynomialAt_isotypicFixedVectorsObjects hu`: if `X^H` is unramified
  at `v` along `ι`, the Euler polynomial at `v` is the reversed characteristic
  polynomial of the geometric Frobenius endomorphism of the fixed vectors of the
  isotypic part along `ι`. Unramifiedness of these fixed vectors is the published
  `FixedVectorGaloisRepresentation.isUnramifiedAlong_fixedVectors_isotypic`.

### The multiplicity space `Hom_G(τ, X)`

The spanning hypothesis `hgen` used below is
`Submodule.span M (⋃ g : G, τ g '' (fixedVectors τ H : Set U)) = ⊤`: the
translates of the `H`-fixed vectors of `τ` span `U`. For an irreducible `τ`
with `τ^H ≠ 0` it holds because the span is a nonzero `G`-stable subspace; this
remark is not formalized here.

- `multiplicityRestriction τ H X : Hom_G(τ, X) →ₗ[M] (τ^H →ₗ[M] X^H)` restricts
  an intertwining map to the `H`-fixed vectors (the published
  `fixedVectorsMap`). `multiplicityEvaluation τ H X u` is its value at
  `u ∈ τ^H`, an `M`-linear map `Hom_G(τ, X) → X^H`. Evaluation commutes with the
  Galois actions: the published `multiplicityActionFunctor` on the source, `X^H`
  on the target (`multiplicityEvaluation_comm`).
- `eq_zero_of_forall_multiplicityEvaluation_eq_zero hgen`: under `hgen`, an
  intertwining map vanishing on `τ^H` is zero. Hence
  `multiplicityRestriction_injective hgen`.
- `finite_multiplicity hgen`: if `τ^H` and `X^H` are finite-dimensional and
  `hgen` holds, then `Hom_G(τ, X)` is finite-dimensional. An instance transports
  finiteness of `τ.IntertwiningMap X.V.representation` to the space of the
  multiplicity action.
- `hasContinuousOrbits_multiplicity hgen hX` and
  `isUnramifiedAlong_multiplicity hgen hu`: continuity of orbits (for a
  finite-dimensional multiplicity space) and unramifiedness pass from `X^H`.
- `multiplicityObjects τ H X hgen hX : Objects F M`, for a finite-dimensional
  multiplicity space. A Galois element acts by composition with its action on
  `X` (`multiplicityObjects_representation_apply`), and the rank is the dimension
  of `Hom_G(τ, X)` (`multiplicityObjects_rank`).
- `hasEulerPolynomialAt_multiplicityObjects hu`: if `X^H` is unramified at `v`
  along `ι`, the Euler polynomial at `v` is the reversed characteristic
  polynomial of the geometric Frobenius endomorphism of the multiplicity space
  along `ι`.

### The Hecke multiplicity space `Hom_{H(H)}(T, X^H)`

- `heckeMultiplicityEvaluation H T X t` evaluates Hecke-linear maps `T → X^H`
  at `t`, an `M`-linear map to `X^H`. It commutes with the Galois actions: the
  published `heckeMultiplicityActionFunctor` on the source, `X^H` on the target
  (`heckeMultiplicityEvaluation_comm`). The family over all `t` is jointly
  injective, since maps that agree everywhere are equal.
- `finite_heckeMultiplicity`: if `T` is finitely generated over the Hecke
  algebra and `X^H` is finite-dimensional, then `Hom_{H(H)}(T, X^H)` is
  finite-dimensional.
- `hasContinuousOrbits_heckeMultiplicity hX`: continuous orbits pass from `X^H`
  to a finite-dimensional Hecke multiplicity space.
- `heckeMultiplicityContinuousObjects H T X hX : Objects F M`, for a
  finite-dimensional Hecke multiplicity space. A Galois element acts by
  composition with the published `fixedVectorsHeckeMap H (X.ρ g)`. The rank is
  the dimension of the Hecke multiplicity space.
- `hasEulerPolynomialAt_heckeMultiplicityContinuousObjects hu`: if `X^H` is
  unramified at `v` along `ι`, the Euler polynomial at `v` is the reversed
  characteristic polynomial of the geometric Frobenius endomorphism of the Hecke
  multiplicity space along `ι`. Unramifiedness is the published
  `isUnramifiedAlong_heckeMultiplicity`. By the published
  `geometricFrobenius_heckeMultiplicity_apply`, this Frobenius endomorphism is
  composition with the Hecke-linear Frobenius endomorphism of `X^H`.

## Proof outline

- Euler polynomials: the iff statement is the published
  `LatticeGaloisRepresentation.hasEulerPolynomialAt_ofContinuous_iff`. The
  version along `ι` rewrites it with `isUnramifiedAt_iff_along` and
  `FrobeniusPolynomial.frobeniusEulerPolynomial_eq_along`.
- Isotypic part: the inclusion is injective because the inclusion of the
  isotypic part is (`isotypicι_app_injective`). Equivariance holds by `rfl`.
  Finiteness follows from `Module.Finite.of_injective` into the
  finite-dimensional `X^H`. Continuity follows from
  `hasContinuousOrbits_of_injective`.
- Multiplicity space: if `φ` vanishes on `τ^H`, then
  `φ (τ g u) = g · φ u = 0` for every `g ∈ G` and `u ∈ τ^H`. So `φ` vanishes
  on a spanning set, hence is zero (`LinearMap.ext_on`). The space
  `τ^H →ₗ[M] X^H` is finite-dimensional when both factors are, which gives
  `finite_multiplicity`. Continuity and unramifiedness use
  `hasContinuousOrbits_of_forall_eq_zero` and
  `isUnramifiedAlong_of_forall_eq_zero` with the family `multiplicityEvaluation`.
- Hecke multiplicity space: for finiteness, choose finitely many generators `s`
  of `T` (`Module.Finite.fg_top`). The map `φ ↦ (φ t)_{t ∈ s}` into the
  finite-dimensional `s → X^H` is injective (`LinearMap.ext_on`). Continuity uses
  `hasContinuousOrbits_of_forall_eq_zero` with the evaluation family.

## Provenance

This is an internal construction. It sits on top of the published isotypic
parts and multiplicity spaces (`Langlands.Shimura.IsotypicGaloisAction`), Hecke
multiplicity spaces (`Langlands.Shimura.HeckeMultiplicityGaloisRepresentation`),
fixed vectors with Galois action (`Langlands.Shimura.LevelHeckeAction`), and the
continuous Galois representations of `Langlands.Shimura.LatticeGaloisRepresentation`.

Harris (1999), §5, printed pp. 312-313, is the source of the objects. They are
the isotypic component `H^{n-1}(S_K(N), W)[π]` at a fixed level and the
`λ`-adic representations with their Frobenius eigenvalues (5.6). Kottwitz
(1992), §1, printed p. 655, is the source of the Hecke multiplicity space
`Hom_{H_K}(π_f^K, H^i(S_K, F))`. The Euler polynomial is that of the Library's
`HasEulerPolynomialAt`, the reversed characteristic polynomial
`det(1 − X · σ(Fr_w))` of a geometric Frobenius. Its roots are the inverses of
the eigenvalues `β` of `σ(Fr_w)` in (5.6). The normalization of the local factor
in (5.6) by the absolute values `|β|` is not formalized here. No statement of
Harris or Kottwitz is formalized in this module.
