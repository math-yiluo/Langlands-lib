# The λ-adic cohomology of a geometric CM level with Harris's coefficient system

This module defines the `λ`-adic cohomology `H^d(S_U ×_F F̄, W)_λ` of a small
level of the Library's geometric CM unitary Shimura tower, with Harris's
coefficient system `W`, as a `K_λ`-vector space with its action of
`Gal(F̄/F)`. It also states, as propositions, the finite dimensionality of
this space, the continuity of the Galois action for the `λ`-adic topology,
and the unramifiedness of the action at a finite place of `F`. It proves that
unramifiedness of all torsion stages at a place gives unramifiedness of the
`λ`-adic cohomology there. All declarations are in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §3, printed pp. 306-307, takes a finite-dimensional algebraic
representation `(ρ, W)` rational over a number field `L = L(ρ)`, puts
`L_ℓ = L ⊗_Q Q_ℓ`, lets `𝒪` be the ring of integers of `L_ℓ`, and fixes a
stable `𝒪`-lattice `ℒ_W`. Printed p. 309 writes `𝒪_m = 𝒪 / ℓ^m 𝒪`. Printed
p. 311 puts `ℒ_m = ℒ ⊗_𝒪 𝒪_m`; the inverse system of the corresponding lisse
sheaves `ℒ̃_m` defines the lisse `ℓ`-adic sheaf `W̃ = lim ℒ̃_m ⊗_𝒪 L_ℓ` on the
geometric fibre `S̄_K(N)`, and Proposition 4.10 concerns its cohomology
`H^{i+j}(S̄_K(N), W̃)`. Printed p. 312 considers the `JL(π_f)`-isotypic
component of `H^{n-1}(S̄_K(N), W̃)`, and §5, printed p. 313, considers the
`λ`-adic representations of `Gal(F̄/F)` carried by such cohomology. Following
Milne, *Étale cohomology*, Chapter V, §1, printed pp. 163-165, the cohomology
of an `ℓ`-adic sheaf `F = (F_r)` is `H^d(X, F) = lim_r H^d(X, F_r)` (p. 164).
The corresponding sheaf of vector spaces is `F ⊗ Q_ℓ`, in the quotient of the
category of constructible `Z_ℓ`-sheaves by its torsion objects (p. 164), and
the discussion extends to the integers `A` of a finite extension `Ω` of `Q_ℓ`
(p. 165). The Library's coefficient field `K` is Harris's `L`, and its
level `U` plays the role of Harris's `K(N)`.

This module implements this in the Library's setting. The published
`cmHarrisEllAdicCohomology ... degree` is the `ℓ`-power torsion limit
`lim_r H^d(X̄_U, ℒ_r)`, a module over the coefficient ring
`R = HarrisCoefficientIntegers K p = ∏_{λ' | ℓ} O_{K,λ'}`, the product of the
completed valuation rings at all places of the coefficient field `K` above the
rational place `p`. Here `X̄_U = X_U ×_{Spec F} Spec F̄`, `ℓ` is the residue
characteristic of `p`, and `ℒ_r` is the `r`-th stage of the published
stable-lattice coefficient system of `W`, the lattice reduced modulo `ℓ^r`.
For a place `λ` of `K` above `p`, the `λ`-adic cohomology is the extension of
scalars

`H^d(S_U ×_F F̄, W)_λ = K_λ ⊗_R lim_r H^d(X̄_U, ℒ_r)`

along the `λ`-component `R → O_{K,λ} → K_λ`, with the Galois action extended
`K_λ`-linearly. Since `R → K_λ` factors through the projection to `O_{K,λ}`,
and `K_λ` is `O_{K,λ}` with `ℓ` inverted, this is the `λ`-component of the
torsion limit with `ℓ` inverted. This identification is explanatory and is
not formalized.

The definition does not assume that the torsion limit is finitely generated,
free or torsion-free; these properties are not known when the space is
defined. The module does not identify the space with any other definition of
`λ`-adic cohomology, does not prove finite dimensionality, continuity or
unramifiedness, and constructs no level-change map, finite-adelic action or
isotypic part. The three properties are stated as propositions for later
use. No statement of Harris is formalized.

## Inputs

The binders `E`, `F`, `A`, `D`, `L`, `C`, the named premises `preservation`
through `htor`, `q`, `U`, `[Module.Finite ℚ A]`, `K`, `W`, `ρ`, `p`,
`existence`, `geometry`, `hRigid` and the two `HasDerivedCategory` instances
(universes `wS` and `wR`) are those of the published
`Langlands.Shimura.PEL.HarrisTaylorCMEllAdicGaloisCohomology`. Below `...`
abbreviates the arguments `D C ... q U ρ p existence geometry hRigid`; `l`
is a place of `K` above `p` (`l : FinitePlacesAbove K p`), written `λ` in the
prose, and `K_λ = FiniteCompletion K l.1`.

- From `Langlands.Shimura.PEL.HarrisTaylorCMEllAdicGaloisCohomology`:
  `cmHarrisEllAdicCohomology ... degree : Action (ModuleCat R) Galois`, the
  `ℓ`-power torsion limit with its action of
  `Galois = AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`, which is
  definitionally `Field.absoluteGaloisGroup F`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMLambdaAdicRepresentation`:
  `harrisCoefficientComponentAlgebra K p l`, the algebra structure of `K_λ`
  over `R` through `harrisCoefficientComponentMap K p l`, the projection to
  the `λ`-component followed by `O_{K,λ} → K_λ`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMAdicGaloisCohomology`:
  `cmHarrisAdicCohomology_isUnramifiedAt`, unramifiedness of the torsion limit
  at a place where every torsion stage is unramified.
- From `Langlands.Shimura.LatticeGaloisRepresentation`: `baseChangeAction`,
  the Galois action on `L ⊗_O V` obtained by extending scalars, and
  `isUnramifiedAlong_baseChange`.
- From `Langlands.Shimura.DecompositionGroupAction`: `IsUnramifiedAt`, the
  inertia group at a finite place acting trivially, for Mathlib's chosen
  embedding of algebraic closures.
- From `Langlands.Shimura.ContinuousOrbitGaloisAction` (new, submitted with
  this module): `ContinuousGaloisAction.HasContinuousOrbits`, the continuity
  of all orbit maps for the module topology.

## Definitions

- `cmHarrisLambdaCohomology ... l degree :
  Action (ModuleCat K_λ) (Field.absoluteGaloisGroup F)`: the `λ`-adic
  cohomology `H^d(S_U ×_F F̄, W)_λ` above, defined as
  `LatticeGaloisRepresentation.baseChangeAction (L := K_λ)` of
  `cmHarrisEllAdicCohomology ... degree`, with the algebra structure
  `harrisCoefficientComponentAlgebra K p l`.

## Propositions

These are the Prop-valued properties of item 4 of the task, stated at a fixed
level.

- `CMHarrisLambdaCohomologyFiniteDimensional ... l degree`: the space of
  `cmHarrisLambdaCohomology ... l degree` is finite-dimensional over `K_λ`.
- `CMHarrisLambdaCohomologyContinuous ... l degree`: the Galois action has
  continuous orbits, `HasContinuousOrbits`: for every vector `x`, the map
  `g ↦ g · x` from `Gal(F̄/F)` with its Krull topology to the space with its
  module topology over `K_λ` is continuous. On a finite-dimensional space the
  module topology is the `λ`-adic topology of `K_λ^n` in any basis, and the
  condition implies continuity of the representation on the endomorphisms
  (`isContinuous_finiteRepresentation_of_hasContinuousOrbits`). The condition
  is stated without finite dimensionality, so it can be assumed separately.
- `CMHarrisLambdaCohomologyUnramifiedAt ... l degree w`: for a finite place
  `w` of `F`, the action is unramified at `w` in the sense of
  `IsUnramifiedAt`: every element of the inertia group at `w` acts as the
  identity.
- `CMHarrisLambdaCohomologyAlmostEverywhereUnramified ... l degree`: there is a
  finite set `S` of finite places of `F` such that the action is unramified at
  every `w ∉ S`, the condition imposed on the `λ`-adic representations of
  Harris (1999), printed p. 313.

The task asks for unramifiedness "at a finite place of good reduction". The
Library has no notion of good reduction for these Shimura varieties, so the
proposition is stated for every finite place `w`. A user restricts it to
places of good reduction once that notion exists; `w` is an explicit
argument.

## Results

- `cmHarrisLambdaCohomology_V`: the space is `K_λ ⊗_R V`, where `V` is the
  space of the torsion limit and `K_λ` is an `R`-algebra through the
  `λ`-component.
- `cmHarrisLambdaCohomology_ρ_hom g`: the action of `g` is the extension of
  scalars `(g on V).baseChange K_λ`.
- `cmHarrisLambdaCohomology_ρ_tmul g a x`: on pure tensors,
  `g · (a ⊗ x) = a ⊗ (g · x)`.
- `cmHarrisLambdaCohomologyUnramifiedAt_of_stages ... l degree w hu`: if every
  torsion stage `H^d(X̄_U, ℒ_r)` of
  `cmHarrisGeometricGaloisCohomologyAction` for `m = ℓ` is unramified at `w`,
  then `CMHarrisLambdaCohomologyUnramifiedAt ... l degree w` holds.

## Proof outline

The three descriptive results hold by definition (`rfl`). For the last
result, the published `cmHarrisAdicCohomology_isUnramifiedAt` gives that the
torsion limit is unramified at `w`. Extension of scalars preserves this: an
inertia element acting as the identity on `V` acts on `K_λ ⊗_R V` as the
base change of the identity, which is the identity
(`LatticeGaloisRepresentation.isUnramifiedAlong_baseChange`).

## Provenance

The cohomology is the `λ`-component of the cohomology of Harris (1999),
printed pp. 311-313, with coefficients in the lisse sheaf
`W̃ = lim ℒ̃_m ⊗_𝒪 L_ℓ`, following Milne, Chapter V, §1, printed pp. 163-165,
for the cohomology of `ℓ`-adic sheaves and the passage to sheaves of vector
spaces. The ring `R` is Harris's `𝒪 = ∏_{λ | ℓ} O_{L,λ}`, and
`L_ℓ = ∏_{λ | ℓ} L_λ`, so the `λ`-component of `L_ℓ` is `K_λ`. The Library's
torsion limit `lim_r H^d(X̄_U, ℒ_r)` is the integral version; this module adds
the extension of scalars to `K_λ`. The propositions are internal formulations of the properties
required of `λ`-adic representations on printed p. 313: finite dimensionality,
continuity, and unramifiedness at a place or at all but finitely many places.
The continuity proposition uses continuous orbit maps so that it can be
stated before finite dimensionality is known.
