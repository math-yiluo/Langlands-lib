# Uniform finite expansion of central action operators

Worker 189 proves the exact published proposition
`Langlands.CentralOperatorExpansionStatement.{uG,uA,uV}` with the closed theorem
`Langlands.centralOperatorExpansion`. The group, parameter group and vector-space
universes remain independent. The statement module and all its imported files
are unchanged.

Let `ρ` be an admissible complex representation of a topological group `G`,
finitely generated for its actual `MonoidAlgebra ℂ G` action, and let
`c : A →* Subgroup.center G` be continuous, where `A` is an abelian topological
group. Write `σ(a) = ρ(c(a))` and let `S` be the complex span of these actual
endomorphisms. The theorem produces a finite set `X` of continuous functions
whose left translates span finite-dimensional spaces and operators `T(χ) ∈ S`
such that `σ(a) = ∑ χ ∈ X, χ(a) • T(χ)` for every `a`. This is one uniform
endomorphism equality, before evaluation on any vector or linear functional.

## Finite-dimensional operator span

`centralActionSpan_finite` imports and applies
`Langlands.finite_intertwiningMap_of_finiteType` from
`Langlands.Representation.Smooth.IntertwinerFiniteness` to `ρ` as both source and
target. That published theorem evaluates intertwiners on a finite family of
actual group-algebra generators. Smoothness provides an open stabilizer for each
generator; admissibility makes the corresponding target fixed spaces finite
dimensional. Evaluation is injective because group-algebra-linear maps are
determined by generators.

The forgetful linear map from intertwiners to complex-linear endomorphisms
therefore has finite-dimensional image. Each `σ(a)` belongs to this image by
Mathlib's `Representation.IntertwiningMap.centralMul`, using the actual center
membership of `c(a)`. Hence `S` is a subspace of this finite-dimensional image
and is finite dimensional. This helper requires no topology on `A` and does not
use a topological-group instance on `G` beyond the topological space needed to
state admissibility.

## Local constancy of the whole action

`centralAction_isLocallyConstant` needs smoothness and finite generation; it does
not need admissibility. Choose group-algebra generators `vᵢ` and open subgroups
`Kᵢ` fixing them. For each `a ∈ A`, the set of `b` such that
`c(a)⁻¹ c(b) ∈ Kᵢ` for every `i` is an open neighborhood of `a`. It is a finite
intersection of preimages under continuous maps. On this neighborhood,
`σ(b)vᵢ = σ(a)vᵢ` for each generator. Both operators are intertwiners because
their group elements are central. Transport to group-algebra-linear maps and
extensionality on the generating family give `σ(b) = σ(a)` on the whole
representation. No topology is placed on `V` or the endomorphism space; local
constancy is formulated for a function into an arbitrary type.

## Coordinates, translates, and the finite set

Choose the finite basis `B = Module.finBasis ℂ S` and let
`χᵢ(a) = B.coord i (σ(a))`, viewing `σ(a)` as an element of `S`. The preceding
local constancy passes to `S` and then to each coordinate, giving continuity
with values in `ℂ`.

For each `b`, left multiplication by `σ(b)` preserves `S`: this holds for a
spanning element since `σ(b)σ(a) = σ(ba)`, and extends by span induction.
Denote this linear map by `L_b`. The linear map from the dual space `S →ₗ[ℂ] ℂ`
to functions on `A` sending `f` to `a ↦ f(σ(a))` has finite-dimensional image.
Every left translate `a ↦ χᵢ(ba)` lies in that image, by taking
`f = B.coord i ∘ L_b`. Its translate span is consequently finite dimensional.
This implements the target's exact `b * a` convention.

The coordinate functions are pairwise distinct. If `χᵢ = χⱼ`, the two coordinate
linear maps agree on every `σ(a)`. These elements span `S`, so the linear maps
are equal; linear independence of the basis coordinates implies `i = j`.
Thus `X`, the finite image of the coordinate family, has no lost repeated terms.
`Function.extend` assigns `T(χᵢ) = Bᵢ` and assigns zero outside this image.
Every selected operator belongs to `S`. Reindexing the basis reconstruction
formula along the injective coordinate family proves the required equality.
The finite basis and function extension also work with an empty index type,
so the zero representation is included without a nonzero hypothesis or case
omission.

## Source provenance and scope

This is an internal derived proof combining the published intertwiner-finiteness
result, elementary linear algebra, and open stabilizers. It does not assume a
finite operator span, generalized-character decomposition, irreducibility,
scalar central action, finite-dimensionality of `V`, or topology on `V`.
Neither local compactness nor Hausdorffness of the groups is needed.

The original passages retained in the target's documentation were read:

- H. Jacquet, I. I. Piatetski-Shapiro and J. Shalika, *Automorphic Forms on
  GL(3) I*, Annals of Mathematics (2) 109 (1979), 169–212, registered source
  `jps-1979-gl3-i`, SHA-256
  `6446822f267f9f95156ce7a193409209e56ce7858ed6d3d350480e73f35b1aa5`.
  Printed p.181 / PDF p.14 defines finite functions and, in the first proof
  paragraph of Proposition 2.2, expands a smooth representation of `Fˣ` whose
  operator algebra is already finite dimensional. Retained file:
  `/home/taskhub/central-library/Jacquet-Piatetski-Shapiro-Shalika--Automorphic Forms on GL(3) I--1979.pdf`.
  Our proof supplies operator-span finiteness from admissibility and finite
  generation and works for the general `A` in the published target. It does not
  prove the paragraph's further bounded-absolute-value spanning assertion or
  Proposition 2.2's Whittaker expansion.
- W. Casselman, *Introduction to the theory of admissible representations of
  p-adic reductive groups*, draft of 1 May 1995, registered source
  `casselman-1995-admissible-representations`, SHA-256
  `78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`.
  Printed/PDF p.18 gives the definitions; p.19, Proposition 2.1.3 and its proof,
  gives center-finiteness from center-stable finite-dimensional fixed spaces.
  Retained file:
  `/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
  The source works with locally compact Hausdorff groups having a compact-open
  subgroup basis. Uniform operator-space finiteness and the broader topological
  scope here are internal deductions, not assertions attributed verbatim to
  that source's more general closed-subgroup conclusion.

No source-specific errata files for these two registered source IDs were present
in the project notes or the supplied Library when this proof was prepared.
