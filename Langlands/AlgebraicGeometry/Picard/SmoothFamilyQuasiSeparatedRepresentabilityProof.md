# Proof: smooth-family representability on quasi-separated tests

This module proves
`Langlands.AbelianScheme.SmoothFamilyQuasiSeparatedRepresentabilityStatement.{u}`
as the theorem
`Langlands.AbelianScheme.smoothFamilyQuasiSeparatedRepresentability`.

## Statement proved

For every scheme `S : Scheme.{u}` with `QuasiSeparatedSpace S` and every
abelian scheme `A : AbelianScheme S`, there are an object `P : Over S` and a
rigidified family `L : RigidifiedFamily A P` such that
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L` holds. That predicate is
the unchanged Library one: `L` is algebraically trivial via an actual smooth
family, and every actual smooth-family algebraically trivial class on every
quasi-separated test `T : Over S`, including nonreduced tests, is the
rigidified classifying-map pullback of `L` along exactly one morphism
`T ⟶ P`. The parameter `P` is unrestricted in the statement.

## Implemented proof

The proof is a projection of one published result:
`Langlands.AbelianScheme.smoothFamilyAbelianRepresentability :
SmoothFamilyAbelianRepresentabilityStatement.{u}`
(module `Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityProof`).
That statement gives, for the same quasi-separated base `S` and the same
abelian scheme `A`, an actual abelian scheme `B : AbelianScheme S`, an actual
rigidified family `L : RigidifiedFamily A B.X`, and a proof of
`IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`.

The Lean proof introduces `S`, its quasi-separatedness instance and `A`,
applies `smoothFamilyAbelianRepresentability` to `S` and `A`, destructures the
result as `⟨B, L, hL⟩`, and returns `⟨B.X, L, hL⟩`. So the parameter is
`P := B.X`, the underlying object of `Over S` of the abelian scheme `B`, and the
family `L` and the universality proof `hL` are used exactly as supplied. No
morphism, class, rigidification or family is transported or modified, and the
universe `u` is kept throughout.

## Provenance and scope

This is an internal logical step between two Library statements: the target
only forgets that the parameter is an abelian scheme. All mathematical
content (the construction of the representer, its universality, and the
source comparisons it requires) lives in the published shared proof
`smoothFamilyAbelianRepresentability` and the modules it imports; see that
module's Markdown for its route. No hypothesis is added: the theorem has
exactly the type `SmoothFamilyQuasiSeparatedRepresentabilityStatement.{u}`.
