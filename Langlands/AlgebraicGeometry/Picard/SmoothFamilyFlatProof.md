# Flatness of a universal smooth-family Picard parameter: proof

Authors: Worker 2037. The assembly adapts Worker 442's earlier conditional
two-input draft. It is internal derived content: it combines published Library
theorems and makes no new literature assertion.

## Result

`Langlands.AbelianScheme.smoothFamilyFlat` has exactly the type
`Langlands.AbelianScheme.SmoothFamilyFlatStatement.{u}` from
`Langlands.AlgebraicGeometry.Picard.SmoothFamilyFlatStatement`. The statement
covers every scheme `S : Scheme.{u}` with `[QuasiSeparatedSpace S]`, every abelian
scheme `A` over `S`, every `P : Over S` and every `L : RigidifiedFamily A P`.
If `L` satisfies `IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`, then
`P.hom` is flat. The theorem adds no hypothesis, and `P.left` stays
unrestricted. In particular `P.left` is never assumed quasi-separated.

## Published inputs

The proof uses three published theorems, imported by their Lean names:

- `Langlands.AbelianScheme.finiteTypeSmoothFamilyAbelianRepresentability`
  (module
  `Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityProof`)
  proves `FiniteTypeSmoothFamilyAbelianRepresentabilityStatement.{u}`. That
  statement says: every abelian scheme over `Spec R`, with `R` of finite type
  over `ℤ`, has an abelian scheme `B` over `Spec R` and a rigidified family on
  `B.X` that is universal on quasi-separated tests.
- `Langlands.AbelianScheme.smoothFamilyAbelianRepresentabilityOfFiniteType`
  (module
  `Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityOfFiniteTypeProof`)
  proves that the finite-type case implies
  `SmoothFamilyAbelianRepresentabilityStatement.{u}`: the same conclusion over
  every quasi-separated base `S`.
- `Langlands.AbelianScheme.smoothFamilyUniversalComparison` (module
  `Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalComparisonProof`)
  proves `SmoothFamilyUniversalComparisonStatement.{u}`. Take two parameters
  `P` and `Q` over `S`, with universal families `L` and `M`, and assume only
  that `P.left` is quasi-separated. Then there is a unique isomorphism
  `e : P ≅ Q` in `Over S` whose pullback of `M` is isomorphic to `L`.

## Proof

1. Fix `S`, the instance `QuasiSeparatedSpace S`, `A`, `P`, `L`, and the
   hypothesis `hL : IsUniversalSmoothFamilyOnQuasiSeparatedTests A L`.
2. Applying `smoothFamilyAbelianRepresentabilityOfFiniteType` to
   `finiteTypeSmoothFamilyAbelianRepresentability` and then to `S` and `A`
   gives an actual abelian scheme `B` over `S`, an actual
   `N : RigidifiedFamily A B.X`, and
   `hN : IsUniversalSmoothFamilyOnQuasiSeparatedTests A N`.
3. The structure morphism `B.X.hom` is proper, hence quasi-separated. Because
   `S` is quasi-separated, Mathlib's `quasiSeparatedSpace_of_quasiSeparated`
   gives `QuasiSeparatedSpace B.X.left`. This is the only quasi-separatedness
   the comparison theorem needs. Nothing is required of `P.left`.
4. `smoothFamilyUniversalComparison S A B.X P N L hN hL` gives an isomorphism
   `e : B.X ≅ P` in `Over S`. The proof keeps only `e`. Its compatibility with
   the families and its uniqueness are not needed.
5. The forgetful functor `Over.forget S` sends `e.inv` to `e.inv.left`, so
   `e.inv.left` is an isomorphism of schemes.
6. The triangle identity `Over.w e.inv` rewrites the goal `Flat P.hom` as
   `Flat (e.inv.left ≫ B.X.hom)`. Instance search then closes the goal:
   isomorphisms are flat, `B.X.hom` is smooth because `B` is an abelian scheme,
   smooth morphisms are flat, and flatness is stable under composition.

The proof passes through an actual isomorphism of the universal parameter with
a smooth abelian scheme. It does not use flatness of fibres or any
geometric-point classification.

## Checks and scope

A development `lean_check` (diagnostic `115f54c7-5d44-484c-a415-690c769f354f`)
built the module with 0 errors and 0 warnings. It reports the axioms
`propext`, `Classical.choice` and `Quot.sound` only, and the theorem type is the
constant `Langlands.AbelianScheme.SmoothFamilyFlatStatement` at universe
parameter `u`.

The proof does not use `RelativeDualSchemeFlatStatement`,
`RelativeDualSchemeGeometryStatement` or any conditional draft. It constructs no
second representer. It uses the published finite-type representer, the
published general-base reduction, and the published comparison. The final
assembly of the shared representability statement belongs to task
`e9fb02f6-3fec-4e98-84cf-fcbd2b47f407`, and this proof does not publish it. It
applies the two published theorems inline instead. Task IDs record ownership
only. They are not mathematical evidence.
