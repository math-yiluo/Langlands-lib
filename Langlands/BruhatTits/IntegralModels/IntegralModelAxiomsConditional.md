# KP Axioms 4.1.20 and 4.1.22 on supplied data from the unramified statements

This module derives `IntegralModelAxiomsStatement` on supplied data satisfying
the corrected Section 4.2 axioms. It assembles the unramified construction of
models and their reductive quotients for Axioms 4.1.20 and 4.1.22 of
Kaletha–Prasad (KP), *Bruhat–Tits Theory: A New Approach* (2023), printed
pp. 163–164 / PDF pp. 194–195.

## Declarations

`integralModelAxiomsStatement_of_unramified` takes the fourteen statements
in the table and proves `IntegralModelAxiomsStatement.{u}`. Here `K` is the
maximal unramified extension `inertiaFixedField F`. The pages paired with the
statement modules give their source correspondence.

| Hypothesis | Statement | Source | Discharger in `integralModelAxiomsStatement_of_unramified_remaining` |
| --- | --- | --- | --- |
| `hapt` | `UnramifiedApartmentDescentStatement` | KP §§9.2–9.3, 9.6.6, 9.9.2 | Argument |
| `hpar` | `UnramifiedParahoricModelStatement` | KP Theorems 8.3.2 and 8.3.13 over `K` | `unramifiedParahoricModel` |
| `hdesc` | `UnramifiedSmoothModelDescentStatement` | KP Fact 2.10.16 | `unramifiedSmoothModelDescent` |
| `hzero` | `UnramifiedZeroDescentStatement` | KP Proposition 9.3.24 for the zero-subgroup intersection, with derived Galois-stability clauses | Argument |
| `hext` | `UnramifiedSmoothHomExtensionStatement` | KP Corollary 2.10.10 | `unramifiedSmoothHomExtension` |
| `hclos` | `UnramifiedOneFixerClosureStatement` | KP 7.4.4(3), §7.7, 7.7.5(1) | `unramifiedOneFixerClosure` |
| `hroot` | `UnramifiedZeroFixerAffineRootStatement` | KP 7.4.1, 7.4.4(3), 7.7.5(1) | `unramifiedZeroFixerAffineRoot` |
| `htor` | `UnramifiedTorusClauseStatement` | KP §9.2.5, 8.3.14(1) | `unramifiedTorusClause` |
| `hker` | `UnramifiedModelKernelStatement` | KP Proposition 8.4.15 over `K` | `unramifiedModelKernel` |
| `hS1` | `UnramifiedFacetParabolicImageStatement` | KP 8.4.19(2)–(3), 9.3.3 | Parabolic-image reduction below |
| `hS2` | `UnramifiedFacetParabolicOrderStatement` | KP 4.1.22(5), 9.3.2, 2.4.5 | `unramifiedFacetParabolicOrder` |
| `hS3` | `UnramifiedFacetCommonTorusStatement` | KP 4.1.22(3) | `unramifiedFacetCommonTorus` |
| `hS4` | `UnramifiedFacetRootDatumStatement` | KP 4.1.22(6), 9.4.23 | `unramifiedFacetRootDatum` |
| `hS5` | `UnramifiedFacetPositiveRadicalStatement` | KP 4.1.22(7) | `unramifiedFacetPositiveRadical` |

`integralModelAxiomsStatement_of_unramified_remaining` takes `hapt` and
`hzero` and applies the fourteen-input theorem with the dischargers in the
table. For `hS1` it applies the Library theorem
`unramifiedFacetParabolicImage_of_generation_positive_modelKernel` to
`unramifiedUpstairsRadicalRootGeneration`, `unramifiedFacetPositiveRadical`
and `unramifiedModelKernel`. The resulting statement gives both the
special-fibre parabolic image and the reduction preimage on integral points.

## Proof

Fix `F`, `G`, `P`, `R`, `T` and the seven predicates `h1`–`h7` of the target.

1. `hapt`, applied to `G` (connected reductive, `P.isConnectedReductive`) and
   the valuation building data of `P`, gives `C`, `A`, `e`, `a` with its eight
   conclusions. The statement installs the instance
   `IsAffineHom G.X.hom` from `hG.isAffineHom` with `letI`. Instances of a
   proposition are equal by proof irrelevance, so it agrees with the instance
   of the target.
2. `BuildingModelFamily.exists_satisfiesModelAxioms_of_unramified` (module
   `ModelAxiomsUnramified`) uses six of these conclusions together with `hpar`,
   `hdesc`, `hzero`, `hext`, `hclos`, `hroot` and `htor`. It gives a family `M`
   with `M.SatisfiesModelAxioms P` (Axiom 4.1.20). The unramified base change of
   every neutral model `(M.model Ω).neutral` has integral points
   `E.zeroPoints ⊓ C.pointwiseFixer (e '' Ω)`, where
   `E = unramifiedZeroDatumOfParahoric P`.
3. `BuildingModelFamily.exists_satisfiesMorphismAxioms_of_unramified` (module
   `MorphismAxiomsUnramified`) uses all eight conclusions, the zero
   datum `E`, the integral points from step 2 and the torus clause
   `hM.torus_clause`, with `hker` and `hS1`–`hS5`. It gives quotient data `Q`
   and relative root reflection data `ρ` with `Q.SatisfiesMorphismAxioms ρ`
   (Axiom 4.1.22).
4. `⟨M, Q, ρ, hM, hQ⟩` proves the target.

The first theorem has `set_option maxHeartbeats 4000000`: with the default
budget, elaborating the fourteen statement binders and the two applications
makes `whnf` time out. Both theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The reduction is derived from KP's construction of the models over the
maximal unramified extension (Chapters 7 and 8), descent of the models
(§9.2.5), and verification of the axioms (§9.5).
