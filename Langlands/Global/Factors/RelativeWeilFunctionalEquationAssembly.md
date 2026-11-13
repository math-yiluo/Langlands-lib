# Assembly of the global functional equation for twisted relative Weil pairs

Author: Worker 5014 (task `cc3ec74b-6eb5-4fd8-af55-97f37ce4d76c`).

## Contents

This module derives the published target
`Langlands.Global.FunctionalEquationComparison.RelativeWeilTwistFunctionalEquationStatement.{u,uV,uE}`
(module `Langlands.Global.Factors.RelativeWeilFunctionalEquationStatement`) from one
published local class field theory statement, which it takes as an explicit hypothesis and
does not prove:

- `hN3 : ClassField.Global.RelativeWeilGroup.LocalTransferReciprocityStatement.{u}`: the
  transfer `W_{E/F} → C_F` composed with a local map `ι : W_{F_z} → W_{E/F}` is the inverse of
  geometric local reciprocity of `F_z` followed by `F_zˣ → C_F`.

Every other input is a proved Library theorem. This includes the local restriction formula
`ClassField.Global.RelativeWeilGroup.localInducedRestriction.{max u uV, u} :
LocalInducedRestrictionStatement.{max u uV, u}` (module
`Langlands.VirtualRepresentation.Global.RelativeWeilLocalRestrictionProof`) and the
geometricity of normalized common-closure reciprocity families,
`LocalClassField.commonClosureGeometricProof.{u, u} : CommonClosureGeometricStatement.{u, u}`
(module `Langlands.ClassFieldTheory.Local.CommonClosureGeometricProof`). The declarations
are:

- `Langlands.FiniteRepresentation.tensorTrivialLineEquiv A`: for a finite representation `A`
  of a group `G` in carrier universe `uV`, an isomorphism of representations
  `A ⊗ characterLine.{uG, uW} 1 ≃ A`. The left side is `A` tensored with the trivial character
  line, whose carrier is `ULift.{uW} ℂ`, so only the carrier universe changes.
- `Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine.exists_functionalEquation_of_heckeFactors`
  (hypothesis `hH : HeckeGlobalFunctionalEquationStatement.{u}`). The setting is that of the
  published `hasGlobalEquation_brauerProduct`: an integer `d`, a Hecke character `χ` of `F`,
  integers `r i`, intermediate fields `K i` of `E / F`, Hecke characters `lam i`, `lam' i` of
  `K i`, archimedean data `DF`, `DK i`, `DK' i`, self-dual measures `μ`, `μK i` and a finite
  set `B` of finite places of `F`. Off `B` the finite epsilon factors of `χ` at `z`, and of
  `lam i`, `lam' i` at the places of `K i` above `z`, are `1`. Let `f : FinitePlace F →
  LocalFactors` satisfy three conditions at every `z`. First, `(f z).lFactor s` equals
  `L(χ, z, s)^d · Π_i (Π_{u|z} L(lam i, u, s) · (Π_{u|z} L(lam' i, u, s))⁻¹)^{r i}` whenever
  all these Hecke L-factors are nonzero. Second, the same holds for `(f z).dualLFactor` with
  the inverse characters. Third, `(f z).epsilonFactor` is the corresponding product of
  `finiteEpsilon` factors for every `s`. Assume also that `(f z).epsilonFactor` is nonzero
  meromorphic for `z ∈ B`. Then for every infinite place `w₀` there are `σ`, `Lp`, `Lpd` such
  that the Euler data `assembledEulerData (lumpedArch w₀ A Ad Ae) f Lp Lpd` is `Admissible`,
  has Euler products outside `exceptionalPlaces F B` on `Re s > σ`, and satisfies
  `FunctionalEquation` there. Here `A = DF.A^d · Π_i ((DK i).A · ((DK' i).A)⁻¹)^{r i}`, and
  likewise for `Ad` and `Ae`.
- `Langlands.ClassField.Global.RelativeWeilGroup.FiniteRepresentation.isContinuous_discrete`:
  a finite representation of `RelativeWeilGroup c F E` that is continuous for the topology
  built from the Krull topology on `Gal(E/F)` is continuous for the one built from
  `relativeGaloisTopology F E`.
- `Langlands.Global.FunctionalEquationComparison.relativeWeilTwistFunctionalEquation_of_localTransferReciprocity hN3 :
  RelativeWeilTwistFunctionalEquationStatement.{u, uV, uE}`, the main theorem. Its conclusion
  is the target statement verbatim, with all three universes free.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`.

## Source and provenance

John Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979), 3–26
(registered `tate-1979-number-theoretic-background`), Theorem (3.5.3) and the paragraph after
it, printed p.16. The functional equation for a representation of a Weil group is obtained by
writing its class as an integral combination of representations induced from characters
(Brauer's theorem). The L- and epsilon factors are additive and inductive in degree 0
((2.3.1), (2.3.5)), so it is a product of Hecke functional equations. Guy Henniart, *Une preuve
simple des conjectures de Langlands pour GL(n) sur un corps p-adique*, Invent. Math. 139
(2000), §2.3 (registered `henniart-2000-simple-proof`), uses these equations for twisted pairs.

The main theorem follows that argument. It is a derived, conditional result: the local
hypothesis `hN3` is a local class field theory compatibility, and the theorem says nothing
beyond "this statement implies the target". `exists_functionalEquation_of_heckeFactors`, `isContinuous_discrete` and
`tensorTrivialLineEquiv` are internal bookkeeping. Placing the whole archimedean block at one
infinite place `w₀` is allowed because the target's archimedean block is existential.

## Proof

- `tensorTrivialLineEquiv` is `TensorProduct.congr` of the identity and `ULift.moduleEquiv`,
  followed by `TensorProduct.rid`. Intertwining is checked on pure tensors with `map_smul`.
- `exists_functionalEquation_of_heckeFactors`: `hasGlobalEquation_brauerProduct` gives a
  global package `P` with exceptional set `B`. `exists_heckeL_ne_zero`, applied to `χ`,
  `χ⁻¹`, `lam i`, `lam' i` and their inverses, gives a common half-plane `Re s > σ` on which
  every Hecke L-factor involved is nonzero. On that half-plane the hypotheses identify
  `(f z).lFactor` and `(f z).dualLFactor` with the package factors. At `z ∈ B` the products of
  Hecke L-factors are nonzero meromorphic functions (`nonzeroMeromorphic_heckeL`), and
  `meromorphicEq_of_eq_of_ne_zero` turns agreement off their zeros into a `MeromorphicEq`.
  Equality of the epsilon factors gives `meromorphicEq_of_eq`. The archimedean functions are
  nonzero meromorphic by the `nonzeroMeromorphic_A`, `_Ad`, `_Ae` fields of `HeckeArchData`
  together with `NonzeroMeromorphic.mul`, `.zpow`, `.inv` and `.finsetProd`. The lemmas
  `lumpedArch_prod_lFactor`, `_dualLFactor` and `_epsilonFactor` compute the archimedean
  products, and `lumpedArch_nonzeroMeromorphic` gives meromorphy of each archimedean factor.
  `HasGlobalEquation.toFunctionalEquation` then yields the three conclusions.
- `isContinuous_discrete` rewrites along `krullTopology_eq_relativeGaloisTopology F E`.
- `relativeWeilTwistFunctionalEquation_of_localTransferReciprocity`, with `relativeGaloisTopology` as a
  local instance (the topology of the published assembly lemmas):
  1. Inputs. `h : FundamentalClass.Restriction c` comes from `hc`.
     `localInducedRestriction.{max u uV, u}` gives
     `LocalInducedRestrictionStatement.{max u uV, u}` (the published proof of the local
     restriction formula), and `hgeo` is
     `commonClosureGeometricProof.{u, u}`. The proved `transferNormCompatibilityStatement`,
     `heckeGlobalFunctionalEquation_proof`, `inducedCharacterGeneration` and
     `transferCharacterFactorization` supply the rest.
  2. Additive data. The first conjunct of the Hecke statement for the trivial character gives
     finite components `ψf v` of `ψ` and self-dual measures `μ v`. `nonempty_selfDualHaar`
     gives measures `μK` for `traceComponents ψf` on every intermediate field.
  3. Brauer decomposition. `X = (S ⊗ S') ⊗ (trivial line)` is continuous, in carrier universe
     `max u uV`, and isomorphic to `S ⊗ S'` by `tensorTrivialLineEquiv`. Let `x` be its class.
     `exists_twist_decomposition` gives `n`, `r`, `K`, `θ`, `θ'` such that for every
     continuous character `η` of `W_{E/F}` the twist of `x` by `η` is
     `deg x · [η] + Σ_i r i · Ind_{K i}([η|·θ i] − [η|·θ' i])`. Then
     `exists_eq_continuousReciprocityCharacter` with `transferCharacterFactorization` writes
     `θ i`, `θ' i` as `continuousReciprocityCharacter` of Hecke characters `θh i`, `θh' i`.
  4. Choices before `χ`. The archimedean data `DF₀ : HeckeArchData 1 ψ` and `DK₀ i`,
     `DK₀' i` for `θh i`, `θh' i` and `traceAdditiveCharacter ψ hψ` come from
     `nonempty_heckeArchData`, and `w₀` is any infinite place. `T₀` is the union of a set off
     which `ψf` has conductor `0` (`exists_finset_additiveConductor_eq_zero`) and the places
     below the ramification sets of `θh i`, `θh' i` (`exists_finset_isUnramifiedAt`) and the
     conductor sets of `traceComponents ψf` on `K i`. The archimedean block is
     `lumpedArch w₀` of the corresponding products with exponents `d = deg x` and `r i`.
  5. For `χ`, `B`, `f`. `χ` is trivial at infinity, and so is `χ ∘ N_{K i/F}`
     (`normComp_infiniteComponent_eq_one`). So `HeckeArchData.ofInfiniteComponent_eq`
     transports `DF₀`, `DK₀ i`, `DK₀' i` to `χ`, `χ ∘ N · θh i`, `χ ∘ N · θh' i` with the same
     archimedean functions, which therefore do not depend on `χ`. Off `B` the epsilon factors
     are `1` (`finiteEpsilon_eq_one`, `normComp_isUnramifiedAt`, `isUnramifiedAt_mul`). At each
     `z`, destructuring `IsTwistedRelativePairFactorsAt` and applying
     `localFactors_eq_heckeFactors h hN2 hN3 hN4 hgeo` gives the three local identities. Its
     input `ψf z = ofCanonicalCharacter z ψz` comes from `eq_of_isFiniteAdditiveComponent`. At
     `z ∈ B` the epsilon factor is an epsilon monomial `c q^(-ms)`, nonzero meromorphic by
     `nonzeroMeromorphic_epsilonMonomial`. `exists_functionalEquation_of_heckeFactors`
     concludes.
