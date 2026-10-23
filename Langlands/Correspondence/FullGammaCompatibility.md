# Derived gamma compatibility of full families

Author: Worker 7. This module defines the pair gamma factor of irreducible
admissible classes of `GL_n(F)`, nongeneric ones included, through the pair L-
and epsilon relations of the full family. It states the gamma compatibility of
a full map. It also states, as a proposition only, that gamma compatibility
follows from the L, epsilon and dual conditions. Nothing is proved. No map,
additive character, measure or local-constant system is chosen.

## Definitions

`F : PadicField p` carries its canonical topological data, `q` is its residue
cardinality, and factors are rational functions of `X = q^(-s)`.
`LocalFactor.residueReflection F` is the unit `q⁻¹` of
`LocalFactor/ResidueReflection`;
`X ↦ q⁻¹/X` is `s ↦ 1 - s`.

`IsAutomorphicPairGammaFactor F ψ ν π π' G`, for automorphic classes `π` of
rank `r + 1` and `π'` of rank `t + 1`, says `γ(s, π × π', ψ) = G(q^(-s))`.
Precisely, there are classes `π^∨`, `π'^∨`, polynomials `P`, `P^∨` and
`e = (c, m) : ℂˣ × ℤ` such that:

- `IsSmoothDual F π π^∨` and `IsSmoothDual F π' π'^∨` (`AutomorphicRelations`):
  `π^∨` and `π'^∨` are the classes of the smooth contragredients;
- `IsAutomorphicPairLPolynomial F ψ ν π π' P` and
  `IsAutomorphicPairLPolynomial F ψ ν π^∨ π'^∨ P^∨`
  (`FullLFactorCompatibility`): `L(s, π × π') = 1/P(q^(-s))` and
  `L(s, π^∨ × π'^∨) = 1/P^∨(q^(-s))`;
- `IsAutomorphicPairEpsilonFactor F ψ ν π π' e` (`FullFactorCompatibility`):
  `ε(s, π × π', ψ) = c q^(-ms)`; and
- `G = RankinSelberg.rationalGammaExpression (residueReflection F) c m P P^∨`,
  that is, `G(X) = c X^m P(X) / P^∨(q⁻¹/X)`.

So `G(q^(-s)) = ε(s, π × π', ψ) L(1 - s, π^∨ × π'^∨) / L(s, π × π')`.

## Conditions

- `FullPairGammaCompatibility F eC ε hε c`, for a full map `c` and a
  local-constant system `ε` for the reciprocity family `eC` with
  `hε : IsSystem F eC ε`: for every nontrivial unitary additive character `ψ`,
  all `r t : ℕ`, and all parameter classes `D` of rank `r + 1` and `D'` of
  rank `t + 1`:
  1. a measure `ν` self-dual for `ψ` exists; and
  2. for every such `ν`, some `G : RatFunc ℂ` satisfies both
     `IsAutomorphicPairGammaFactor F ψ ν (c D) (c D') G` and
     `IsArithmeticPairGammaFactor F eC ε hε ψ (parameterForget F D)
     (parameterForget F D') G`.

  The arithmetic side is the published `IsArithmeticPairGammaFactor` of
  `SupercuspidalGammaCompatibility`:
  `G = c X^m · L((X ⊗ Y)^∨)(q⁻¹/X) / L(X ⊗ Y)(X)` for the arithmetic epsilon
  factor `c q^(-ms)` of the tensor product. It applies to Weil–Deligne pair
  classes with any monodromy; the dual has monodromy `-Nᵀ`.
- `FullGammaCompatibility F e c`, for a rank-one reciprocity candidate `e`:
  some system `(eC, ε, hε)` with `IsBaseReciprocity F e eC` satisfies
  `FullPairGammaCompatibility F eC ε hε c`.
- `FullGammaFromFactorsStatement F` says: for every reciprocity family `eC`,
  system `ε` with `hε : IsSystem F eC ε`, and full map `c`, if
  `FullPairLCompatibility F c`, `FullPairEpsilonCompatibility F eC ε hε c` and
  `DualCompatibility F c` hold, then `FullPairGammaCompatibility F eC ε hε c`
  holds, for the same system and the same map. It is a statement, not a
  theorem; its proof is a separate obligation.

## Sources and provenance

- Henniart 2002, §1.2, printed p.589 (PDF p.3):
  `γ(s, σ, ψ) = ε(s, σ, ψ) L(1 - s, σ^∨) / L(s, σ)`, "et de même pour
  `π × π'`". Both definitions of `IsAutomorphicPairGammaFactor` and
  `IsArithmeticPairGammaFactor` are this formula.
- Henniart 2002, §2.8, printed p.596 (PDF p.10): for `π = Σ π_i`,
  `π' = Σ π'_j` in `N[A_2] - {0}`, `π^∨ = Σ π_i^∨` and the L, gamma and
  epsilon factors of `π × π'` are the products over all pairs `(i, j)`.
  §2.9, printed p.596: the full bijection satisfies
  `γ(s, π(σ) × π(σ'), ψ) = γ(s, σ ⊗ σ', ψ)` for `σ, σ' ∈ G`, besides the L
  and epsilon identities.
- Henniart 2000, §1.2, remark after property 4), printed p.440 (PDF p.2): the
  gamma identity follows from the L and epsilon identities ("une identité
  évidente (4γ)"). `FullGammaFromFactorsStatement` is this remark for the
  full family.

Source files:

- `henniart-2002-characterization`, SHA-256
  `40c0ed7c7bfb05f1415fd66642d0b1984052f0af7cb5f3061b328216e2d24306`.
- `henniart-2000-simple-proof`, SHA-256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.

## Interpretation

- **Derived, not a substitute.** Gamma compatibility is weaker than the
  separate L and epsilon conditions and is not part of the full specification
  (`FullSpecification`). It is stated only as a consequence.
- **Gamma through L and ε.** For nongeneric representations the gamma
  factor is defined here from the L and epsilon relations, as in Henniart
  2002, §1.2. It is not the JPSS functional-equation gamma of generic
  representations, which needs Whittaker models. For generic classes the two
  agree by the JPSS functional equation; that is not proved in the Library.
- **Duals.** The dual classes `π^∨`, `π'^∨` are existential, with
  `IsSmoothDual`. Under dual compatibility they are the images of the dual
  parameters, which the intended proof of `FullGammaFromFactorsStatement` uses
  together with the L condition at `(D^∨, D'^∨)`.
- **Totality.** The witness `G` is asserted to exist, so the condition implies
  that the L-polynomials of the image pairs and of their duals, and the
  epsilon factor of the image pair, exist.
- **Measures and characters.** As in `FullFactorCompatibility`, a self-dual
  measure is asserted to exist, the identity is required for every self-dual
  measure, and the condition is required for every nontrivial `ψ` with one
  map `c`.

## Scope

- The module imports, and does not copy: this task's `FullFactorCompatibility`
  (`IsAutomorphicPairEpsilonFactor`, `FullPairEpsilonCompatibility`),
  `FullLFactorCompatibility` (`IsAutomorphicPairLPolynomial`,
  `FullPairLCompatibility`), `SupercuspidalGammaCompatibility`
  (`IsArithmeticPairGammaFactor`), `LocalFactor/ResidueReflection`
  (`residueReflection`),
  `OperationCompatibility` (`DualCompatibility`) and `AutomorphicRelations`
  (`IsSmoothDual`), and the published `RankinSelberg/PairFactors`
  (`rationalGammaExpression`).

## Validation

The module compiles in the project Lean service with no errors or warnings.
There is no `sorry` and no new axiom. Every definition returns `Prop`.
