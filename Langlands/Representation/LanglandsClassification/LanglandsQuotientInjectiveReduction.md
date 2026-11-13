# Langlands quotient injectivity from opposite intertwining rigidity

Worker 63, Task 5295. This module splits Renard VII.4.2 (ii) at the diagram
(VII.4.2.1). It defines the proposition
`LanglandsTripletOppositeIntertwiningRigidityStatement` and proves that it
implies the published `LanglandsQuotientInjectiveStatement`, given second
adjointness and the opposite kernel part of VII.4.1. It does not prove the
rigidity proposition, second adjointness or the kernel part; it does not prove
part (ii) unconditionally.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VII.4.2, Theorem (ii), proof printed pp.244–246 /
PDF pp.250–252. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The rigidity statement

`LanglandsTripletOppositeIntertwiningRigidityStatement` (universes `u` of the
field and `v` of the inducing carriers, independent) quantifies over:

- a nonarchimedean local field `k` (`Field`, `ValuativeRel`, topology,
  `IsNonarchimedeanLocalField`, `T2Space`), a connected reductive group scheme
  `G` over `k` whose rational points carry the canonical point topology and are
  locally compact and a nonarchimedean group;
- a torus `i : T → G` (monomorphism), a cocharacter `ν` and integral reflection
  data `D` — the choices relative to which Langlands triplets are defined;
- a first actual parabolic `p₁ : P₁ → G` with rational Levi `l₁ : M₁ → P₁`,
  geometric unipotent radical `r₁ : U₁ → P₁` with `P₁ = M₁U₁`
  (`subgroupMultiplication` an isomorphism), split component `a₁ : A₁ → M₁`,
  simple-root index `J₁`, factor `f₁ : A₁ → T`, a smooth representation `σ₁`
  of `M₁(F)` on a carrier in universe `v` and an unramified character `ψ₁` of
  `M₁(F)`;
- a second actual parabolic `p₂ : P₂ → G` with rational Levi `l₂ : M₂ → P₂`,
  split component `a₂`, index `J₂`, factor `f₂`, representation `σ₂` and
  unramified character `ψ₂` (no unipotent radical of `P₂` is needed);
- an actual parabolic `q₂ : Q₂ → G` with rational Levi `lQ₂ : M₂ → Q₂` and
  geometric unipotent radical `rQ₂ : V₂ → Q₂`, `Q₂ = M₂V₂`, which is opposite
  to `P₂` in the published sense used throughout the Langlands classification
  modules: `lQ₂ ≫ q₂ = l₂ ≫ p₂` (the same Levi embedding into `G`) and
  `P₂(F) ∩ Q₂(F) = M₂(F)` inside `G(F)` (`pointImage` equation).

Assume both `(P₁, σ₁, ψ₁)` and `(P₂, σ₂, ψ₂)` are Langlands triplets
(`IsLanglandsTriplet`) and write `τⱼ = σⱼ ⊗ ψⱼ` (`SmoothRep.twist`). The
statement asserts: for every **nonzero** intertwining map
`t : i_{P₁}^G(τ₁) → i_{Q₂}^G(τ₂)` between the actual normalized induced
representations (`leviInductionFunctor`), the conclusion of the published
`LanglandsQuotientInjectiveStatement` holds verbatim:

1. `J₁ = J₂`;
2. `‖ψ₁(m₁)‖ = ‖ψ₂(m₂)‖` whenever `m₁ ∈ M₁(F)` and `m₂ ∈ M₂(F)` have the same
   image in `G(F)`;
3. there is a complex linear equivalence `φ : τ₁ ≃ τ₂` with
   `φ(τ₁(m₁)x) = τ₂(m₂)(φ x)` for all such pairs `(m₁, m₂)`.

### Correspondence with the source

Renard's proof of (ii) starts from the diagram (VII.4.2.1), which produces a
nonzero element of `Hom_G(i_{P₁}^G(σ₁ψ₁), i_{P̄₂}^G(σ₂ψ₂))`. Every subsequent
step (Frobenius reciprocity, the geometric lemma, second adjointness on the
Levi, the exponent bounds for tempered `σᵢ`, the uniqueness in the Langlands
combinatorial lemma V.3.18, Lemma V.3.17, the representatives of V.4.6) uses only
this nonzero morphism and the triplet hypotheses, and ends with `M₁ = M₂`,
`μ₁ = μ₂` (equal real parts) and a nonzero, hence bijective, element of
`Hom_{M₁}(σ₁ψ₁, σ₂ψ₂)` (printed pp.244–246). The rigidity statement is exactly
this assertion, with `P̄₂` replaced by any actual opposite `Q₂` in the sense
above and the conclusion phrased as in the published part (ii) statement:
equal indices for `M₁ = M₂`, equal norms on common points for
`ℜ(ψ₂ψ₁⁻¹) = 0`, and an equivalence over common Levi points for
`σ₁ψ₁ ≃ σ₂ψ₂`. Its provenance is therefore derived: an intermediate claim of the
source proof, isolated so that the purely formal first step can be proved now.

## The reduction

`langlandsQuotientInjective_of_inputs` proves
`LanglandsQuotientInjectiveStatement.{u, v}` from

- `LeviSecondAdjointnessStatement.{u, v}` (Renard VI.9.6; unproved here),
- `LanglandsTripletOppositeKernelStatement.{u, v}` (the ideal-comaximality part
  of VII.4.1; unproved here),
- `LanglandsTripletOppositeIntertwiningRigidityStatement.{u, v}` (above;
  unproved here).

The published proved theorem `oppositeIdentitySupport` supplies the remaining
identity-support input; it is not a hypothesis.

### Implemented proof

Fix the two triplets and an irreducible smooth `π` (carrier universe
`max u v`) with surjective intertwiners from both induced representations.

1. `oppositeLeviParabolic hG p₂ l₂ hp₂ hl₂` chooses actual opposite data `O`
   for `(P₂, M₂)`, with the same Levi embedding and the intersection property.
2. Second adjointness for `(P₂, O)` gives an adjunction
   `i_{P₂} ⊣ r_O` on carriers of universe `max u v`; the kernel statement gives
   `IsPQRegular` for `τ₂`; `oppositeIdentitySupport` identifies the identity
   boundary-support image with `τ₂`. `τ₂` is irreducible because `σ₂` is
   (`SmoothRep.isIrreducible_twist_iff`).
3. The published `exists_regularOppositeQuotientEmbedding` (the argument of
   VII.4.2 (i)) then gives an injective intertwiner `j : π → i_O^G(τ₂)`.
4. Let `q : i_{P₁}^G(τ₁) → π` be the surjection from the first quotient
   hypothesis. `π` is nontrivial since it is irreducible, so pick `x ≠ 0` and
   `y` with `q y = x`; then `(j ∘ q) y = j x ≠ 0` by injectivity of `j`. Hence
   `j ∘ q` is a nonzero intertwiner `i_{P₁}^G(τ₁) → i_O^G(τ₂)`.
5. The rigidity statement applied to `O` and `j ∘ q` yields exactly the
   required conclusion.

No universe is identified with another, no hypothesis is added to the published
statement, and the statement's Lean/Markdown pair and imports are unchanged.
