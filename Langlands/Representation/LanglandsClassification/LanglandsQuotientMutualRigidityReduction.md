# Langlands quotient injectivity from two-sided opposite intertwining rigidity

Worker 63, Task 5295. Module
`Langlands.Representation.LanglandsClassification.LanglandsQuotientMutualRigidityReduction`,
namespace `Langlands.Aubert.General.RepresentedParabolic`.

This module splits Renard VII.4.2 (ii) at the diagram (VII.4.2.1), in a two-sided
form. It defines the proposition
`LanglandsTripletMutualOppositeIntertwiningRigidityStatement` and proves that it
implies the published `LanglandsQuotientInjectiveStatement`, given second adjointness
and the opposite kernel part of VII.4.1. It proves neither the rigidity proposition,
nor second adjointness, nor the kernel part. So part (ii) is not proved
unconditionally here.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VII.4.2, Theorem (ii), proof printed pp.244–246 /
PDF pp.250–252. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

## The two-sided rigidity statement

`LanglandsTripletMutualOppositeIntertwiningRigidityStatement` has independent
universes `u` (field) and `v` (inducing carriers). It quantifies over:

- a nonarchimedean local field `k` (`Field`, `ValuativeRel`, topology,
  `IsNonarchimedeanLocalField`, `T2Space`);
- a connected reductive group scheme `G` over `k`, whose rational points carry the
  canonical point topology and form a locally compact nonarchimedean group;
- a torus `i : T → G` (monomorphism), a cocharacter `ν` and integral reflection
  data `D`. Langlands triplets are defined relative to these choices.
- for `j = 1, 2`, an actual parabolic `pⱼ : Pⱼ → G` with:
  - rational Levi `lⱼ : Mⱼ → Pⱼ`;
  - geometric unipotent radical `rⱼ : Uⱼ → Pⱼ`, with `subgroupMultiplication lⱼ rⱼ`
    an isomorphism;
  - split component `aⱼ : Aⱼ → Mⱼ`, index set `Jⱼ` and map `fⱼ : Aⱼ → T`;
  - a smooth representation `σⱼ` of `Mⱼ(F)` and `ψⱼ ∈ X(Mⱼ)`;
- for `j = 1, 2`, an actual parabolic `qⱼ : Qⱼ → G` with:
  - rational Levi `lQⱼ : Mⱼ → Qⱼ` and geometric unipotent radical
    `rQⱼ : Vⱼ → Qⱼ`, with isomorphic multiplication;
  - the same Levi embedding, `lQⱼ ≫ qⱼ = lⱼ ≫ pⱼ`;
  - `Pⱼ(F) ∩ Qⱼ(F) = Mⱼ(F)`, so `Qⱼ` is opposite to `Pⱼ`.

The hypotheses are:

- both `IsLanglandsTriplet` predicates;
- a nonzero intertwining map `t₁ : i_{P₁}^G(σ₁ ⊗ ψ₁) → i_{Q₂}^G(σ₂ ⊗ ψ₂)`;
- a nonzero intertwining map `t₂ : i_{P₂}^G(σ₂ ⊗ ψ₂) → i_{Q₁}^G(σ₁ ⊗ ψ₁)`.

Inductions are the published `leviInductionFunctor`, and twists the published
`SmoothRep.twist` with `Plancherel.unramifiedCharacter_isOpen_ker`, as in
`LanglandsClassificationStatement`. The conclusion is verbatim that of
`LanglandsQuotientInjectiveStatement`:

- `J₁ = J₂`;
- `‖ψ₁(m₁)‖ = ‖ψ₂(m₂)‖` whenever `m₁, m₂` have the same image in `G(F)`;
- a complex linear equivalence `φ : σ₁ ⊗ ψ₁ ≃ σ₂ ⊗ ψ₂` with
  `φ(τ₁(m₁) x) = τ₂(m₂) φ(x)` for all such pairs.

## Relation to Renard and to the one-sided statement

After the diagram (VII.4.2.1), Renard's proof uses one nonzero element of
`Hom_G(i_{P₁}(σ₁ψ₁), i_{P̄₂}(σ₂ψ₂))`. The published one-sided proposition
`LanglandsTripletOppositeIntertwiningRigidityStatement`
(`LanglandsQuotientInjectiveReduction`) records exactly that claim. The present
proposition also assumes the symmetric map `i_{P₂}(σ₂ψ₂) → i_{P̄₁}(σ₁ψ₁)`. Since
(VII.4.2.1) applies to either triplet, both maps exist in Renard's situation. The
two-sided hypothesis makes the proof of the comparison `Re ψ₁ = Re ψ₂` symmetric:
each map gives one inequality for a Weyl-invariant inner product. The one-sided
proposition implies this one, since the extra hypotheses are unused. This is a
derived intermediate claim, not a transcription of a printed statement.

## The reduction theorem

`langlandsQuotientInjective_of_mutualRigidity` takes three hypotheses:

- `hAdj : LeviSecondAdjointnessStatement`;
- `hK : LanglandsTripletOppositeKernelStatement`;
- `hR : LanglandsTripletMutualOppositeIntertwiningRigidityStatement`.

It proves `LanglandsQuotientInjectiveStatement`, at the same universes `u, v`.

Implemented proof: let `π` be a common irreducible quotient. The following is done
for each `j = 1, 2`.

1. Take `Oⱼ = oppositeLeviParabolic hG pⱼ lⱼ hpⱼ hlⱼ`.
2. Get the second-adjointness equivalence for `(Pⱼ, Oⱼ)` from `hAdj`, and
   `PQ`-regularity from `hK`.
3. Get the identity-support equivalence from the proved `oppositeIdentitySupport`.
4. The existing `exists_regularOppositeQuotientEmbedding` gives an injective
   intertwiner `jⱼ : π → i_{Oⱼ}(τⱼ)`. Twisting preserves irreducibility
   (`SmoothRep.isIrreducible_twist_iff`), so `τⱼ` is irreducible.

With `qⱼ` the quotient maps, `j₂ ∘ q₁` and `j₁ ∘ q₂` are nonzero: `π` is
nontrivial, `qⱼ` is surjective and `jⱼ` is injective. Then `hR` applies with
`Qⱼ = Oⱼ`. This is the same argument as `langlandsQuotientInjective_of_inputs`,
run for both triplets.

## Qualifications

The rigidity proposition, `LeviSecondAdjointnessStatement` and
`LanglandsTripletOppositeKernelStatement` remain unproved here. A proof of the
rigidity proposition is planned by Worker 63 for Task 5295. It will use the
geometric lemma, the tempered exponent cone, a Weyl-invariant form comparison of
dominant parameters, and the identity support piece.
