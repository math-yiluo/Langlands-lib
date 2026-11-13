# Conditional reduction of Renard VI.10.4, Theorem, first sentence

Worker 98. This is a conditional reduction for statement 1 of Task 5545. The source is Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026 (`renard-2026-representations-groupes-reductifs-padiques`,
SHA-256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`),
VI.10.4, Theorem, first sentence, with Remark 1 (printed pp.211–212 /
PDF pp.217–218).

The module proves the closed proposition
`BernsteinBlockCenterFunctionsReductionStatement`. It says that the published
`BernsteinBlockCenterFunctionsStatement` (module
`BernsteinCenterFunctionsStatements`) follows from four published or staged
propositions:

1. **P1** `BernsteinBlockHomEquivalenceStatement` (Renard VI.10.2, Theorem,
   printed p.208 / PDF p.214). `Π_Ω = i_P^G Π_D` lies in the block `M(G)_Ω`,
   and `Hom(Π_Ω, •)` is an equivalence from the block to modules over
   `(End Π_Ω)ᵐᵒᵖ`.
2. **P2** `RepresentedParabolic.InducedProgeneratorCenterInclusionStatement`,
   at carriers in `Type (max uF uV)` (Renard VI.10.4, second Lemma and the
   centralizer identity `ℨ_Ω = 𝒞_{ℨ_D}(R_Ω)` after it, printed p.211 /
   PDF p.217, in the represented-parabolic framework). Every central
   endomorphism of `i_P^G Π_D` is `i_P^G ζ` for some `ζ` in the centre `ℨ_D`
   of `End_M Π_D`.
3. **P4** `BernsteinAssociatedSupportInvarianceStatement i ν family` for every
   standard family (Renard VI.5.4). Associated cuspidal data have the same
   irreducible subquotients of their inductions. It is quantified exactly as in
   the published `BernsteinCenterFunctionsReductionStatement`.
4. **P5** `BernsteinInvariantCenterInclusionStatement`, the inclusion
   `ℨ_D^{W(D)} ⊂ ℨ_Ω` from Renard's proof of VI.10.4 (module
   `BernsteinBlockCenterFunctionsInvariantCenter`).

The conclusion is the published statement itself, unchanged.

## Lean statement

```
def BernsteinBlockCenterFunctionsReductionStatement : Prop :=
  BernsteinBlockHomEquivalenceStatement.{uF, uV} →
    RepresentedParabolic.InducedProgeneratorCenterInclusionStatement.{uF, max uF uV} →
    (∀ F … G … T i ν, letI … pointTopology, ∀ [LocallyCompactSpace …]
        [NonarchimedeanGroup …] (family : BernsteinStandardFamily i ν),
        BernsteinAssociatedSupportInvarianceStatement.{uF, uV} i ν family) →
    BernsteinInvariantCenterInclusionStatement.{uF, uV} →
    BernsteinBlockCenterFunctionsStatement.{uF, uV}
```

The binder block of the third hypothesis is copied verbatim from the published
`BernsteinCenterFunctionsReductionStatement`.

## Provenance

This is a derived statement: it is Renard's proof of VI.10.4 (first sentence and
Remark 1), with the cited inputs as hypotheses. Renard's proof goes as follows.

- `ℨ(M(G)_Ω)` is the centre of `End Π_Ω` (Morita, VI.10.2, Theorem).
- That centre is `ℨ_Ω = 𝒞_{ℨ_D}(R_Ω)` (VI.10.4, second Lemma and the
  sentence after it; this is P2), which equals `ℨ_D^{W(D)}` (P5 gives the
  inclusion `ℨ_D^{W(D)} ⊂ ℨ_Ω`).
- By VI.4.4, `ℨ_D` is the algebra of polynomial functions on
  `Irr(M)_D = X(M)/Stab`.
- So `ℨ_Ω` is the algebra of `W(D)`-invariant polynomial functions.

In the Lean statement, "`W(D)`-invariant" means "constant on association
classes of the twists `ρ ⊗ ω`", exactly as in the published statement. VI.4.4
at `M_a` is not a hypothesis. It is the proved
`bernsteinLeviCenterVarietyStatement_holds` (module
`BernsteinBlockCenterFunctionsLevi`).

## Proof (as implemented)

Fix the data and an actual cuspidal datum `a = (M, ρ)`. Write `X = X(M)`, and
write `ind ω` for the literal normalized induction of `ρ ⊗ ω`.
`bernsteinBlockCenterFunctions_of_inputs` proves the conclusion at `a`. The
closed theorem `bernsteinBlockCenterFunctions_reduction` only introduces the
binders and applies it.

1. **Block membership.** Each `ind ω` lies in the block: this is the published
   `twistInduction_mem_saturatedBlock`.
2. **Choosing `ρ₀`, `Π_D` and the Morita data.**
   `bernsteinCuspidalDatum_exists_normKernelConstituent` gives an irreducible
   `ρ₀ ⊂ ρ|_{⁰M}`. P1 gives `hmem`, saying that `Π_Ω` is in the block, and the
   equivalence `hEq`. The Levi theorem gives the injective
   `Ψ : Subalgebra.center ℂ (End Π_D) →ₐ (X → ℂ)`. Its range is the
   `Stab`-invariant part of `unramifiedRegularFunctions`, and `ζ ≫ φ = Ψ ζ ω • φ`.
3. **From `z` to `ζ_z`.**
   - For a central `z` of the block, `catCenter_conj_mem_center` shows that the
     conjugate of `z_{Π_Ω}` by the represented iso
     `bernsteinStandardRepresentedInductionIso` (`I(Π_D) ≅ Π_Ω`) is central in
     `End I(Π_D)`.
   - P2 (through `bernsteinInducedCenter_exists`) writes this conjugate as
     `I(ζ_z)` with `ζ_z ∈ ℨ_D`. Here `I` is
     `bernsteinStandardRepresentedInductionFunctor`.
   - `choose` fixes `ζ_z` for each `z`.
4. **Scalars (key transfer).** `twistInduction_centerScalar_of_generator` shows
   that `z` acts on `ind ω` by `Ψ ζ_z ω`.
   - Take a surjection `φ : Π_D → ρ ⊗ ω`
     (`bernsteinCuspidalDatum_exists_surjective_twist`).
   - Then `g = iso⁻¹ ≫ I(φ) ≫ iso_ω : Π_Ω → ind ω` is surjective. This uses the
     exactness of `i_P^G` (`leviParabolicFunctorsExact`, through
     `bernsteinStandardRepresentedInduction_map_surjective`).
   - Naturality of `z` along `g`, together with `ζ_z ≫ φ = Ψ ζ_z ω • φ` and the
     `ℂ`-linearity of `I` (`bernsteinStandardRepresentedInduction_map_smul`),
     gives `g ≫ z = Ψ ζ_z ω • g`.
   - Since `g` is surjective, `z` acts by that scalar on all of `ind ω`.
   - The scalar is unique because `ind ω ≠ 0`
     (`twistInduction_centerScalar_unique`, using the published
     `nontrivial_twistInduction`).
5. **The ring homomorphism.** `e z := fun ω => Ψ ζ_z ω`. By uniqueness of
   scalars, `e` is multiplicative and additive, using
   `(z * w).app = w.app ≫ z.app` and `app_add`. It also sends `1` to `1`.
6. **The subalgebra `O`.** `O` is the subalgebra whose carrier is the published
   set `invariant`: regular functions that are constant on association classes.
   `e z ∈ O` for two reasons.
   - It lies in the range of `Ψ`, so it is regular.
   - Associated `ω, ω'` have a common irreducible subquotient `τ` of `ind ω`
     and `ind ω'`. This is P4, through the published
     `exists_common_irreducible_subquotient`. The block is closed under
     subquotients, so `z` acts on `τ` by both scalars, and they agree
     (`twistInduction_centerScalar_eq_of_associated`).
7. **Injectivity.** Suppose `e z = e w`.
   - Then `Ψ ζ_z = Ψ ζ_w`, so `ζ_z = ζ_w` because `Ψ` is injective.
   - Hence `z_{Π_Ω} = w_{Π_Ω}`, and `z = w` by
     `Renard.generatorCenterEvaluation_injective`, which applies because
     `Hom(Π_Ω, •)` is faithful (P1).
8. **Surjectivity.** Let `f ∈ O`.
   - **`f` is `Stab`-invariant.** For `s ∈ Stab`, the twists `ρ ⊗ χs` and
     `ρ ⊗ χ` are associated by the identity conjugacy
     (`twist_mul_stabilizer_associated`). Hence `f = Ψ ζ₀` for some `ζ₀ ∈ ℨ_D`.
   - **P5 applies.** `ζ₀` satisfies the hypothesis of P5. If `ζ₀` acts by `c` on
     every map `Π_D → ρ ⊗ ω`, then `c = Ψ ζ₀ ω`: compare on a surjection onto
     the nonzero `ρ ⊗ ω` (`smul_eq_of_surjective`). Then `Ψ ζ₀ ω = Ψ ζ₀ ω'` for
     associated `ω, ω'`, because `f ∈ O`.
   - **A preimage.** So `I(ζ₀)` is central. Its conjugate is central in
     `End Π_Ω` inside the block. Since `Hom(Π_Ω, •)` is full and faithful (P1),
     `Renard.generatorCenterEvaluation_surjective` gives a `z` with that
     component (`catCenter_exists_of_inducedCenter`).
   - **Conclusion.** By the key transfer and uniqueness of scalars, `e z = f`.
9. Finally `e` is `RingEquiv.ofBijective` of the corestriction of the ring
   homomorphism to `O`. The scalar property holds by step 4.

## Auxiliary results in the module

- `conj_comm_of_comm`, `smoothRep_iso_hom_surjective` and
  `smul_eq_of_surjective` are generic helpers.
- `bernsteinStandardRepresentedInduction_map_surjective` and
  `bernsteinStandardRepresentedInduction_map_smul` say that `I` preserves
  surjections and is `ℂ`-linear on morphisms.
- `twist_mul_stabilizer_associated` handles the `Stab`-invariance step.
- `twistInduction_centerScalar_of_generator`,
  `twistInduction_centerScalar_unique` and
  `twistInduction_centerScalar_eq_of_associated` give the scalar of a central
  element on `ind ω`: its value, its uniqueness, and its invariance under
  association.
- `bernsteinInducedCenter_exists`, `catCenter_conj_mem_center` and
  `catCenter_exists_of_inducedCenter` are the Morita transfer between the block
  and `End I(Π_D)`.

## Scope

The four inputs P1, P2, P4 and P5 are hypotheses, and none of them is proved
here. No published statement is modified. The module needs two accepted
modules that are not yet in the Library: `BernsteinBlockCenterFunctionsLevi`
and `BernsteinBlockCenterFunctionsInvariantCenter`. Their pairs are listed in
`repository_paths`.
