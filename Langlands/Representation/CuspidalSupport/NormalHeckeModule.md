# The action of End(ind_H^G ρ) on Hom(ind_H^G ρ, B)

Author: Worker 1826.

This is a supporting module for the proofs of Renard VI.4.4 (the Theorem
`RationalSummandEndCenterStatement`, the Corollary
`RationalSummandEndNoetherianStatement` and the Proposition
`RationalSummandCenterGroupAlgebraStatement`). It continues the modules
`Langlands.Algebra.RankOneGradedAlgebra`,
`Langlands.Representation.CuspidalSupport.NormalHeckeGrading` and
`Langlands.Representation.CuspidalSupport.NormalHeckeTwist`. Source: David Renard,
*Représentations des groupes réductifs p-adiques* (registered source
`renard-2026-representations-groupes-reductifs-padiques`), VI.4.4, printed
pp.155–159 / PDF pp.161–165. There End(ind ρ) acts on Hom(ind ρ, π), and the twists
π ⊗ ω by unramified characters are compared with π through this action. All
declarations are internal helpers; none of them is a statement of the book.

## Commutation scalars in a rank-one graded algebra

Namespace `Langlands.RankOneGraded.IsRankOneGrading`. Let R be a k-algebra (k a field)
with a grading 𝒜 by an additive commutative group ι, and `h𝒜 : IsRankOneGrading 𝒜`
(the published notion of `Langlands.Algebra.RankOneGradedAlgebra`: every piece has
rank at most one and nonzero homogeneous elements are units).

- `exists_commutation_hom h𝒜 hv hv0`: if v ∈ 𝒜_j is nonzero, there is an additive
  homomorphism β from the support subgroup `h𝒜.support` to `Additive kˣ` such that
  x v = β(a) (v x) for every a in the support and every x ∈ 𝒜_a.
  Proof: for a in the support, pick a nonzero x₀ ∈ 𝒜_a. Then v x₀ and x₀ v both lie in
  the line 𝒜_{a+j}, and v x₀ ≠ 0 (`mul_ne_zero`), so x₀ v = c (v x₀) with c ≠ 0
  (`exists_smul_eq`). Every other x ∈ 𝒜_a is a multiple of x₀, so the same scalar
  works for all of 𝒜_a. Multiplicativity in a: compare (x y) v for x ∈ 𝒜_a, y ∈ 𝒜_b
  nonzero, using v (x y) ≠ 0.

## Characters with values in ℂˣ

Namespace `Langlands.CuspidalSupport.NormalHecke`.

- `baer_additive_units`: `Additive ℂˣ` satisfies Baer's criterion over ℤ. It is
  divisible: an n-th root of z is exp(log(z)/n). Mathlib's `Module.Baer.of_divisible`
  then applies.
- `exists_addMonoidHom_extend S β`: every additive homomorphism β from a subgroup S of
  an additive commutative group ι to `Additive ℂˣ` extends to ι (Baer's criterion).
- `addCircleToUnits` (**definition**, internal): the homomorphism ℚ/ℤ → ℂˣ,
  q ↦ exp(2π i q). `addCircleToUnits_ne_zero`: it is injective, i.e. it sends nonzero
  classes to nonzero elements of `Additive ℂˣ`, since exp(2π i q) = 1 forces q ∈ ℤ.
- `exists_addMonoidHom_ne_zero S hi`: if i ∉ S, there is χ : ι → `Additive ℂˣ`
  vanishing on S with χ(i) ≠ 0. A ℚ/ℤ-valued character of ι/S that is nonzero at the
  class of i exists by Mathlib's `CharacterModule.exists_character_apply_ne_zero_of_ne_zero`;
  compose it with `addCircleToUnits`.

## The action

G is a topological group, H a subgroup with `hH : IsOpen H`, ρ a smooth complex
representation of H, and I = `inducedRep H ρ` = ind_H^G ρ (published). B is a smooth
representation of G in the carrier universe of I.

- `homAction H ρ B` (**definition**, internal): the ℂ-linear map
  End(I) → End_ℂ(Hom(I, B)) sending α to φ ↦ α ≫ φ ("first α, then φ"; Mathlib's
  `Linear.leftComp`). `homAction_apply` (by `rfl`), `homAction_one`.
- `homAction_mul`: homAction(α β) = homAction(β) ∘ homAction(α). Products in
  End(I) are α β = β ≫ α (Mathlib's `End.mul_def`), so the action is
  anti-multiplicative; `isMulOrAntiMul_homAction` records this in the form
  `IsMulOrAntiMul` of `Langlands.Algebra.RankOneGradedAlgebra`.
- `surjective_homAction` (**Burnside**): suppose Hom(I, B) is finite-dimensional and
  nonzero, and every nonzero φ generates it, i.e. for every ψ there is α with
  α ≫ φ = ψ. Then every ℂ-linear endomorphism of Hom(I, B) is homAction(α) for some
  α. Proof: Hom(I, B) is a module over End(I)ᵐᵒᵖ (op α acting by φ ↦ α ≫ φ), which is
  simple by the generation hypothesis (Mathlib's
  `isSimpleModule_iff_toSpanSingleton_surjective`). Burnside's theorem
  `exists_forall_eq_smul_of_isSimpleModule` of `Langlands.Algebra.RankOneGradedAlgebra`
  applies since ℂ is algebraically closed.

## Equivariant bijections and twists

Let p : G → ι be a degree for H in the sense of the published `IsDegree` (ι an
additive commutative group), ω : G → ℂˣ a character with open kernel and
`hωH : H ≤ ker ω`, and Φ = `twistHomEquiv ρ hH ω hω hωH B` the published bijection
Hom(I, B ⊗ ω) ≃ Hom(I, B) of `NormalHeckeTwist`. Its twist law
(`twistHomEquiv_comp`) is Φ(α ≫ φ) = ω(g)⁻¹ (α ≫ Φ(φ)) for α in the published
`component H ρ hH p (p g)`.

- `eq_zero_of_mem_component`: an element of `component H ρ hH p a` is zero when no g
  has p(g) = a. Its values at every g vanish by definition of the component, and
  maps out of I are determined by these values (published `end_ext`).
- `twistModuleEquiv ρ hH ω hω hωH B v` (**definition**, internal): for a unit v of
  End(I), the linear bijection Hom(I, B ⊗ ω) ≃ Hom(I, B), φ ↦ v ≫ Φ(φ), with inverse
  ψ ↦ Φ⁻¹(v⁻¹ ≫ ψ). `twistModuleEquiv_apply` (by `rfl`).
- `eq_one_of_homEquiv`: let Ψ : Hom(I, B ⊗ ω) ≃ Hom(I, B) be a linear bijection with
  Ψ(α ≫ φ) = α ≫ Ψ(φ) for all α. Suppose Hom(I, B) ≠ 0, and some u in
  `component H ρ hH p (p g)` satisfies u ≫ φ = φ for every φ : I → B. Then ω(g) = 1.
  Proof: take ψ ≠ 0 and φ = Ψ⁻¹(ψ). Then u ≫ φ = φ by equivariance and injectivity of
  Ψ. The twist law gives Φ(φ) = ω(g)⁻¹ Φ(φ) with Φ(φ) ≠ 0.
- `twistModuleEquiv_comp`: assume H is normal and ρ irreducible (the hypotheses of
  the published grading `iSup_component`). Let v be a unit with
  α v = ω(g) (v α) for every g and every α in `component H ρ hH p (p g)`. Then
  `twistModuleEquiv` is equivariant: v ≫ Φ(α ≫ φ) = α ≫ (v ≫ Φ(φ)) for every α
  and φ. Proof: the α satisfying this form a subspace. It contains every component
  of degree p(g), by the twist law and the commutation relation, which together give
  ω(g)⁻¹ ω(g) = 1. It also contains every component of a degree not of the form p(g),
  since such a component is zero. The components span End(I) (`iSup_component`).

## Relation to the source

Renard compares Hom(ind ρ, π ⊗ ω) and Hom(ind ρ, π) as modules over End(ind ρ) and
uses that the operators of the homogeneous pieces act through commutation scalars.
`twistModuleEquiv_comp` makes this comparison explicit: conjugating by a unit v whose
commutation scalars are the values of ω gives an equivariant bijection.
`eq_one_of_homEquiv` is the converse direction. The character lemmas supply the
characters ω that these comparisons need.
