# Parabolics with a maximal Levi determined by a missed direction: proof

Worker 5004.

`Langlands.GroupScheme.maximalLeviConeComplement` proves exactly the published
proposition `Langlands.GroupScheme.MaximalLeviConeComplementStatement.{u}` of module
`Langlands.GroupScheme.Rational.MaximalLeviConeComplementStatement`. It has the same
universe `u` and no added premise. The only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.

## The statement proved

Take an arbitrary field `k : Type u` and a connected reductive group `G` over
`Spec k`. Let `p : P ⟶ G` be an actual rational parabolic with rational Levi
`l : M ⟶ P`. Assume `p` is proper (`¬ IsIso p`) and maximal: for every rational
parabolic `q' : Q' ⟶ G` and every `j : P ⟶ Q'` with `j ≫ q' = p`, either `j` or `q'`
is an isomorphism. Let `a : A ⟶ M` be a split component. Let `x : Vstar A` be nonzero
with `pair A x (1 ⊗ ν) = 0` for every cocharacter `ν` of `A` such that `ν ≫ a ≫ l ≫ p`
is central in `G`. For `i = 1, 2` take maps `qᵢ : Qᵢ ⟶ G`, `lQᵢ : M ⟶ Qᵢ` and a
geometric unipotent radical `rQᵢ : Uᵢ ⟶ Qᵢ` with `lQᵢ ≫ qᵢ = l ≫ p`, and root
presentations `presᵢ : ParabolicRootPresentation qᵢ lQᵢ a`. If `x` lies in neither
`pres₁.positiveCone` nor `pres₂.positiveCone`, then
`SubgroupFunctor.range q₁ = SubgroupFunctor.range q₂` and
`SubgroupFunctor.range (rQ₁ ≫ q₁) = SubgroupFunctor.range (rQ₂ ≫ q₂)`.

## The Lean proof

The proof is one term:

`maximalLeviConeComplementFromParabolicDynamic parabolicDynamic`.

It applies two published theorems of the Library.

- `maximalLeviConeComplementFromParabolicDynamic` (module
  `Rational.MaximalLeviConeComplementReduction`) proves the implication
  `ParabolicDynamicStatement.{u} → MaximalLeviConeComplementStatement.{u}`.
- `parabolicDynamic` (module `Absolute.ParabolicDynamicProof`) proves
  `ParabolicDynamicStatement.{u}`, Milne's Theorem 25.1 in the Library's
  formulation. Over every field `k`, a closed subgroup `i : P ⟶ G` of a connected
  reductive `G` is parabolic exactly when `SubgroupFunctor.range i` is the dynamic
  parabolic `Dynamic.parabolic χ` of some cocharacter `χ` of `G` defined over `k`.
  This proof has no premises.

Both theorems are proved at the same universe `u`, so the term has exactly the type
of the target.

## What the reduction does

The following summary describes the published reduction applied above. Its details
are in the Markdown of the modules named here.

1. *Central-kernel character* (`hasCentralKernelCharacter_of_maximal`, module
   `Rational.MaximalLeviCentralKernel`). By `ParabolicDynamicStatement`, `P` is a
   dynamic parabolic. A split-component cocharacter `ζ` of `A` presents `P` as
   `P(ζ ≫ a ≫ l ≫ p)`, and the range of `l ≫ p` as the centralizer of that
   cocharacter. Because `p` is proper, some relative root `α₀` of `a ≫ l ≫ p` has
   `⟨α₀, ζ⟩ ≠ 0`. Suppose a cocharacter `ν` with `⟨α₀, ν⟩ = 0` is not central. Then a
   proper centralizer coarsening `μ` gives a dynamic parabolic `P(μ ≫ a ≫ l ≫ p)`
   containing `P`, whose centralizer is proper and strictly contains the range of
   `l ≫ p`. `ParabolicDynamicStatement` makes it a parabolic subgroup, and `p` factors
   through it. By maximality the factor or the inclusion is an isomorphism. The first
   case forces the two centralizers to agree, and the second makes the centralizer of
   `μ` everything; both are contradictions. So every cocharacter in the kernel of `α₀`
   is central.
2. *The central annihilator is a line* (`mem_span_of_hasCentralKernelCharacter`, same
   module). The pairing on the split torus `A` is perfect. Every real character
   vanishing on the central cocharacters vanishes on the kernel of `α₀`, so these
   characters lie on one line. Since `x ≠ 0`, that line is `Submodule.span ℝ {x}`. In
   Renard's proof this is the fact that `A_M / A_G` has dimension one.
3. *Missed cones give equal parabolics* (`maximalLeviConeComplement_of_line` and
   `range_eq_of_line`, module `Rational.MaximalLeviConeComplementLine`). Every
   restricted root of a presentation lies on the line of `x`. The presentation has a
   restricted root because the range of `l ≫ p` is not all of `G`. Since `x` misses
   the positive cone, `x` is negative on the defining split-component cocharacter of
   each presentation. So the two defining cocharacters give every relative root of
   the torus of `pres₁` the same sign. The published `relativeRootSignInclusions` then
   gives equal dynamic parabolics and equal dynamic unipotent radicals. The
   presentation fields identify these with `range qᵢ` and `range (rQᵢ ≫ qᵢ)`.

## Provenance

The target is an internal statement derived from the proof of Renard,
*Représentations des groupes réductifs p-adiques* (2026 version), VII.1.3
(printed p.225, PDF p.231), as its own Markdown explains. This proof follows the
route recorded in `MaximalLeviConeComplementReduction`: the line property for a
maximal Levi comes from the dynamic description of parabolics, not from a relative
root-system classification. The proof adds no new mathematics. It closes the
reduction's only premise with the published proof `parabolicDynamic`.
