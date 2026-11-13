# Finite generation of the induced Bernstein progenerator (Renard VI.10.1)

Author: Worker 5225. Derived supporting result for Task 5225.

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, VI.10.1, introduces the candidate
`Π_Ω = i_P^G(Π_D)` (printed p.207 / PDF p.213), and its Théorème (printed
p.208 / PDF p.214) proves that `Π_Ω` is a finitely generated progenerator of
the block `M(G)_Ω`. For finite generation the proof says only that VI.7.5 shows
`i_P^G` preserves finitely generated representations, so `Π_Ω` is finitely
generated. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

This module proves that conjunct. The VI.7.5 Theorem stays an explicit
premise. That `Π_D` is finitely generated is taken from the published,
premise-free Library theorem
`Langlands.CuspidalSupport.finite_rationalNormKernelSummandInduction`
(`RationalSummandSmallProgeneratorReduction`). Renard takes this fact from
VI.4.1, where `Π_D` is a finitely generated progenerator.

## Declarations

- `moduleFinite_of_smoothRepIso`: if `A ≅ B` in `SmoothRep ℂ H` and `A` is
  finitely generated over `MonoidAlgebra ℂ H`, then so is `B`. The proof
  uses Mathlib's `Module.Finite.of_surjective` on the group-algebra-linear
  map from `e.hom`. That map is surjective because an isomorphism is an
  epimorphism and `SmoothRep.epi_iff_surjective` applies.

- `finite_bernsteinStandardInduction_of_leviInductionFiniteType`: assume
  `RepresentedParabolic.LeviInductionFiniteTypeStatement.{uF, max uF uV}`
  (VI.7.5). Then for each standard rational Levi
  `bernsteinLeviScheme i ν I` and each finitely generated `ρ`, the literal
  standard normalized induction
  `(normalizedInductionFunctor (family.decomposition I) (family.closedUnipotent I)).obj
  (bernsteinLiteralLeviRep i ν I ρ)` is finitely generated over
  `ℂ[G(F)]`. The proof instantiates the premise at the standard parabolic,
  Levi and unipotent radical
  (`Standard.parabolicHom`, `Standard.leviToParabolic`,
  `Standard.unipotentToParabolic`). The geometric hypotheses come from
  `bernsteinStandardRepresentativesGeometric i ν family I`, and connected
  reductivity comes from `family.connectedReductive`. The resulting
  finiteness for the represented induction is moved to the literal standard
  induction along the published isomorphism
  `bernsteinStandardRepresentedInductionIso i ν family I ρ`, using
  `moduleFinite_of_smoothRepIso`.

- `bernsteinInducedProgenerator i ν family a ρ₀` (definition): Renard's
  `Π_Ω = i_P^G(Π_D)` for a Bernstein cuspidal datum `a` of the standard
  family and a smooth representation `ρ₀` of the common norm kernel
  `⁰M(F)` of the standard Levi `M = bernsteinLeviScheme i ν a.roots`. Its
  value is
  `(normalizedInductionFunctor (family.decomposition a.roots)
  (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots
  (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))`.
  This is word for word the `piOmega` of the published
  `BernsteinInducedProgeneratorStatement`, a named copy of an expression
  already in the Library and not a new mathematical notion. The definition
  makes no irreducibility or embedding assumption on `ρ₀`; the theorems
  state the hypotheses they need. Its level parameters are `uF` and `uV`,
  and the representation spaces live in `Type (max uF uV)`. Write it as
  `bernsteinInducedProgenerator.{uF, uV}` at use sites: without the explicit
  universes, the level `max ?uF ?uV` is left unresolved and elaboration times
  out.

- `bernsteinInducedProgenerator_eq`: the defining unfolding, proved by
  `rfl`. It equates the definition with the `piOmega` expression above.

- `finite_bernsteinInducedProgenerator_of_leviInductionFiniteType`: assume
  the same VI.7.5 premise. Then for every Bernstein cuspidal datum `a` and
  every irreducible `ρ₀` of the common norm kernel of
  `bernsteinLeviScheme i ν a.roots`, `bernsteinInducedProgenerator.{uF, uV} i
  ν family a ρ₀` is finitely generated over `ℂ[G(F)]`. Since the definition
  unfolds by `rfl` to the `piOmega` of `BernsteinInducedProgeneratorStatement`,
  the conclusion is that statement's `Module.Finite` conjunct. The proof
  applies the previous theorem with `I = a.roots` to `Π_D`. The finiteness
  hypothesis on `Π_D` is the published
  `finite_rationalNormKernelSummandInduction` for the standard Levi
  `bernsteinLeviScheme i ν a.roots`. That theorem holds for every
  irreducible `ρ₀` of the open common norm kernel: `ρ₀` is cyclic, and
  compact induction from an open subgroup preserves finite generation.

The local instances for affineness of `G` and of the standard Levi, finite
type of the Levi, the closed-immersion property of the Levi inclusion, and
the point and rational-point topologies use the same terms that
`BernsteinInducedProgeneratorStatement` declares through `haveI`/`letI`. The
extra local instance `T2Space F` is the published
`Langlands.HarmonicAnalysis.GeneralLocalField.t2Space F`.

## Scope

Apart from the named definition of `Π_Ω`, this is a conditional reduction for one conjunct of the VI.10.1 Theorem.
The VI.7.5 Theorem is an unproved premise, owned by another task. The module
does not prove block membership, projectivity or the generator property of
`Π_Ω`. It does not prove the unconditional
`BernsteinInducedProgeneratorStatement` and is not submitted as acceptance
of that target. The finite generation of `Π_D` is used here as derived
content: Renard gets it from VI.4.1, while the Lean proof uses the published
compact-induction finiteness theorem on the open common norm kernel.
