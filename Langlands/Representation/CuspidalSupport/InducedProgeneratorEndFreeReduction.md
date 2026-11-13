# The endomorphism ring of the induced progenerator, from the joint special-compact basis

Author: Worker 5226. This is a derived reduction for task `03c64afa` (Renard VI.10.4–VI.10.5). Reference: David Renard, *Représentations des groupes réductifs p-adiques*, French version dated 9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The first Lemma of VI.10.4 is on printed pp.209–210 / PDF pp.215–216.

The module proves that the published Library proposition
`BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}` implies the published statement `InducedProgeneratorEndFreeStatement.{u, v}`, the Lean form of the first Lemma of Renard VI.10.4. It does not prove `InducedProgeneratorEndFreeStatement` outright. The joint special-compact basis existence is still open in the Library; task `8c39faa0-2a70-4fc4-a027-914987aba924` owns it. It is the only premise, and it is used for one fact only: `Π_D` is projective.

## Relation to Renard

In Renard, `Π_D` is the progenerator of `M(M)_D` constructed in VI.4.1 (VI.10.1, printed p.207 / PDF p.213), so its projectivity comes from VI.4.1. In the Library, VI.4.1 for `Π_D` is available only through compact coefficients. The published Renard VI.2.1, (a) implies (c) (`compactRestriction_of_isSupercuspidal`) shows that a supercuspidal `π` has compact coefficients on `⁰M(F)`. That result needs the joint special-compact basis existence as a hypothesis. Its three other structural hypotheses are proved in the Library: `parabolicDynamic`, `standardCocharacter` and `relativeRootSystem`. Compact coefficients pass to the subrepresentation `ρ₀`, and then `c-ind_{⁰M}^{M} ρ₀` is projective (`CuspidalSupport.rationalNormKernelSummandInduction_projective`).

The free-module part of the Lemma is the construction `inducedProgeneratorEndBasis` (`InducedProgeneratorEndBasis.lean`). That construction follows a route of the author's own: the first adjunction `r_P ⊣ i_P` and the geometric-lemma filtration, instead of Renard's second adjointness and block projection `r_D`. Its Markdown describes the route. This module only discharges the construction's two hypotheses on `Π_D` and assembles the four conjuncts.

## Setting

- `k` is a nonarchimedean local field in universe `u`. `G` is a connected reductive group scheme over `k` (`hG`). `G(F)` carries `RationalPointFamily.pointTopology` and is assumed locally compact and nonarchimedean.
- `P = MN` is an actual rational parabolic of `G`, given by `p l r hp hr hl hmul`. `M(F)` carries `leviPointTopology l hl`, which is locally compact and nonarchimedean by `leviPoints_locallyCompactSpace` and `leviPoints_nonarchimedeanGroup`.
- `π : SmoothRep.{0, u, v} ℂ M(F)` is irreducible and supercuspidal (`IsSupercuspidal`, tested on every proper actual rational parabolic of `M`). `ρ₀` is an irreducible smooth representation of `⁰M(F) = Plancherel.rationalCommonNormKernel M`, and `j : ρ₀ ⟶ π|_{⁰M(F)}` is injective.
- `Π_D = CuspidalSupport.rationalNormKernelSummandInduction M ρ₀ = c-ind_{⁰M(F)}^{M(F)} ρ₀`, a `SmoothRep.{0, u, max u v}`, and `i_P = leviInductionFunctor.{u, max u v} p l r hp hr hl hmul`.
- `W = twistStabilizerDoubleCosets p l hp hl π`. This is the set `W` of `InducedProgeneratorEndFreeStatement`, written out the same way: the double cosets `P(F) w P(F)` of points `w` that normalize `M` through some `φ : M ≅ M` and for which `π ∘ φ` is an unramified twist of `π`. It is the actual-group form of Renard's `W(D)`.

## Declarations

- `projective_rationalNormKernelSummandInduction_of_jointSpecialCompact` (theorem). Assume `hJoint : JointSpecialCompactBasisExistenceStatement.{u}`, `π` supercuspidal and `j : ρ₀ ⟶ π|_{⁰M(F)}` injective. Then `Π_D` is projective in `SmoothRep ℂ M(F)`. Irreducibility of `π` and `ρ₀` is not needed. Proof: `compactRestriction_of_isSupercuspidal parabolicDynamic standardCocharacter relativeRootSystem hJoint` at the connected reductive group `M` (`hl.isConnectedReductive`) gives `HasCompactNormKernelRestriction π`. By definition, that is compact coefficients of the restriction `π.representation.comp (⁰M).subtype`, which is the hypothesis of `CuspidalSupport.rationalNormKernelSummandInduction_projective`. The topology `leviPointTopology l hl` on `M(F)` is definitionally the point topology used by both lemmas.

- `inducedProgeneratorEndBasisOfJointSpecialCompact` (definition, entry declaration). Assume `hJoint`, `hG`, the parabolic data, `π` irreducible and supercuspidal, `ρ₀` irreducible and `j` injective. The definition is a `Module.Basis` of `i_P Π_D ⟶ i_P Π_D` over `(End Π_D)ᵐᵒᵖ`, indexed by `W`. The module structure is `RepFunctorFiltration.endPrecompModule`, with `op a • x = i_P(a) ≫ x`. The definition is `inducedProgeneratorEndBasis` with its two hypotheses supplied: `Π_D` is projective by the previous theorem, and supercuspidal by the published `isSupercuspidal_rationalNormKernelSummandInduction`.

- `inducedProgeneratorEndFree_of_jointSpecialCompact` (theorem): `JointSpecialCompactBasisExistenceStatement.{u} → InducedProgeneratorEndFreeStatement.{u, v}`. After introducing the data of the statement, the proof establishes the four conjuncts as follows.
  1. Injectivity of `a ↦ i_P(a)` on `End(Π_D)` is the injectivity of the published embedding `leviInductionEndEmbedding.{u, max u v} p l r hp hr hl hmul Π_D`, which holds without any hypothesis.
  2. `W.Finite` comes from `inducedProgeneratorEnd_expansion`.
  3. So do `b : Fin W.ncard → End(i_P Π_D)` and the unique expansion `x = ∑ i_P(aᵢ) ≫ bᵢ`. That theorem needs `Π_D` projective and supercuspidal, which the previous theorem and `isSupercuspidal_rationalNormKernelSummandInduction` supply. Its `W` is `twistStabilizerDoubleCosets p l hp hl π`, which is definitionally the `W` of the statement.
  4. The finite unique expansion over the centre of `End(Π_D)` is the published `leviInducedEndCenterExpansion_of_endExpansion`, applied to the expansion of conjunct 3.

## Use

Once task `8c39faa0` proves `JointSpecialCompactBasisExistenceStatement`, the proof of `InducedProgeneratorEndFreeStatement` is `inducedProgeneratorEndFree_of_jointSpecialCompact` applied to that proof. No other open input remains for this statement.
