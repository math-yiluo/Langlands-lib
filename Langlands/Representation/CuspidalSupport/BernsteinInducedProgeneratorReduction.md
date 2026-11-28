# The induced Bernstein progenerator from its structural inputs (Renard VI.10.1–VI.10.3)

Derived supporting result for Renard VI.10.1–VI.10.3.

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
VI.10.1 (printed p.207 / PDF p.213) introduces `Π_Ω = i_P^G(Π_D)`, where
`Π_D` is the progenerator of `M(M)_D` from VI.4.1. Its Théorème (printed
p.208 / PDF p.214) says that `Π_Ω` is a finitely generated progenerator of the
block `M(G)_Ω`. VI.10.2 (same page) and the VI.10.3 Proposition (printed
p.209 / PDF p.215) are deduced from it.

This module derives the published `BernsteinInducedProgeneratorStatement`
(all four conjuncts), `BernsteinBlockHomEquivalenceStatement` and
`BernsteinBlockJacquetFaithfulStatement` from three Library propositions.
The assembly through Renard's finite-type theorem takes two additional
premises. The individual lemmas use the following inputs.

- `hIndep : RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV}`,
  the VI.10.1 Proposition and Corollary (independence of `i_P^G(Π_D)` from
  the parabolic);
- `hAdj : RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV}`,
  Bernstein's second adjointness (VI.9.6);
- `hJoint : BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}`,
  used for the compact-coefficient property of the restriction of a
  supercuspidal to the common norm kernel (Renard VI.2.1, (a) implies (c));
- `hFT : RepresentedParabolic.LeviInductionFiniteTypeStatement.{uF, max uF uV}`,
  the VI.7.5 Theorem;
- `hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV}`,
  the represented VI.5.2 Lemma (no irreducible subquotient of a proper
  parabolic induction is supercuspidal).

Not every declaration uses all five; each lists the premises it takes.

## Declarations

General lemmas:

- `smoothRepPullbackPullbackSymmIso e A` (definition): for a topological group
  isomorphism `e : H ≃ₜ* K` and a smooth representation `A` of `H`, the
  isomorphism `pullback e (pullback e.symm A) ≅ A` whose carrier map is the
  identity. The first pullback, along `e.symm : K ≃ₜ* H`, is a representation
  of `K`; the second, along `e`, is again a representation of `H`, on which
  `g ∈ H` acts by `A(e.symm (e g)) = A(g)`. The published
  `SmoothRep.pullbackSymmIso` applied to `e.symm` has the same type up to
  `e.symm.symm`; the version here states it with `e` itself, so that its use in
  `exists_surjective_bernsteinStandardRepresentedJacquet_of_isQuotient` at the
  concrete standard Levi does not have to identify `e.symm.symm` with `e`.
- `smoothRep_ne_zero_iff_exists_apply_ne_zero`: a morphism of smooth
  representations is nonzero exactly when it moves some vector off zero. The
  later statements express nonvanishing in this vector form. Elaboration then
  never compares zero morphisms of `SmoothRep` categories whose topology
  instances are written differently.

The core lemma, for arbitrary actual parabolics:

- `exists_ne_zero_leviInduction_of_jacquet_epi`: premises `hIndep`, `hAdj`.
  Take actual rational parabolics `P = MN` and `Q = LU` of a connected reductive
  `G`, an algebraic isomorphism `φ : M ≅ L` and `g ∈ G(F)` with
  `φ ≫ ι_Q = ι_P ≫ Int(g)`. Take an irreducible supercuspidal `π` of `M(F)` and
  an irreducible `ρ₀ ↪ π|_{⁰M(F)}`, and assume `Π_D` is projective. Let `X` be a
  representation of `G(F)` with a surjection `t : r_Q^G(X) ⟶ σ`. Let `s` be a
  morphism to `σ` from the pullback of `Π_D` along
  `(rationalPointIso φ).symm : L(F) ≃ M(F)`, and let `s` move some vector off
  zero. Then every `Y ≅ i_P^G(Π_D)` has a morphism `Y ⟶ X` that moves some
  vector off zero.

  Proof. Let `Q̄ = L Ū` be the opposite parabolic of `Q`, the published
  `oppositeLeviParabolic`. `hIndep` for `P` and `Q̄` gives
  `ψ : i_P^G(Π_D) ≅ i_{Q̄}^G(Π_D ∘ φ⁻¹)`. `hAdj` for `Q̄` and `Q` gives an
  adjunction `i_{Q̄}^G ⊣ r_Q^G`. Pullback along a point isomorphism is an
  equivalence, so the transported `Π_D` is projective. Hence `s` lifts through
  the epimorphism `t` to `u` with `u ≫ t = s`, and `u ≠ 0`. Since `u` is the
  unit of the adjunction followed by `r_Q^G` applied to the adjoint transpose
  of `u`, that transpose `i_{Q̄}^G(Π_D ∘ φ⁻¹) ⟶ X` is nonzero. Composing it
  with `ψ` and the given isomorphism gives the morphism.

  The point isomorphism `e = (rationalPointIso φ).symm` is built inside the
  proof. Its pointwise description `e x = rationalPoints.map φ.inv x`, which
  `hIndep` asks for, then holds by `rfl` for an abstract `φ`. The same
  equation checked at the concrete standard Levis exceeds the kernel's
  heartbeat limit.

The standard-family lemmas (local instances as in
`BernsteinInducedProgeneratorStatement`: the Levi topology is
`rationalPointTopology F (bernsteinLeviScheme i ν I).X`):

- `bernsteinInducedProgenerator_mem`: premises `hind`, `hJoint`. For a cuspidal
  datum `a` and an injective `j : ρ₀ ⟶ Res_{⁰M(F)} a.representation`,
  `bernsteinInducedProgenerator i ν family a ρ₀` lies in
  `bernsteinSaturatedBlockProperty` of `bernsteinInertialClass i ν family a`.
  The joint-basis premise gives the compact restriction
  (`hasCompactNormKernelRestriction_bernsteinCuspidalDatum`). Then the
  published `rationalNormKernelCompactInduction_mem_of_restriction` (with the
  proved `rationalNormKernelFiniteRestriction` and
  `rationalNormKernelTwistEquivalence`) and
  `rationalNormKernelSummandInduction_mem` put `Π_D` in the same-Levi inertia
  block of `a.representation`. `Π_D` is supercuspidal
  (`isSupercuspidal_rationalNormKernelSummandInduction`). The published
  `bernsteinJacquetExclusion_of_inertiaBlock_supercuspidal`, which takes
  `hind`, and `bernsteinJacquetExclusion_implies_block` conclude.
- `bernsteinInducedProgeneratorBlockObject` (definition, entry declaration):
  `Π_Ω` as an object of `BernsteinSaturatedBlock i ν family
  (bernsteinInertialClass i ν family a)`, namely
  `⟨bernsteinInducedProgenerator i ν family a ρ₀, bernsteinInducedProgenerator_mem …⟩`.
  It takes `hind` and `hJoint`.
- `exists_related_jacquet_quotient_of_inertialSupport`: premise `hind`. Let `τ`
  be irreducible with inertial support the class of `a`. Then for some
  cuspidal datum `c` with `IsBernsteinInertiaRelated i ν family a c`, the
  literal representation of `c` is a quotient of the literal standard Jacquet
  module of `τ` along the parabolic of `c`. The published
  `exists_bernsteinCuspidalDatum_jacquet_quotient_induction_embedding` supplies
  `c`. Suppose `τ` is a subquotient of the induction of a datum `b` in the
  class. The represented VI.5.2, through
  `bernsteinJacquetExclusion_of_inertiaBlock_supercuspidal` applied to `b`,
  shows that `c` is related to `b`, hence to `a`.
- `exists_surjective_bernsteinStandardRepresentedJacquet_of_isQuotient`: a
  quotient of the literal standard Jacquet module gives a surjection from the
  represented standard Jacquet module `bernsteinStandardRepresentedJacquetFunctor`
  onto the representation of the standard Levi. It uses
  `bernsteinStandardRepresentedJacquetIso`, pullback along
  `leviRationalPointHomeomorph` and `smoothRepPullbackPullbackSymmIso`.
- `exists_ne_zero_pullback_rationalNormKernelSummandInduction`: if `a` is
  inertia-related to the pullback of `c` along `φ : M_a ≅ M_c`, then the pullback
  of `Π_D` (of `a`) along `(rationalPointIso φ).symm` has a morphism to
  `c.representation` that moves some vector off zero. This is the published
  `exists_nonzero_rationalNormKernelSummandInduction` (Renard VI.4.1:
  `Π_D` maps nontrivially to every irreducible of `M(M)_D`), transported along
  the pullback equivalence.
- `exists_ne_zero_bernsteinInducedProgenerator_of_inertialSupport`: premises
  `hIndep`, `hAdj`, `hJoint`, `hind`. Every irreducible `τ` with inertial
  support the class of `a` receives a nonzero morphism from `Π_Ω`. It combines
  the three previous lemmas with `c` and its conjugacy `cc`. It applies the
  core lemma to the standard parabolics of `a` and `c`, with `φ = cc.iso` and
  `g = cc.point`. The projectivity of `Π_D` is
  `projective_rationalNormKernelSummandInduction_of_datum`, which takes
  `hJoint`. The standard object is matched through
  `bernsteinStandardRepresentedInductionIso`.
- `bernsteinInducedProgenerator_separates`: premises `hIndep`, `hAdj`, `hJoint`,
  `hind`. For every membership proof `hmem` of `Π_Ω` and all block morphisms
  `f ≠ g : X ⟶ Y`, there is `h : ⟨Π_Ω, hmem⟩ ⟶ X` with `h ≫ f ≠ h ≫ g`. This
  is the generator conjunct of `BernsteinInducedProgeneratorStatement`. `Π_Ω`
  is projective in `M(G)` (`projective_bernsteinInducedProgenerator`, which
  takes `hAdj` and `hJoint`). Every irreducible subquotient of `Y` lies in the
  class, by the block property of `Y`, and so receives a nonzero morphism from
  `Π_Ω`. The published `SmoothRep.exists_comp_ne_zero_of_projective_subquotients`,
  applied to `f - g`, gives `h`.

### Finite generation by second adjointness

The private lemma `finite_of_projective_adjoint_image` takes an adjunction
`L ⊣ R` on smooth representation categories with `L` additive and `R`
preserving small colimits. Let `P` be finitely generated over its group
algebra and let `Y = L.obj P` be projective. For each vector `i` of `Y`, take
the subrepresentation `A i` spanned over the group algebra by `i`. The map
`q : ⨁ A ⟶ Y` whose components are the inclusions is surjective, since
each vector lies in its own cyclic subrepresentation. Projectivity gives a
section `s : Y ⟶ ⨁ A`. Its adjoint transpose is a map
`P ⟶ ⨁ (R.obj ∘ A)`, via the isomorphism given by coproduct preservation.
By `SmoothRep.finite_decomposition_hom_directSum` this map is a sum of its
components over a finite set `T`. Naturality and additivity of the adjunction
transport that sum back to `s`. Evaluating `s ≫ q = 𝟙 Y` on each vector of
`Y` shows that the cyclic spans indexed by `T` generate `Y`.

`finite_bernsteinInducedProgenerator_of_secondAdjointness` applies this lemma
to `P = Π_D`, with `L` represented standard induction and `R` opposite
Jacquet restriction. `bernsteinStandardSecondAdjunction` takes `hAdj`.
`leviInductionFunctor_additive` gives additivity, and
`leviJacquetFunctor_preservesColimits` gives coproduct preservation.
`finite_rationalNormKernelSummandInduction` gives finite generation of `Π_D`
from irreducibility of `ρ₀`. The published `jointSpecialCompactBasisExistence`
gives the joint basis for projectivity of `Π_D`, which transfers to `L.obj Π_D`
by `projective_bernsteinStandardRepresentedInduction`. Finally
`moduleFinite_of_smoothRepIso` transports the conclusion to the literal
standard induction via `bernsteinStandardRepresentedInductionIso`.

Renard obtains this conjunct from VI.7.5. The adjunction argument uses
projectivity of the particular induced object and finite generation of its
inducing representation.

### Assembly

The following declarations use the binders of the published statements.

- `bernsteinInducedProgenerator_of_independence`: from `hIndep`, `hAdj` and
  `hind`, `BernsteinInducedProgeneratorStatement.{uF, uV}`. This uses
  `finite_bernsteinInducedProgenerator_of_secondAdjointness` and supplies the
  published `jointSpecialCompactBasisExistence` to the membership, lifting
  and generator arguments.
- `bernsteinBlockHomEquivalence_of_independence` and
  `bernsteinBlockJacquetFaithful_of_independence`: from the same three
  premises, `BernsteinBlockHomEquivalenceStatement.{uF, uV}` and
  `BernsteinBlockJacquetFaithfulStatement.{uF, uV}`. These apply
  `bernsteinBlockHomEquivalence_of_inducedProgenerator` and
  `bernsteinBlockJacquetFaithful_of_inducedProgenerator`, respectively.
- `bernsteinInducedProgenerator_of_secondAdjointness`: from `hIndep`, `hAdj`,
  `hJoint`, `hFT` and `hind`, `BernsteinInducedProgeneratorStatement.{uF, uV}`.
  Membership is `bernsteinInducedProgenerator_mem`. The lifting conjunct is the
  published `bernsteinInducedProgenerator_lift_of_secondAdjointness`.
  Finite generation is the published
  `finite_bernsteinInducedProgenerator_of_leviInductionFiniteType`. The
  generator conjunct is `bernsteinInducedProgenerator_separates`.
- `bernsteinBlockHomEquivalence_of_secondAdjointness`: from the same five
  premises, `BernsteinBlockHomEquivalenceStatement.{uF, uV}`, through the
  published `bernsteinBlockHomEquivalence_of_inducedProgenerator`.
- `bernsteinBlockJacquetFaithful_of_secondAdjointness`: from the same five
  premises, `BernsteinBlockJacquetFaithfulStatement.{uF, uV}`, through the
  published `bernsteinBlockJacquetFaithful_of_inducedProgenerator`.

## Comparison with the source proof

Renard proves generation as follows. For irreducible `π` in `M(G)_Ω`, take a
standard `P' = M'N'` with `r_{P̄'}^G(π)` supercuspidal. The counit of
`i_{P'}^G ⊣ r_{P̄'}^G` and the exactness of `i_{P'}^G` give a composition
factor `ρ'` with `i_{P'}^G(ρ') ↠ π`. Then `Π_{D'} ↠ ρ'` gives
`i_{P'}^G(Π_{D'}) ↠ π`, and the Proposition replaces `(P', D')` by `(P, D)`.
The Lean argument starts instead with a standard Jacquet quotient. The
Library's standard support presentation gives a cuspidal datum `c` whose
representation `σ_c` of `M_c(F)` is a quotient of the standard Jacquet module
`r_{P_c}^G(τ)` along the standard parabolic `P_c` of `c`. The represented
VI.5.2, through the published geometric exclusion, shows that `c` is in the
inertial class of `a`, with a conjugacy `φ : M_a ≅ M_c`. Over the Levi
`M_c(F)`, the transported `Π_D ∘ φ⁻¹` maps nontrivially to `σ_c` (VI.4.1), and
projectivity lifts this map through the surjection `r_{P_c}^G(τ) ↠ σ_c` to a
nonzero morphism `Π_D ∘ φ⁻¹ ⟶ r_{P_c}^G(τ)`. Second adjointness for the
opposite parabolic `P̄_c`, that is the adjunction `i_{P̄_c}^G ⊣ r_{P_c}^G`,
turns it into a nonzero morphism `i_{P̄_c}^G(Π_D ∘ φ⁻¹) ⟶ τ`. The
independence premise identifies its source with `i_{P_a}^G(Π_D) = Π_Ω`. Renard also passes from irreducible objects to all
objects of the block by projectivity and the existence of irreducible
subquotients; the Lean proof does the same through
`SmoothRep.exists_comp_ne_zero_of_projective_subquotients`.

The membership of `Π_Ω` in the block, implicit in the source, is derived here
from the represented VI.5.2 and the joint-basis premise as described above.

## Technical notes

Call sites write the universes explicitly (`.{uF, uV}`) wherever no argument
fixes `uV`. Without them the level `max ?uF ?uV` stays unresolved and
elaboration times out. Several declarations set a finite `maxHeartbeats`
above the default (800000, and 1600000 for
`exists_related_jacquet_quotient_of_inertialSupport`).

## Scope

The three conclusions are conditional on the premises listed for their
assembly. The shorter assembly takes independence, second adjointness and the
represented VI.5.2. Irreducibility of `ρ₀` is used for generation and finite
generation. Block membership and projectivity use the injectivity of `j`.
