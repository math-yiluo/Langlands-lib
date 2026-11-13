# Projectivity of the induced Bernstein progenerator (Renard VI.10.1)

Author: Worker 5225. Derived supporting result for Task 5225.

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
VI.10.1 introduces `Π_Ω = i_P^G(Π_D)` (printed p.207 / PDF p.213), where
`Π_D` is the progenerator of `M(M)_D` from VI.4.1. The proof of the
Théorème (printed p.208 / PDF p.214) begins: by Bernstein's second
adjointness theorem, `i_P^G` is left adjoint to `r_{P̄}^G`, which is exact,
so `i_P^G` preserves projectives, and `Π_Ω` is projective.

This module formalizes that step. Two unproved Library propositions are
explicit premises:

- `RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV}`, Renard
  VI.9.6 (second adjointness), owned by another task;
- `BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}`,
  owned by task `8c39faa0-2a70-4fc4-a027-914987aba924`. The published
  Library proof of Renard VI.2.1, (a) implies (c), needs it.

The second premise is used only for the projectivity of `Π_D` in `M(M)`.
Renard takes that fact from VI.4.1. The Lean proof gets it from compact
coefficients instead, as described below.

## Declarations

- `bernsteinStandardOpposite i ν family I` (definition): the opposite
  parabolic `P̄ = M N̄` of the standard parabolic `P = M N` of the simple-root
  set `I`, as `RepresentedParabolic.OppositeLeviParabolicData`. It has the
  same Levi `M` and satisfies `P(F) ∩ P̄(F) = M(F)`. It is the published,
  unconditional `RepresentedParabolic.oppositeLeviParabolic` applied to
  `family.connectedReductive` and the geometric facts
  `bernsteinStandardRepresentativesGeometric i ν family I`.

- `bernsteinStandardOppositeJacquetFunctor i ν family I` (definition): the
  normalized Jacquet functor `r_{P̄}^G`, that is
  `RepresentedParabolic.leviJacquetFunctor` of the opposite data, from
  `SmoothRep ℂ G(F)` to `SmoothRep ℂ M(F)` in the carrier universe
  `max uF uV`.

- `bernsteinStandardSecondAdjunction i ν family hAdj I` (definition, entry
  declaration): a chosen adjunction
  `bernsteinStandardRepresentedInductionFunctor i ν family I ⊣
  bernsteinStandardOppositeJacquetFunctor i ν family I`, that is
  `i_P^G ⊣ r_{P̄}^G` for the standard parabolic of `I`. The premise `hAdj`
  is instantiated at the standard parabolic, Levi and unipotent radical and
  at the opposite data, and gives `Nonempty (i_P^G ⊣ r_{P̄}^G)`. The
  definition takes `Nonempty.some`. The represented induction functor is
  the published `bernsteinStandardRepresentedInductionFunctor`.

- `bernsteinStandardOppositeJacquetFunctor_preservesEpimorphisms`
  (instance): `r_{P̄}^G` preserves epimorphisms. It is a left adjoint by the
  published first adjointness
  `RepresentedParabolic.leviFirstAdjointnessAdjunction` for `P̄`, and
  Mathlib's `Functor.preservesEpimorphisms_of_adjunction` applies. This
  replaces Renard's appeal to exactness of `r_{P̄}^G`.

- `projective_bernsteinStandardRepresentedInduction`: under `hAdj`, the
  represented standard induction sends projective objects to projective
  objects. This is Mathlib's `Adjunction.map_projective` for the adjunction
  above.

- `projective_bernsteinStandardInduction`: the same for the literal standard
  normalized induction
  `(normalizedInductionFunctor (family.decomposition I)
  (family.closedUnipotent I)).obj (bernsteinLiteralLeviRep i ν I ρ)`. The
  proof transports along the published isomorphism
  `bernsteinStandardRepresentedInductionIso i ν family I ρ` with
  `Projective.of_iso`.

- `hasCompactNormKernelRestriction_bernsteinCuspidalDatum`: under `hJoint`,
  for every Bernstein cuspidal datum `a` the restriction of
  `a.representation` to the common norm kernel `⁰M(F)` has compact
  coefficients (`RepresentedParabolic.HasCompactNormKernelRestriction`).
  This is Renard VI.2.1, (a) implies (c). It applies the published
  `RepresentedParabolic.compactRestriction_of_isSupercuspidal` with the
  proved inputs `parabolicDynamic`, `standardCocharacter` and
  `relativeRootSystem`. Connected reductivity of the Levi comes from
  `bernsteinStandardRepresentativesGeometric`, and supercuspidality from
  the published `BernsteinCuspidalDatum.isSupercuspidal`.

- `projective_rationalNormKernelSummandInduction_of_datum`: under `hJoint`,
  for every subrepresentation `j : ρ₀ ↪ Res_{⁰M(F)} a.representation`
  (`j` injective), `Π_D = rationalNormKernelSummandInduction M ρ₀` is
  projective in `SmoothRep ℂ M(F)`. The proof applies the published
  `rationalNormKernelSummandInduction_projective` to the compactness above.
  The proof restates that compactness as
  `HasCompactSmoothDualCoefficients (a.representation.representation.comp
  (rationalCommonNormKernel M).subtype)` by `exact`, which avoids a costly
  unification.

- `projective_bernsteinInducedProgenerator`: under `hAdj` and `hJoint`, the
  representation
  `(normalizedInductionFunctor (family.decomposition a.roots)
  (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots
  (rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀))`
  is projective in `SmoothRep ℂ G(F)`. This expression is word for word the
  `piOmega` of `BernsteinInducedProgeneratorStatement`. The proof combines
  the two previous theorems with `I = a.roots`.

- `bernsteinSaturatedBlock_lift_of_projective`: in a Bernstein saturated
  block `BernsteinSaturatedBlock i ν family s`, an object whose underlying
  representation is projective in `SmoothRep ℂ G(F)` lifts along every
  block epimorphism. The block is a Serre class (published instance
  `bernsteinSaturatedBlockProperty_isSerreClass`), so its inclusion
  preserves epimorphisms (Mathlib's
  `ObjectProperty.preservesEpimorphisms_ι_of_isNormalMonoCategory`). The
  lift is `ObjectProperty.homMk (Projective.factorThru f.hom q.hom)`. The
  proof follows the published `rationalInertiaBlockProjectiveLift`.

- `bernsteinInducedProgenerator_lift_of_secondAdjointness`: under `hAdj`
  and `hJoint`, for every datum `a`, every injective `j`, and every proof
  `hmem` that `piOmega` lies in the block of
  `bernsteinInertialClass i ν family a`, the following holds: for all block
  objects `Y Z`, every epimorphism `q : Y ⟶ Z` and every `f : ⟨piOmega, hmem⟩
  ⟶ Z`, there is `g` with `g ≫ q = f`. This is the projectivity conjunct of
  `BernsteinInducedProgeneratorStatement`, stated for an arbitrary
  membership proof.

Several theorems that do not need `[LocallyOfFiniteType G.X.hom]` omit it.
Call sites write the universes explicitly, as in `.{uF, uV}`, wherever no
argument fixes `uV`. Otherwise the level `max ?uF ?uV` is left unresolved
and elaboration times out. The local instances for affineness and topology
of `G` and the standard Levi use the same terms as
`BernsteinInducedProgeneratorStatement`. The extra local instances are
`T2Space F` and local compactness and the nonarchimedean group property of
the standard Levi points. They are proved as in the published
`BernsteinRepresentedCuspidality`.

## Scope

This module is a conditional reduction for the projectivity conjunct of the
VI.10.1 Theorem. Its two premises are unproved and owned by other tasks. It
does not prove block membership of `Π_Ω`, its finite generation, or the
generator property. It does not prove `BernsteinInducedProgeneratorStatement`
and is not submitted as acceptance of that target. Irreducibility of `ρ₀` is
not needed here; only the injectivity of `j` is used.
