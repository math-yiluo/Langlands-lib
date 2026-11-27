# Berkovich's comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` (étale): proof

Module `Langlands.Cohomology.AnalyticEtaleCompactComparison.Proof`, namespace
`Langlands.Cohomology.AnalyticEtaleCompactComparison`.

The theorem `analyticEtaleCompactComparison` proves
`AnalyticEtaleCompactComparisonStatement L X h G ρ R`, defined in the module
`Langlands.Cohomology.AnalyticEtaleCompactComparison.Statement`. It takes only the
parameters and instance arguments of the statement, and it is universe-polymorphic in
`u`, `v`, `uL` and `z` as the statement is.

## What is proved

Let `K : Type u` be a complete ultrametric normed field, `L : Type uL` a normed field with
`[NormedAlgebra K L]`, `X : LocalizedCategory.{u, v, v} (K := K)` an analytic space over
`K`, `h` the point axioms for every `L`-valued point of `X`, `G : Type z` a topological group
with `[Small.{max u (v + 1) uL} G]`, `ρ : G →* Aut X` an action with
`[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`, and
`R : Type (max u (v + 1) uL)` a commutative ring. If `|X| = localizedSpaceFunctor.obj X` is
Hausdorff, `pointProjection L X` is surjective (every point of `X` underlies an `L`-valued
point) and `IsContinuousAction ρ` holds, then for every `q : ℕ` the natural transformation

```text
etaleCompactComparison L ρ h R q :
  etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G
    ⟶ etaleGSheafRestriction ρ R ⋙ etaleCompactCohomology L h R q
```

is an isomorphism. That is, the comparison maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)` are
bijective, naturally in the étale `G`-sheaf of `R`-modules `F`. The binder `h` and the
instance `HasAdmissibleRefinements` are used only as the hypotheses they are; no other
hypothesis enters.

## The implemented proof

The proof is one application:

```lean
compactComparison_of_compactAcyclic L X h G ρ R
  (analyticEtaleRestrictedInjectiveAcyclic L X h G ρ R).1
```

- `compactComparison_of_compactAcyclic` (module
  `Langlands.Cohomology.AnalyticEtaleCompactComparison.GeometryReduction`) proves
  `AnalyticEtaleCompactComparisonStatement L X h G ρ R` from the single premise
  `AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R`.
- `analyticEtaleRestrictedInjectiveAcyclic` (module
  `Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.Proof`) proves the
  conjunction `AnalyticEtaleRestrictedInjectiveAcyclicStatement L X h G ρ R`, with no
  hypotheses beyond the same parameters and instances. Its first component, taken with
  `.1`, is exactly that premise: if `|X|` is Hausdorff, `pointProjection L X` is
  surjective and the action is continuous, then for every injective object `I` of
  `EtaleGSheaf ρ` and every `q`, `etaleCompactCohomology L h R (q + 1)` vanishes on
  `(etaleGSheafRestriction ρ R).obj I`.

Inside the reduction the argument runs as follows (see `GeometryReduction.md` and
`Reduction.md` in this directory).

1. **Geometric inputs.** `compactComparison_of_compactAcyclic` supplies
   `etaleOpenDomainStatement X` (module `Langlands.Geometry.Analytic.EtaleOpenDomains.Proof`:
   inclusions of open analytic domains are étale) and `etaleOpenMap K` (module
   `Langlands.Geometry.Analytic.EtaleOpenMap.Proof`: underlying maps of étale morphisms
   are open) to `compactComparison_of_openDomains_of_openMap_of_compactAcyclic`
   (module `Langlands.Cohomology.AnalyticEtaleCompactComparison.Reduction`).
2. **Degree zero.** Since `|X|` is Hausdorff, the complement of a point is an open
   domain; from the open-domain statement and `h`, `etalePointLifting_of_openDomains`
   (module `Langlands.Sheaf.Equivariant.AnalyticEtaleSupport`) gives `EtalePointLifting`:
   an `L`-valued point lifts to every étale object whose image contains its underlying
   point. With this lifting, surjectivity of `pointProjection L X` and openness of the
   structural maps of étale objects, `isIso_etaleCompactInclusion` (module
   `Langlands.Sheaf.Equivariant.AnalyticEtaleCompactLocal`) shows that the inclusion
   `etaleCompactInclusion` of `Γ_{c,X{G}}(F)` into `Γ_c(X, b^*F)` is an isomorphism:
   every compactly supported global section of `b^*F` is fixed by an open subgroup of
   `G`.
3. **Higher degrees.** `isIso_etaleCompactComparison_of_injective_acyclic` (module
   `Langlands.Sheaf.Equivariant.AnalyticEtaleCompactDerivedComparison`, an instance of
   `ExactBaseChange.isIso_baseChangeNatTrans_of_injective_acyclic` for the exact functors
   `b^*` and `smoothForget`) turns the degree-zero isomorphism and the vanishing of
   positive-degree compactly supported cohomology on restrictions of injective étale
   `G`-sheaves into invertibility of `etaleCompactComparison L ρ h R q` in every degree
   `q`. The vanishing is the premise
   supplied by `(analyticEtaleRestrictedInjectiveAcyclic L X h G ρ R).1`, whose proof
   (described in `../AnalyticEtaleRestrictedInjectiveAcyclic/Proof.md`) exhibits each
   injective `I` as a retract of its degree-zero equivariant Godement term and shows that
   the restriction of that term is acyclic for compactly supported cohomology.

No step assumes that the restriction `etaleGSheafRestriction` preserves injective objects.

## Axioms

The theorem depends on the axioms `propext`, `Classical.choice` and `Quot.sound` only.

## Source

Vladimir G. Berkovich, *Étale equivariant sheaves on p-adic analytic spaces* (unfinished
manuscript, 1995–1996), Corollary 1.5.2(i), first assertion, printed pp. 11–12; the
statement module documents how the Library's formulation corresponds to it. Berkovich's
proof (p. 12) derives degree zero from the fact that every element of `H^0_c(X, b^*F)` is
fixed by an open subgroup of `G`, and the general case from Proposition 1.5.1, the softness
of `b^*` of the Godement terms. The Lean proof follows the same two steps; in higher degrees
it uses the vanishing of compactly supported cohomology of the restricted Godement terms in
place of softness, and the Godement retraction of injective objects in place of a δ-functor
argument.
