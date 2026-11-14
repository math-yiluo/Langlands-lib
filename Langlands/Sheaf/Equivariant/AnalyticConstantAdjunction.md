# Constant étale and quasi-étale `G`-sheaves and injectivity of `Γ_{X{G}}`

Author: Worker 26. Specializes `Langlands.Sheaf.Equivariant.TwistedConstantAdjunction`
(Worker 26, submitted together with this module) to Berkovich's étale and quasi-étale
`G`-sheaves. It also uses:

- `Langlands.Sheaf.Equivariant.AnalyticGSheaves` (Worker 26): `EtaleGSheaf ρ` (locally
  discrete sheaves of `distinguishedLiftSystem ρ` on `twistedEtaleTopology ρ`),
  `QuasiEtaleGSheaf ρ` (discrete sheaves of `compactLiftSystem ρ` on
  `twistedQuasiEtaleTopology ρ`), and `isLiftSystem_liftSystem` (the admissible actions of a
  lift system are lifts);
- `Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology` (`etaleGSheafSections`) and
  `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology` (`quasiEtaleGSheafSections`)
  (Worker 26): Berkovich's `Γ_{X{G}}`;
- `twistedEtale_hasSheafify` (`AnalyticEtaleCompactCohomology`) and
  `twistedQuasiEtale_hasSheafify` (`AnalyticQuasiEtaleCompactCohomology`), supplied with
  `haveI`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant.Analytic`.

## Data and universes

- `K : Type u` is a complete ultrametric normed field, `X` an object of Worker 21's
  `LocalizedCategory.{u, v, v} (K := K)`, `G : Type z` a topological group with
  `[Small.{w} G]` and `ρ : G →* Aut X`, where `w = max u (v + 1) uL`.
- `R : Type w` is a commutative ring. As `uL` occurs only inside `w`, uses name the universes
  explicitly, as in `etaleConstantGSheaf.{u, v, uL} ρ R`.
- Étale case: `[(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]`.
  Quasi-étale case:
  `[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`.
  These are the hypotheses of the published modules on these sheaves.

## Declarations

- `etaleConstantGSheaf ρ R : SmoothRep R G ⥤ EtaleGSheaf ρ (ModuleCat R)`: the constant
  étale `G`-sheaf of a smooth representation `M`, the sheafification of the presheaf that is
  `M` on every object of the twisted étale site, where a twisted morphism with twist `g` acts
  by `g⁻¹` (`smoothSheafConstantTwisted`).
- `etaleConstantGSheafAdjunction ρ R : etaleConstantGSheaf ρ R ⊣ etaleGSheafSections ρ R`.
- `etaleConstantGSheaf_preservesMonomorphisms`.
- `etaleGSheafSections_preservesInjectiveObjects`: `Γ_{X{G}}` sends injective étale
  `G`-sheaves to injective smooth representations of `G`.
- `quasiEtaleConstantGSheaf ρ R : SmoothRep R G ⥤ QuasiEtaleGSheaf ρ (ModuleCat R)`
  (`discreteConstantTwisted`), `quasiEtaleConstantGSheafAdjunction ρ R` (left adjoint to
  `quasiEtaleGSheafSections ρ R`), `quasiEtaleConstantGSheaf_preservesMonomorphisms` and
  `quasiEtaleGSheafSections_preservesInjectiveObjects`.

## Original source

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
manuscript), registered as
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90` (folder
SHA-256 `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`):

- §1.2, printed pp.4–5 = PDF pp.4–5: the spectral sequence
  `E_2^{p,q} = H^p(G, H^q(X{G}, F)) ⟹ H^{p+q}(X(G), F)` for quasi-étale (resp. étale)
  abelian sheaves, quoted in the Markdown of `AnalyticEtaleCohomology`.
- Definition 1.4.1 and Theorem 1.4.2, printed pp.7–8: étale `G`-sheaves and their twisted
  model, as recorded in the Markdown of `AnalyticEtaleComparison` and
  `AnalyticEtaleCompactCohomology`.

## Provenance and correspondence

Derived, a specialization of `TwistedConstantAdjunction`; see its Markdown. With the published
modelling of Berkovich's étale and quasi-étale sheaves on `X(G)` by `EtaleGSheaf ρ` and
`QuasiEtaleGSheaf ρ`, and of `Γ_{X{G}}` by `etaleGSheafSections` and
`quasiEtaleGSheafSections`, the theorems `etaleGSheafSections_preservesInjectiveObjects` and
`quasiEtaleGSheafSections_preservesInjectiveObjects` are the input of the composite-functor
spectral sequence of §1.2 for `Γ_{X(G)} = (-)^G ∘ Γ_{X{G}}` (`etaleGSheafInvariantSections`,
and `exactInvariantGlobalSections` for quasi-étale `G`-sheaves). Berkovich does not single out
this statement; it is our step towards his spectral sequence. The constant `G`-sheaf of a
smooth representation is our construction and is not claimed to be named in the manuscript.

## Not formalized here

The spectral sequence of §1.2 and its derived-category form; the identification of the global
sections of the constant `G`-sheaf of `M` with `M`; and the refinement hypotheses, which
remain hypotheses.
