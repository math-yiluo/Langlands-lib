# Harris's `ℓ`-divisible Godement systems on a coreflective subcategory of twisted sheaves

Author: Worker 26. Generalizes Worker 26's published modules
`Langlands.Cohomology.DivisibleSystem.TwistedGodement`, `TwistedTruncation` and
`TwistedInverseLimit` from discrete sheaves to a coreflective exact subcategory. It uses:

- `Langlands.Sheaf.Equivariant.TwistedExactGodement` (Worker 26, submitted with this module):
  `exactZeroFunctor`, `exactCoaugmentation`, `mono_exactCoaugmentation_of_jointlyFaithful` and
  `exactComplexFunctor`;
- `Langlands.Sheaf.Equivariant.TwistedExactCompactComparison` (Worker 26):
  `exactCompactSections`, `exactCompactDerived` and the left exactness of
  `exactCompactSections`;
- the generic constructions that the published twisted modules use: `DivisibleSystem.map`
  (`Langlands.Cohomology.DivisibleSystem`), `coaugmentation`, `residualSystem` and
  `termSystem` (`DivisibleSystem.Coaugmented`), `resolutionSystem` and its lemmas
  (`DivisibleSystem.Resolution`), `truncatedResolutionSystem` and its lemmas
  (`DivisibleSystem.Truncation`), `acyclicTruncatedSectionsSystem`,
  `acyclicTruncatedSectionsHomologyIso` and `isZero_rightDerived_truncatedResolutionSystem_obj_X`
  (`DivisibleSystem.AcyclicTruncation`), and `acyclicTruncatedSectionsHomologyNatIso` from
  `TwistedInverseLimit`;
- Worker 61's `quotientInvariantsLimit`, `quotientInvariantsLimitToRepExtend`,
  `quasiIso_quotientInvariantsLimitToRepExtend`, `quotientInvariantsInverseLimit`,
  `quotientInvariantsInverseLimitComparison`, `isIso_quotientInvariantsInverseLimitComparison`,
  `extendHomologyNatIso`, `extendLevelCohomologyLimitIso`, `mapHomologicalComplexHomologyIso`,
  `finite_of_rep_iso` and `Rep.ρ_eq_id_of_iso`;
- Worker 3's statements `ProPInvariantSubcomplexStatement` and
  `FiniteCohomologyInverseLimitStatement`. Neither is proved in the Library; both appear
  only as hypotheses `hS` and `hS'`.

All declarations are in `Langlands.Cohomology.DivisibleSystem`.

## Purpose

The published twisted modules build Harris's Lemma 2.2, Lemma 2.2 bis, (2.3), (2.6), (2.7)
and Lemma 2.8 for the discrete sheaves of a local action system. Their proofs only use that
discrete sheaves form an abelian category with a fully faithful exact inclusion into module
sheaves on the twisted site, that this inclusion has a right adjoint (the discrete part),
and that the category has enough injectives. This module repeats the constructions for any
abelian category `𝒜` with such an inclusion `incl` and adjunction `adj : incl ⊣ cor`. Each
declaration applies the same generic construction as its published counterpart, with
`discreteZeroFunctor`, `discreteCoaugmentation` and `discreteCompactSections` replaced by
`exactZeroFunctor`, `exactCoaugmentation` and `exactCompactSections`. The intended
instance is the étale `G`-sheaves (`DivisibleSystem.AnalyticEtale`).

## Data and hypotheses

In the sections up to compact sections:

- `ρ`, `J`, `points : I → J.Point.{w}` with `I : Type w`, `R : Type w`, and the Kan
  extension hypothesis, as in `TwistedExactGodement`;
- an abelian category `𝒜`, functors `incl` and `cor`, and `adj : incl ⊣ cor`;
- `[PreservesFiniteLimits (exactZeroFunctor ρ J points R incl cor)]`, and from the section
  on exactness on also `[PreservesFiniteColimits ...]`: the Godement functor is exact
  (Harris's Fact 3, a hypothesis);
- an `ℓ`-divisible system `T : DivisibleSystem 𝒜 ℓ`;
- from the residual systems on, `[incl.Full] [incl.Faithful]` and
  `hpoints : JointlyFaithful fun i => (points i).sheafFiber`, which make the coaugmentation
  monic;
- a bound `D : ℕ` for the truncation.

The compact-section section adds: `[P.ContainsIdentities]`, `[LocallySmall.{w} (P.Over ⊤ X)]`,
a topological group `G`, `[HasSheafify J (ModuleCat R)]`, `[incl.Additive]`, the exactness
of `incl`, `[EnoughInjectives 𝒜]`, points `Ψ : I' → J.Point.{w}` with a continuous action of
`G` on `I'` and `E : PointEquivariance ρ Ψ`, and the hypotheses

- `hF`: `exactCompactDerived J R incl E (r + 1)` vanishes on every `exactZeroFunctor M`
  (Godement objects are acyclic for compactly supported sections);
- `hT`: `exactCompactDerived J R incl E n` vanishes on every `T m` for `n > D` (Harris's
  Fact 2).

The inverse-limit section takes the same data with coefficients `R : Type (max w uG)`, as in
`TwistedInverseLimit`, a filtered preorder `ι : Type uG` and an antitone family
`H : ι → Subgroup G` of normal subgroups of finite index with `Fintype` and `DecidableEq`
instances on the quotients, and Worker 61's hypotheses `hK` and `hk`.

## Declarations

Godement systems (Lemma 2.2):

- `exactZeroFunctor_additive`: a left exact Godement functor is additive (Mathlib's
  `Functor.additive_of_preservesBinaryBiproducts`).
- `exactGodementImageSystem`: the system `F(T_m)` (Harris's Fact 4);
  `exactGodementCoaugmentation`: the morphism `T ⟶ F(T)`.
- `exactGodementResidualSystem q` and `exactGodementTermSystem q`: the residual systems and
  the term systems `F^q`.
- `exactGodementResolutionSystem adj T hpoints`: Lemma 2.2, the `ℓ`-divisible system of
  Godement resolutions. `exactGodementResolutionSystemDegreeIso q` identifies degree `q`
  with `F^q`, `exactGodementResolutionSystemObjIso m` identifies level `m` with
  `exactComplexFunctor` of `T m`, and `exactGodementResolutionSystem_obj_exactAt` gives
  exactness in positive degrees.

Truncation (Lemma 2.2 bis):

- `exactGodementTruncatedResolutionSystem ... D`: `G^• = τ_{≤ D+1}(F^•)`;
  `exactGodementTruncatedResolutionHom` the inclusion `G^• ⟶ F^•`, a quasi-isomorphism at
  every level (`quasiIso_exactGodementTruncatedResolutionHom`);
  `isZero_exactGodementTruncatedResolutionSystem_obj_X`: zero above degree `D + 1`;
  `exactGodementTruncatedAugmentation m` and `quasiIso_exactGodementTruncatedAugmentation m`:
  each level resolves `T m`.

Compact sections ((2.3)):

- `isZero_exactCompactDerived_truncatedResolutionSystem_obj_X`: all terms of `G^•_m` are
  acyclic for compactly supported sections.
- `exactGodementTruncatedCompactSectionsSystem ... E hF hT`: the `ℓ`-divisible system of
  complexes `Γ_c(G^•_m)` of smooth representations (`_obj`, by `rfl`, describes level `m`).
- `exactGodementTruncatedCompactHomologyIso m n`: Harris's (2.3),
  `Hⁿ(Γ_c(G^•_m)) ≅ exactCompactDerived n (T m)`; `_hom` (by `rfl`) identifies it with the
  comparison map of the acyclic resolution.
- `isZero_exactGodementTruncatedCompactSectionsSystem_homology`: vanishing above `D`;
  `isZero_exactGodementTruncatedCompactSectionsSystem_obj_X`: vanishing of the terms in
  degrees `q ≥ D + 2`.
- `exactGodementTruncatedCompactHomologyNatIso n`: (2.3), naturally in `m`.
- `exactGodementTruncatedCompactRepHomologyIso m n` and
  `exactGodementTruncatedCompactRepHomology_ρ_eq_id`: the same in `Rep R G`, and the
  transfer of trivial actions of a subgroup.

Inverse limits ((2.6), (2.7), Lemma 2.8):

- `exactGodementQuotientInvariantsLimit`: Harris's `C^•_m`;
  `exactGodementQuotientInvariantsLimitToRepExtend`: the comparison (2.6).
- `quasiIso_exactGodementQuotientInvariantsLimitToRepExtend hS hP hR m htriv`: (2.6) is a
  quasi-isomorphism at level `m` if the `H i` are pro-`p`, `p` is invertible in `R`, and the
  `H i` act trivially on every `exactCompactDerived q (T m)`.
- `exactGodementQuotientInvariantsLimitHomologyIso`: (2.7).
- `exactGodementQuotientInvariantsInverseLimit`: `lim_m C^•_m`;
  `exactGodementQuotientInvariantsInverseLimitHomologyIso hS hS' hP hR htriv hfin n`:
  Lemma 2.8, `Hⁿ(lim_m C^•_m) ≅ limit (m ↦ exactCompactDerived n (T m))` in `Rep R G`.

## Original source

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
Univ. 39 (1999), registered as
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d` (file SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`), §2, printed pp.303–306
= PDF pp.5–8: Fact 2 and Fact 3 (pp.303–304), Lemma 2.2 (p.304), Lemma 2.2 bis and (2.3)
(p.305), (2.6), (2.7) and Lemma 2.8 (p.306). The quotations are in the Markdown of the
published `AnalyticQuasiEtale`.

## Provenance and correspondence

The correspondence with Harris is the one recorded in the published twisted modules. The
generalization from discrete sheaves to a coreflective exact subcategory is ours. Its
purpose is to apply the constructions to Berkovich's étale `G`-sheaves, which are the
locally discrete sheaves of `LocalActionSmoothPart`.

## Not formalized here

The exactness of the Godement functor, the joint faithfulness of the fibre functors, the
acyclicity `hF`, the bound `hT`, Worker 3's statements, and any comparison with the
published discrete-sheaf constructions.
