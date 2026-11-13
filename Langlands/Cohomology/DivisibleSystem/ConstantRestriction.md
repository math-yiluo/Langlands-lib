# Restriction of constant equivariant sheaves and the comparison with plain cohomology

Author: Worker 26. Builds on the following modules:

- Mathlib's `Functor.pushforwardContinuousSheafificationCompatibility` and
  `Functor.toSheafify_pullbackSheafificationCompatibility`
  (`Mathlib/CategoryTheory/Sites/CoverLifting.lean`). For a functor `G : C ⥤ D` that is
  continuous and cocontinuous for topologies `J` and `K`, they give the isomorphism
  `(whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅ presheafToSheaf K A ⋙
  G.sheafPushforwardContinuous A J K`. This requires pointwise right Kan extensions along
  `G.op` and weak sheafification for both topologies. They also describe its components
  through the canonical maps `toSheafify`.
- `Langlands.Sheaf.Equivariant.TwistedOver` (Worker 26). It provides the twisted site of
  `G` acting on `X` through `ρ`, its topology `twistedTopology ρ J`, the inclusion
  `ι P ρ` (continuous and cocontinuous), and `TwistedOver.restriction ρ J A`, the
  pushforward along `ι P ρ`. Restriction forgets the equivariant structure.
- `Langlands.Sheaf.Equivariant.LocalActionConstant` (Worker 26). It provides
  `discreteConstantSheaf L J R`, Mathlib's `constantSheaf` with values in discrete sheaves.
- `Langlands.Cohomology.DiscreteSheafDerivedComparison` (Worker 26):
  `discreteRestriction J R L`, the inclusion of discrete sheaves followed by restriction.
- `Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtaleConstant` (Worker 26). It provides
  the constant quasi-étale `G`-sheaf functor `quasiEtaleConstantSheaf ρ R`, Harris's compact
  section complexes `quasiEtaleConstantCompactSectionsSystem` for the constant system
  `{R / ℓ ^ m R}`, and Harris's (2.3) for it, `quasiEtaleConstantCompactHomologyIso`.
- `Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleComparison` (Worker 26). It provides
  Berkovich's `b^*` (`quasiEtaleGSheafRestriction ρ R`), the plain compactly supported
  cohomology `quasiEtaleCompactCohomology L h R q` (`H^q_c(X, -)` on the quasi-étale site
  of `X`), and Berkovich's comparison
  `quasiEtaleCompactComparison L ρ h R q : H^q_c(X{G}, F) → H^q_c(X, b^*F)`.
  Through it, the module uses the instances `quasiEtale_hasSheafify`,
  `twistedQuasiEtale_hasSheafify` and `quasiEtale_hasPointwiseRightKanExtension`.

All declarations are in the namespace `Langlands.Sheaf.Equivariant`; the quasi-étale ones
are in `Langlands.Sheaf.Equivariant.Analytic`.

## Purpose

Harris's (2.3) identifies the compactly supported cohomology of the space `U(ẽ)` itself
with constant coefficients `ℤ/ℓ^mℤ` with the cohomology of his complexes `G^•_m`. The
published (2.3), `quasiEtaleConstantCompactHomologyIso`, computes instead the equivariant
cohomology `H^n_c(X{G}, R / ℓ ^ m R)`. Berkovich's comparison
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` goes to plain cohomology, but its target has coefficients
`b^*F`. This module identifies `b^*` of a constant `G`-sheaf with the constant sheaf of `X`.
It then composes the published maps into the map from Harris's complexes to the plain
cohomology `H^n_c(X, R / ℓ ^ m R)`.

## Restriction of constant sheaves on the twisted site

Let `C` be a category with a morphism property `P` respecting isomorphisms, `X : C`, and
`ρ : G →* Aut X`. Let `J` be a topology on `P.Over ⊤ X` invariant under translations, and
`A` a category. Assume pointwise right Kan extensions along `(ι P ρ).op` of all presheaves
with values in `A`, and `[HasWeakSheafify J A]` and
`[HasWeakSheafify (twistedTopology ρ J) A]`.

- `constantSheafCompRestrictionIso ρ J A :
  constantSheaf (twistedTopology ρ J) A ⋙ TwistedOver.restriction ρ J A ≅ constantSheaf J A`.
  The restriction of the constant sheaf `M` on the twisted site is the constant sheaf `M`
  over `X`. Its component at `M` is the inverse of Mathlib's
  `pushforwardContinuousSheafificationCompatibility` at the constant presheaf `M` on the
  twisted site. The composite of `ι P ρ` with that constant presheaf is, by definition, the
  constant presheaf `M` on `P.Over ⊤ X`. Naturality is the naturality of Mathlib's
  isomorphism at the constant presheaf maps.
- `constantSheafCompRestrictionIso_inv_app` (`rfl`): the inverse at `M` is the
  compatibility isomorphism at the constant presheaf `M`.
- `toSheafify_constantSheafCompRestrictionIso_inv_app`: the canonical map of the constant
  presheaf `M` over `X` to its sheafification, followed by the inverse at `M`, is the
  restriction (`whiskerLeft (ι P ρ).op`) of the canonical map of the constant presheaf `M`
  on the twisted site to its sheafification. By the universal property of sheafification
  this equation determines the inverse. Proof: Mathlib's
  `toSheafify_pullbackSheafificationCompatibility`.

For discrete sheaves, let additionally `R : Type w` be a commutative ring, `G` a
topological group, and `L` a local action system on the twisted site, with
`[HasSheafify J (ModuleCat.{w} R)]`,
`[HasSheafify (twistedTopology ρ J) (ModuleCat.{w} R)]`,
`[L.HasFiniteEquivariantRefinements (twistedTopology ρ J)]`, and the pointwise right Kan
extensions.

- `discreteConstantSheafCompRestrictionIso J R L :
  discreteConstantSheaf L (twistedTopology ρ J) R ⋙ discreteRestriction J R L ≅
  constantSheaf J (ModuleCat.{w} R)`: the same isomorphism, since `discreteConstantSheaf`
  followed by the inclusion of discrete sheaves is `constantSheaf` by definition.

## The quasi-étale case

Data and universes are those of `AnalyticQuasiEtaleConstant`: `K` a complete ultrametric
normed field, `X : LocalizedCategory.{u, v, v} (K := K)`, `G : Type z` a topological group
with `ρ : G →* Aut X` and `[Small.{w} G]` for `w = max u (v + 1) uL`, a commutative ring
`R : Type w`, and the published, unproved finite equivariant refinement condition
`[(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]`.
Declarations that do not take the field `L` are used with explicit universes
`.{u, v, uL}`.

- `quasiEtaleConstantSheafRestrictionIso ρ R :
  quasiEtaleConstantSheaf ρ R ⋙ quasiEtaleGSheafRestriction ρ R ≅
  constantSheaf (quasiEtaleTopology X) (ModuleCat.{w} R)`: Berkovich's `b^*` takes the
  constant quasi-étale `G`-sheaf `M` to the constant sheaf `M` on the quasi-étale site of
  `X`. It is `discreteConstantSheafCompRestrictionIso` for the twisted quasi-étale site.

The following also take the field `L : Type uL` with `[NormedAlgebra K L]`, the point
axioms `h`, and `[IsTopologicalGroup G]`, as in `AnalyticQuasiEtaleComparison`.

- `quasiEtaleConstantCompactComparison L ρ h R q`: the natural transformation
  `quasiEtaleConstantSheaf ρ R ⋙ quasiEtaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget
  ⟶ constantSheaf (quasiEtaleTopology X) _ ⋙ quasiEtaleCompactCohomology L h R q`. For a
  module `M`, this is the comparison `H^q_c(X{G}, M) → H^q_c(X, M)` for the constant sheaves
  `M`, with the action of `G` on the source forgotten. It is Berkovich's
  `quasiEtaleCompactComparison` whiskered by `quasiEtaleConstantSheaf`, followed by
  `H^q_c(X, -)` applied to `quasiEtaleConstantSheafRestrictionIso`.
- `quasiEtaleConstantCompactComparison_app`: its component at `M` is
  `(quasiEtaleCompactComparison L ρ h R q).app (constant G-sheaf M)` followed by
  `H^q_c(X, -)` of the component at `M` of `quasiEtaleConstantSheafRestrictionIso`.

Finally, with the hypotheses of the compact part of `AnalyticQuasiEtaleConstant`:

- `hℓ : IsSMulRegular R (ℓ : R)`;
- exactness of the quasi-étale Godement functor;
- `hpoints`, joint faithfulness of the fibre functors;
- a bound `D`, with `hF` (Godement sheaves are `Γ_{c,X{G}}`-acyclic) and `hC`
  (`H^n_c(X{G}, R / ℓ ^ m R) = 0` for `n > D`).

The declaration is:

- `quasiEtaleConstantCompactHomologyToPlain ρ R hℓ L h hpoints D hF hC m n`: the
  `R`-linear map
  `Hⁿ(Γ_{c,X{G}}(G^•_m)) → H^n_c(X, R / ℓ ^ m R)`. Its source is the cohomology of
  Harris's complex of level `m` for the constant system, with the action of `G` forgotten
  (`smoothForget`). Its target is the plain compactly supported cohomology of `X` with
  coefficients in the constant sheaf `R / ℓ ^ m R` of the quasi-étale site. It is Harris's
  (2.3) for the constant sheaves (`quasiEtaleConstantCompactHomologyIso`) followed by the
  component at `R / ℓ ^ m R` of `quasiEtaleConstantCompactComparison`.

## Original sources

- Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto
  Univ. 39 (1999), registered as
  `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, §2. Printed p.305
  (PDF p.7), the passage cited in `AnalyticQuasiEtale` and `AnalyticQuasiEtaleConstant`:
  "Lemma 2.2 bis. For each `m` the constant sheaf `ℤ/ℓ^mℤ` admits an `RΓ_c`-acyclic
  resolution of finite length [...] Thus Lemma 2.2 provides an isomorphism (2.3)
  `H^q_c(U(ẽ)_F̄, ℤ/ℓ^mℤ) ⥲ Z_m^q/B_m^q = H^q(G_m^•(U(ẽ)_F̄))`."
- Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished 1995–1996
  manuscript), registered as
  `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
  Corollary 1.5.2(i), printed pp.11–12, as cited in `AnalyticQuasiEtaleComparison`: "For
  any étale abelian sheaf F on X(G) there are canonical isomorphisms
  H^q_c(X{G}, F) ⥲ H^q_c(X, b^*F), [q] ≥ 0."

## Provenance and correspondence

- The left side of Harris's (2.3) is the compactly supported cohomology of `U(ẽ)` with
  coefficients in the constant sheaf `ℤ/ℓ^mℤ`. In the published framework, (2.3) is proved
  for `H^n_c(X{G}, -)` of constant quasi-étale `G`-sheaves. Berkovich's Corollary 1.5.2(i)
  passes to `H^n_c(X, b^*F)`. The identification of `b^*` of a constant `G`-sheaf with the
  constant sheaf of `X` is implicit in both sources. Here it is the general fact that
  restriction along a continuous and cocontinuous functor commutes with sheafification,
  applied to constant presheaves.
- `quasiEtaleConstantCompactHomologyToPlain` goes from Harris's complexes to plain
  cohomology, the inverse direction of Harris's (2.3). It is an isomorphism exactly when
  the comparison of Berkovich's Corollary 1.5.2(i) is an isomorphism at the constant sheaf
  `R / ℓ ^ m R`; this is not proved.
- As in `AnalyticQuasiEtaleComparison`, `X` carries its quasi-étale site, so
  `H^n_c(X, -)` is quasi-étale cohomology with supports in the `L`-valued points. For
  `R = ULift ℤ` the coefficients are `ℤ/ℓ^mℤ` up to an isomorphism that is not
  formalized (`AnalyticQuasiEtaleConstant`).

## Not formalized here

That the comparison maps `quasiEtaleConstantCompactComparison` and
`quasiEtaleConstantCompactHomologyToPlain` are isomorphisms (Berkovich's
Corollary 1.5.2(i)) is not proved. The comparison of quasi-étale with étale cohomology,
the spaces `U(ẽ)` and the groups `S(ẽ)` are not formalized here. The hypotheses inherited from
`AnalyticQuasiEtaleConstant` and `AnalyticQuasiEtaleComparison` remain hypotheses.
