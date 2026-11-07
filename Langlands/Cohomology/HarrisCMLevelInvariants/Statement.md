# Level invariants of CM cohomology at finite level

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition, `HarrisCMLevelInvariantsStatement`. It is
about the cohomology of the Library's geometric CM tower `U ↦ X̄_U` (module
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology`) with
coefficients in a diagram of étale sheaves over the tower. Take sufficiently
small levels `V ≤ U` with `V` normal in `U` and index `[U : V]` invertible in
the coefficient ring `R`. Then, in every degree, restriction from level `U` to
level `V` is injective, and its image is the set of classes fixed by the action
of `U` on the level-`V` cohomology. This is the finite-level comparison
`H^i(X_U) ≅ H^i(X_V)^{U/V}` that Harris and Taylor state on p.96 of III.2.
Nothing is proved here.

A companion statement, `HarrisCMColimitInvariantsStatement` (module
`Langlands.Cohomology.HarrisCMColimitInvariants.Statement`), states the
consequence for the colimit over all small levels.

## Objects

All arithmetic types live in `Type` (universe zero), as in the Library's
modules. The binders are copied from
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology`:

- number fields `E` (totally real) and `F` (totally complex CM, quadratic
  over `E`), the algebra `A` with its compatible `E`-, `F`- and
  `ℚ`-algebra structures, and `D : CentralSimpleUnitaryData E F A n`;
- an imaginary quadratic number field `L` with `[Algebra L F]`, an
  embedding `τ₀ : L →+* ℂ`, and the signature charts `C`;
- the named premises `preservation`, `composition`, `unitCoherence`,
  `associativity`, `comparison`, `symmetry`, `stability`, `square`,
  `universality`, `dualityNaturality`, `polarizationStability`,
  `compatibility`, `h : Global.RationalProfiniteIntegerAdeleComparison` and
  `htor : TorsionFiniteEtaleStatement.{0}`;
- the representability premise
  `q : CMRepresentabilityStatement D C ... h htor`;
- `existence : RelativeDualSchemeExistenceStatement.{0}`,
  `geometry : RelativeDualSchemeGeometryStatement.{0}`, coarse rigidity
  `hRigid` at every `U : SmallCMLevel D`, and
  `criterion : DominantUnramifiedEtaleStatement.{0}`. The Library uses these
  four in `cmSmallLevelTowerEtale` to prove that every transition map of the
  geometric tower is étale;
- a commutative ring `R : Type`.

### Proof status of the premises

The Lean definition keeps every premise as an explicit hypothesis, as the
Library's modules do. A premise being a parameter does not mean that it is
unproved. In Library commit `eec7519b852f9097606377425625fd5794c87f71`,
fourteen premise types have published proofs, so a user can pass these
theorems as the corresponding arguments. Check `88f571ea` (see the checks
below) confirms that each theorem, at universe zero, has the premise type.

| Premise | Type | Library theorem | Module |
| --- | --- | --- | --- |
| `preservation` | `pullbackTensorComparisonIsIsoStatement.{0}` | `Langlands.Scheme.Modules.pullbackTensorComparisonIsIso` | `Langlands.AlgebraicGeometry.Modules.PullbackTensorProof` |
| `composition` | `PullbackTensorCompositionStatement.{0}` | `Langlands.Scheme.Modules.pullbackTensorComposition` | `Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs` |
| `unitCoherence` | `PullbackTensorUnitCoherenceStatement.{0}` | `Langlands.Scheme.Modules.pullbackTensorUnitCoherence` | `Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs` |
| `associativity` | `ExplicitPullbackTensorAssociativityStatement.{0}` | `Langlands.Scheme.Modules.explicitPullbackTensorAssociativity` | `Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs` |
| `comparison` | `TensorMonoidalLeftUnitorComparisonStatement.{0}` | `Langlands.Scheme.Modules.tensorMonoidalLeftUnitorComparison` | `Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs` |
| `symmetry` | `PullbackTensorSymmetryStatement.{0}` | `Langlands.Scheme.Modules.pullbackTensorSymmetry` | `Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs` |
| `stability` | `PicardZeroPullbackStatement.{0}` | `Langlands.AbelianScheme.picardZeroPullback` | `Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof` |
| `universality` | `PicardZeroUniversalBaseChangeStatement.{0}` | `Langlands.AbelianScheme.picardZeroUniversalBaseChange` | `Langlands.AlgebraicGeometry.Picard.PicardZeroUniversalBaseChangeProof` |
| `dualityNaturality` | `DualAbelianBaseChangeNaturalityStatement.{0}` | `Langlands.AbelianScheme.dualAbelianBaseChangeNaturality` | `Langlands.AlgebraicGeometry.Picard.DualAbelianBaseChangeNaturalityProof` |
| `polarizationStability` | `PolarizationBaseChangeStatement.{0}` | `Langlands.AbelianScheme.polarizationBaseChange` | `Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeProof` |
| `compatibility` | `RelativeFiniteWeilTransitionStatement.{0}` | `Langlands.AbelianScheme.relativeFiniteWeilTransition` | `Langlands.AlgebraicGeometry.Picard.FiniteWeilTransitionProof` |
| `h` | `Global.RationalProfiniteIntegerAdeleComparison` | `Langlands.Global.rationalProfiniteIntegerAdeleComparison` | `Langlands.Global.RationalProfiniteIntegerComparisonProof` |
| `htor` | `TorsionFiniteEtaleStatement.{0}` | `Langlands.AbelianScheme.torsionFiniteEtale` | `Langlands.AbelianScheme.TorsionFiniteEtale` |
| `criterion` | `Langlands.AlgebraicGeometry.DominantUnramifiedEtaleStatement.{0}` | `Langlands.AlgebraicGeometry.DominantUnramifiedEtaleProof.dominantUnramifiedEtale` | `Langlands.AlgebraicGeometry.DominantUnramifiedEtaleProof` |

These proof modules are not imported here. Five premises have no proof in
that commit. The published statement
[HarrisCMLevelGaloisSmooth](../HarrisCMLevelGaloisSmooth/Statement.md)
records, for Library `ce52163e`, that no theorem there concludes any of these
types and how far each one is reduced. No new proof of these premises was
added between that commit and `eec7519b`; the added
`HarrisCMLevelGaloisSmooth.Statement` mentions all five but proves none.

- `square : MumfordBundlePicardZeroStatement.{0}`, which the Library derives
  only conditionally (`mumfordBundlePicardZero_of_cube`);
- `q : CMRepresentabilityStatement ...`, representability of the CM moduli
  problem;
- `existence : RelativeDualSchemeExistenceStatement.{0}` and
  `geometry : RelativeDualSchemeGeometryStatement.{0}`;
- `hRigid`, coarse rigidity at every small level. This is a condition on the
  levels, not a general theorem: the docstring of `CMGeometricCoarseRigidity`
  says that it "is not inferred from sufficiently small level".

Since `q` is unproved, the proposition is a statement about the objects that
any witness `q` produces. A proof must work for every such witness.

### Notation

Write `G = D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`, the group in which the
Library's levels live. An object `U : SmallCMLevel D` is a compact open
subgroup `U.obj.subgroup` of `G` that is sufficiently small
(`LevelSufficientlySmall`). A morphism `U ⟶ V` is an element `g` of `G` with
`g⁻¹ U g ⊆ V` (`CompactOpenLevel.Arrow`, module `Langlands.Shimura.Levels`).

- `X̄_U = (cmGeometricSchemeTower ... q).obj U`, the scheme at level `U`
  base changed to `Spec F̄`, `F̄ = AlgebraicClosure F`. The tower is a functor
  `SmallCMLevel D ⥤ Scheme`. `cmSmallLevelTowerEtale` proves that every
  transition map is étale.
- For `V ≤ U` (`hVU : V.obj.subgroup ≤ U.obj.subgroup`), the inclusion arrow
  is `smallCMInclusion D hVU : V ⟶ U`, with element `1`. Its tower map is
  `π = (cmGeometricSchemeTower ... q).map (smallCMInclusion D hVU) : X̄_V ⟶ X̄_U`.
- If moreover `V.obj.subgroup.subgroupOf U.obj.subgroup` is normal, then for
  `g ∈ U` the arrow `smallCMNormalInverseArrow D U V hVU g : V ⟶ V` has element
  `g⁻¹` (`smallCMNormalInverseArrow_element`). Its tower map is the deck map
  `σ_g : X̄_V ⟶ X̄_V`.
- A coefficient diagram `coeff : cmSmallLevelCoefficientDiagram ... R` is a
  `CoefficientDiagram R (cmGeometricSchemeTower ... q).op` (module
  `Langlands.Geometry.EtaleCohomologyDiagram`). It consists of a sheaf
  `coeff_U` of `R`-modules on the small étale site of each `X̄_U`, and, for
  every arrow `a : U ⟶ V` of levels, a morphism of sheaves
  `coeff.map a.op : (restriction f_a) coeff_V ⟶ coeff_U`, where
  `f_a : X̄_U ⟶ X̄_V` is the tower map of `a` and `restriction f_a` is
  restriction along the étale map `f_a`, that is pullback. These morphisms
  satisfy the identity and composition laws. No morphism is assumed to be an
  isomorphism.
- `cmSmallLevelTrivialCoefficients ... R coeff` is the Library's
  `IsLevelTrivialCoefficients`. For each level `K` and `k ∈ K`, the self-arrow
  `⟨k⟩ : K ⟶ K` acts on `X̄_K` as the identity
  (`cmGeometricSchemeTower_map_eq_id_of_mem`). The property requires that
  `coeff.map ⟨k⟩.op` is the identity coefficient map, transported along that
  equality of scheme maps.
- `H^d(X̄_U, coeff_U) = (cmSmallLevelCohomology ... R coeff d).obj (op U)`.
  This is the `d`-th right derived functor of global sections on
  `Sheaf (Scheme.smallEtaleTopology X̄_U) (ModuleCat.{0} R)`, computed with
  injective resolutions (Worker 13's `EtaleDerivedSections`). For an arrow
  `a`, `(cmSmallLevelCohomology ... R coeff d).map a.op` is
  `cohomologyMapWithCoefficients f_a R d (coeff.map a.op)`: the pullback map
  `cohomologyMap f_a R d` followed by the map induced by `coeff.map a.op`.
- Write `res = (cmSmallLevelCohomology ... R coeff d).map (smallCMInclusion D hVU).op :
  H^d(X̄_U, coeff_U) ⟶ H^d(X̄_V, coeff_V)` and
  `T_g = (cmSmallLevelCohomology ... R coeff d).map (smallCMNormalInverseArrow D U V hVU g).op`,
  an endomorphism of `H^d(X̄_V, coeff_V)`.

## The proposition

```lean
def HarrisCMLevelInvariantsStatement : Prop :=
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  ∀ (coeff : coefficients), trivialCoefficients coeff →
    ∀ (U V : SmallCMLevel D) (hVU : V.obj.subgroup ≤ U.obj.subgroup)
      [(V.obj.subgroup.subgroupOf U.obj.subgroup).Normal],
      IsIso (coeff.map (smallCMInclusion D hVU).op) →
      IsUnit ((V.obj.subgroup.subgroupOf U.obj.subgroup).index : R) →
      ∀ d : ℕ,
        Function.Injective ((levelCohomology coeff d).map (smallCMInclusion D hVU).op).hom ∧
        Set.range ((levelCohomology coeff d).map (smallCMInclusion D hVU).op).hom =
          {y | ∀ g : U.obj.subgroup,
            ((levelCohomology coeff d).map
              (smallCMNormalInverseArrow D U V hVU g).op).hom y = y}
```

`geometricSchemes`, `towerEtale`, `coefficients`, `trivialCoefficients` and
`levelCohomology` are local notations for `cmGeometricSchemeTower`,
`cmSmallLevelTowerEtale`, `cmSmallLevelCoefficientDiagram`,
`cmSmallLevelTrivialCoefficients` and `cmSmallLevelCohomology`, applied to all
binders. The `letI` supplies the étaleness instance that the coefficient
diagram needs, as in the Library's own definitions. The definition has no
universe parameters.

In words: let `coeff` be a level-trivial coefficient diagram, and let `V ≤ U` be
small levels with `V` normal in `U`. Suppose that the transition map
`π^* coeff_U ⟶ coeff_V` along the inclusion is an isomorphism and that the
index `[U : V]` (`Subgroup.index`, finite because `V` is open and `U` is
compact) is a unit of `R`. Then for every degree `d`, `res` is injective and its
image is `{y | T_g y = y for all g ∈ U}`.

There are three hypotheses on the coefficients:

- *Level triviality.* It is needed for the image to consist of invariants.
  The arrows satisfy `⟨g⁻¹⟩_V ≫ incl = incl ≫ ⟨g⁻¹⟩_U` (both have element
  `g⁻¹`), so `T_g ∘ res` is `res` composed with the operator of the self-arrow
  `⟨g⁻¹⟩_U` on `H^d(X̄_U, coeff_U)`. Level triviality makes that operator the
  identity. Check `6773df61` (below) proves this inclusion of the image in
  the invariants in Lean.
- *Cartesian transition along `V ≤ U`.* Without it, `coeff_V` is not
  determined by `coeff_U`, and the invariants of `H^d(X̄_V, coeff_V)` have no
  reason to come from level `U`.
- *Invertible index.* Harris and Taylor work over `ℚ_ℓ^ac`. With torsion
  coefficients the comparison fails in general: for the trivial coefficient
  `ℤ/p` and a connected Galois cover of degree `p`, restriction in degree one is
  not injective.

## Why the statement is expected to hold

This argument is derived. It combines the trace morphism of SGA 4 IX 5.1 with
Library facts; neither source states it in this form. Fix `coeff`, `U`, `V`,
`d` as in the proposition. Let `Γ = U/V`, the Library's
`SmallCMResidualGroup D U V`, of order `N = [U : V]`, a unit of `R`.

1. *`π` is a finite étale `Γ`-torsor with deck maps `σ_g`.* Worker 57's
   module `Langlands.Shimura.PEL.HarrisTaylorCMGeometricNormalActions` defines
   the action `cmGeometricNormalQuotientAction ... U V hVU` of `Γ` on `X̄_V`.
   `cmGeometricNormalQuotientAction_mk` proves, by `rfl`, that the class of
   `g ∈ U` acts by `σ_g`, the tower map of `smallCMNormalInverseArrow D U V hVU g`.
   `cmGeometricNormalProjection_invariant` gives `σ_g ≫ π = π`. Worker 57's
   theorem `cmGeometricNormalEtaleAction_isFiniteGeometricTorsor_of_dominantCriterion`
   (module `Langlands.Shimura.PEL.HarrisTaylorCMGeometricNormalTorsor`) proves,
   from the premises above, `IsFiniteGeometricTorsor` for this action
   (`Langlands.Shimura.Coefficients.Etale`). That is: `π` is étale (the action
   lives in the small étale site of `X̄_U`), finite and surjective, and `Γ`
   acts simply transitively on the geometric points of each fiber. Hence (this
   step is derived) every geometric fiber of `π` has exactly `N` points, and
   the map `Γ × X̄_V ⟶ X̄_V ×_{X̄_U} X̄_V`, `(γ, y) ↦ (σ_γ y, y)`, is an
   isomorphism. It is a morphism of finite étale `X̄_V`-schemes that is
   bijective on geometric points.
2. *The operators `T_g` are the deck-transformation operators.* Write
   `F = coeff_U` and `φ = coeff.map (smallCMInclusion D hVU).op : π^* F ⟶ coeff_V`,
   an isomorphism by hypothesis. By definition, `res` is the pullback
   `π^♯ : H^d(X̄_U, F) ⟶ H^d(X̄_V, π^* F)` followed by `H^d(φ)`. In the level
   category, `⟨g⁻¹⟩_V ≫ incl = incl ≫ ⟨g⁻¹⟩_U` (the Lean lemma
   `inverseArrow_comp_inclusion` of check `6773df61`). The composition law of
   `coeff` for both factorizations, together with level triviality at `U`,
   gives `coeff.map ⟨g⁻¹⟩_V.op ∘ σ_g^*(φ) = φ ∘ c_g`. Here
   `c_g : σ_g^* π^* F ≅ (σ_g ≫ π)^* F = π^* F` is the canonical isomorphism
   (`diagramRestrictionComp` and `restrictionCongr`). So `H^d(φ)` carries the
   canonical operator `σ_g^♯ = H^d(c_g) ∘ (cohomologyMap σ_g R d)` of the deck
   transformation `σ_g` on `H^d(X̄_V, π^* F)` to `T_g`. It therefore suffices
   to show that `π^♯` is injective with image the classes fixed by all
   `σ_g^♯`.
3. *Trace (SGA 4 IX 5.1).* For a finite étale cover `π` and a sheaf `F` on
   `X̄_U`, SGA 4 IX 5.1 defines the restriction morphism `F ⟶ π_* π^* F`. Since
   `π` is finite, `H^q(X̄_U, π_* π^* F) ≅ H^q(X̄_V, π^* F)`, which gives the
   restriction map (5.1.1). SGA 4 IX 5.1 also defines the trace morphism
   `tr : π_* π^* F ⟶ F` (5.1.2) and its map on cohomology (5.1.3). The trace is
   characterized by (i) it is local for the étale topology, and (ii) for `X'`
   the disjoint sum of `d` copies of `X`, it is the sum map `F^d ⟶ F`. By
   (5.1.4), `tr ∘ res` is multiplication by the local degree of `π`. Here the
   degree is `N` everywhere (step 1), so `tr ∘ π^♯ = N` on `H^d(X̄_U, F)`. Since
   `N` is a unit, `π^♯` is injective. The restriction map of SGA 4 agrees with
   the Library's `cohomologyMap π R d`. Both are morphisms of δ-functors in
   `F` that agree in degree zero, and the source is universal (Tôhoku
   Proposition 2.2.1); restriction along the étale `π` is exact and preserves
   injectives (module `Langlands.Geometry.EtaleDerivedPullback`). This
   identification is derived.
4. *Invariant classes come from level `U`.* On `π_* π^* F`, the endomorphism
   `res ∘ tr` equals `Σ_{γ ∈ Γ} (γ)`, the sum of the automorphisms induced by
   the deck maps. By (i), it suffices to check this after base change along an
   étale cover of `X̄_U`, and `π` itself is one. By step 1, after this base
   change `π` becomes the projection from `N` copies of `X̄_V`, permuted by `Γ`.
   Then `π_* π^* F` becomes `F^N`, `res` is the diagonal and `tr` is the sum
   (ii), so `res ∘ tr` sends `(x_γ)` to the constant family `Σ_γ x_γ`, which is
   the sum of the permutations. On cohomology, `π^♯ ∘ tr = Σ_{γ ∈ Γ} σ_γ^♯`.
   If `y` is fixed by every `σ_g^♯`, then `π^♯(tr y) = N y`, so
   `y = π^♯(N⁻¹ tr y)` lies in the image of `π^♯`. With step 2, and the
   inclusion of the image in the invariants proved in Lean, this gives the
   proposition. This step is derived from (i) and (ii) of SGA 4 IX 5.1.

Nothing here uses finiteness of the sheaves, the degree `d`, or any property of
`R` beyond invertibility of `N`.

## Provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p.96, read on a rendered image of the page
because the text layer omits the displays. For sufficiently small open compact
subgroups `U` of `G(A^∞)` they construct lisse étale `ℚ_ℓ^ac`-sheaves `L_ξ` on
`X_U`. For `g ∈ G(A^∞)` and `g⁻¹ V g ⊂ U` they construct morphisms
`g : H^i_et(X_U ×_F F^ac, L_ξ) ⟶ H^i_et(X_V ×_F F^ac, L_ξ)`. They then write:
"If `V ⊂ U` then we see that
`H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`."

The proposition is this isomorphism, for the Library's objects:

- `V` is normal in `U`, so that `U/V` is a group. Since the action of `V` on
  `H^d(X̄_V, coeff_V)` is trivial by level triviality, invariance under `U` is
  invariance under `U/V`.
- The isomorphism is the restriction map, the map of the arrow
  `V ⟶ U` with element `1`, which is the map Harris and Taylor construct for
  `g = 1`.
- The coefficients are any level-trivial diagram of `R`-module sheaves whose
  transition along `V ≤ U` is an isomorphism, not the sheaves `L_ξ`. The
  coefficient ring is any commutative ring in which `[U : V]` is a unit, not
  `ℚ_ℓ^ac`.
- The levels are the Library's Harris–Taylor CM PEL levels, conditional on the
  premises above.

| Lean | Source |
| --- | --- |
| `(levelCohomology coeff d).map (smallCMInclusion D hVU).op` | the map `g` of Harris–Taylor p.96 for `g = 1` |
| `{y \| ∀ g : U.obj.subgroup, T_g y = y}` | `H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`, Harris–Taylor p.96 |
| injective, with that image | "`≅`", Harris–Taylor p.96; truth from SGA 4 IX 5.1 |
| `IsUnit ((V.obj.subgroup.subgroupOf U.obj.subgroup).index : R)` | Harris–Taylor's coefficients are `ℚ_ℓ^ac`-vector spaces |

Neither source states the proposition with these hypotheses.

## Scope

The statement does not cover:

- the colimit over all small levels; that is the companion statement
  `HarrisCMColimitInvariantsStatement`;
- non-normal `V ⊂ U`, or the maps attached to `g ∉ U`;
- the sheaves `L_ξ`, ℓ-adic coefficients or limits over torsion coefficients;
- Hecke operators, compact supports, admissibility, or local-global
  compatibility;
- a proof of any premise. The open premises `square`, `q`, `existence`,
  `geometry` and `hRigid` stay open, and the proved ones are not
  instantiated here.

## Registered sources

- `harris-taylor-2001-geometry-cohomology-simple-shimura`: Harris–Taylor
  2001, PDF SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`
  (printed page = PDF page - 8); III.2, printed p.96 (PDF p.104), read on a
  rendered image. Provenance.
- `sga4-1973-tome3-deligne-xvii-original-scan`: SGA 4 Tome 3, Lecture Notes in
  Mathematics 305, original scan, PDF SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`. Exposé IX
  (Artin), §5 "La méthode de la trace", 5.1 with (5.1.1)-(5.1.4) and
  Corollaire 5.2, printed pp.36-38 (PDF pp.39-41; PDF page = printed page + 3
  in this exposé), read on rendered images of the scanned pages. Used only in
  the truth argument.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), SHA-256
  `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
  Proposition 2.2.1, printed p.141 (PDF p.23). Used only in the truth
  argument.

## Formal dependencies and checks

Direct project imports, in Library commit
`eec7519b852f9097606377425625fd5794c87f71` and the workspace:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology` | Library (no Author line) | `9348395d2f5acbdf1856b569010a2aa79c1fcfd7395a88f2b36e7b93ab560af8` | `13c08eb11012cbe385fd3a316fafa8fb12d7ef3a819a86389b6250f324e41e61` |
| `Langlands.Shimura.PEL.HarrisTaylorCMNormalActions` | Library (no Author line) | `e9433447a4a96d4f4c287ef26be0ab1752bed20b8c7e2737a4db002d652174d2` | `82b0dbc1e512aab98c7912dbace2eb087dd99357dcb375384dd86900394e9910` |

Through these imports the module uses `HarrisTaylorCMSmallLevelIndex`
(Author: Worker 57) for `SmallCMLevel`; `EtaleDerivedSections` (Author:
Worker 13) for the cohomology; and the Library modules
`HarrisTaylorCMHeckeSchemes` (`smallCMInclusion`), `EtaleCohomologyDiagram`
(`CoefficientDiagram`), `RestrictedLevelTowerCohomology`
(`IsLevelTrivialCoefficients`) and `EtaleDerivedPullback`
(`cohomologyMapWithCoefficients`), whose Markdown files have no Author line.
The truth argument cites `HarrisTaylorCMGeometricNormalActions` and
`HarrisTaylorCMGeometricNormalTorsor` (Author: Worker 57), which are not in
the import closure of this module, and `Langlands.Shimura.Coefficients.Etale`
(Author: Worker 57), which is.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks against Library `eec7519b`, all on the final Lean file (SHA-256
`12ae07052e246441424ca1578519b405baf8d2fa5874bc23d61a419ace54f3b3`). None reported errors or warnings.

- `97938dd2-0df7-4490-bbfb-651027237eaf` built the file from a draft
  directory and inspected `HarrisCMLevelInvariantsStatement`: a
  `Prop`-valued definition with no universe parameters, depending only on
  `propext`, `Classical.choice` and `Quot.sound` (type hash
  `3ad5af95f6f5d54ad0235fee8d51eec72df261e55ca929c4d0ecc590ca9703b8`).
- `6773df61-f66e-4af8-83b3-8c34c0f0f376` compiled a test file
  (`Langlands/Inspect/CMLevelInvariantsPrint.lean`, SHA-256
  `0a2bf3ffa1d7e1a5adc2dfc5a6e6a478caa7a4f3a21f76d26d506ea048b04134`), not part
  of the candidate, against this file and the companion statement. It printed
  both definitions with universes and proved two lemmas, both depending only on
  the three standard axioms:
  - `inverseArrow_comp_inclusion`:
    `smallCMNormalInverseArrow D U V hVU g ≫ smallCMInclusion D hVU =
    smallCMInclusion D hVU ≫ restrictedSelfArrow small U (g⁻¹) _`;
  - `restrict_invariant`: for level-trivial `coeff`, `T_g (res x) = res x`
    for every `x` and every `g ∈ U`. This is the inclusion of the image of
    `res` in the invariants.
- `88f571ea-ab8f-40d6-8edd-403fa3f86d75` compiled a test file
  (`Langlands/Inspect/CMLevelInvariantsPremises.lean`, SHA-256
  `b7bcb2ead3df306593f0fdd14577c0cfed3eaf7e7fcd8ca3489cc706b3fa1809`)
  against this file. For each of the fourteen proved premises in the table
  above, an `example` with the premise type at universe zero is closed by the
  cited theorem. `#print axioms` shows that each theorem depends only on
  `propext`, `Classical.choice` and `Quot.sound`.
- `633ed74f-b170-4256-a7c1-a5500f464416` built the file with Lake from the workspace and inspected
  `HarrisCMLevelInvariantsStatement`, with the same result and the same type hash.

This establishes a well-formed statement. It does not prove it.
