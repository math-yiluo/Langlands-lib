# Level invariants of CM cohomology over all small levels

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition, `HarrisCMColimitInvariantsStatement`. It is
about the colimit, over all sufficiently small CM levels, of the cohomology of
the Library's geometric CM tower `U ↦ X̄_U` (module
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology`), with its smooth
action of the finite-adelic group. Let `R` be a `ℚ`-algebra, and let the
coefficients be a level-trivial diagram of étale sheaves whose transition maps
are isomorphisms. Then at every small level `U` and in every degree, the map
from level-`U` cohomology to the colimit is injective, and its image is the
set of `U`-invariant classes. Harris and Taylor deduce admissibility of
`H^i(X, L_ξ)` from their finite-level comparison on p.96 of III.2; the
proposition is the step in between. Nothing is proved here.

The companion statement `HarrisCMLevelInvariantsStatement` (module
`Langlands.Cohomology.HarrisCMLevelInvariants.Statement`) is the finite-level
comparison. The truth argument below derives this proposition from it.

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
- a commutative ring `R : Type` with `[Algebra ℚ R]`.

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
types and how far each one is reduced. No Lean file added or edited between
that commit and `eec7519b` mentions any of the five types.

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
- The colimit is that of `RestrictedLevelColimit.diagram (cmSmallLevelCohomology ... R coeff d)`,
  the restriction of `cmSmallLevelCohomology ... R coeff d` to
  `(OrderedSmallCMLevel D)ᵒᵖ`, the small levels ordered by inclusion with the
  inclusion arrows. `cmSmallLevelCohomologyDiagram_eq_restricted` identifies it
  with the Library's `cmSmallLevelCohomologyDiagram`. Write
  `ι_U = RestrictedLevelColimit.ι (cmSmallLevelCohomology ... R coeff d) U` for
  the colimit insertion at `U`.
- For level-trivial `coeff` with witness `hcoeff`,
  `cmSmallLevelSmoothCohomology ... R coeff hcoeff d` is the Library's smooth
  representation of `G` on this colimit
  (`RestrictedLevelTowerCohomology.smoothColimitCohomology`). Its operator
  `ρ u` is, definitionally, `RestrictedLevelColimit.translate u`; the lemma
  `colimit_invariant` of check `6773df61` uses this.
  `cmSmallLevelSmoothCohomology_action` proves that `ρ u (ι_K x)` is
  `ι_{uKu⁻¹}` of the image of `x` under the map of the arrow
  `restrictedConjArrow small u K : uKu⁻¹ ⟶ K`, whose element is `u`.

## The proposition

```lean
def HarrisCMColimitInvariantsStatement [Algebra ℚ R] : Prop :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  ∀ (coeff : coefficients) (hcoeff : trivialCoefficients coeff),
    (∀ {i j : (SmallCMLevel D)ᵒᵖ} (a : i ⟶ j), IsIso (coeff.map a)) →
    ∀ (d : ℕ) (U : SmallCMLevel D),
      Function.Injective (RestrictedLevelColimit.ι (levelCohomology coeff d) U).hom ∧
      Set.range (RestrictedLevelColimit.ι (levelCohomology coeff d) U).hom =
        {z | ∀ u ∈ U.obj.subgroup,
          (cmSmallLevelSmoothCohomology D C preservation composition unitCoherence
            associativity comparison symmetry stability square universality dualityNaturality
            polarizationStability compatibility h htor q existence geometry hRigid criterion
            R coeff hcoeff d).obj.ρ u z = z}
```

`geometricSchemes`, `towerEtale`, `coefficients`, `trivialCoefficients` and
`levelCohomology` are local notations for `cmGeometricSchemeTower`,
`cmSmallLevelTowerEtale`, `cmSmallLevelCoefficientDiagram`,
`cmSmallLevelTrivialCoefficients` and `cmSmallLevelCohomology`, applied to all
binders. The three `letI` lines supply instances that the Library's
`cmSmallLevelSmoothCohomology` and `cmSmallLevelSmoothCohomology_action` also
supply: finiteness of `F` and `A` over `ℚ` (needed for the instances saying
that sufficiently small levels are closed under shrinking and conjugation),
and étaleness of the tower maps. The definition has no universe parameters.

In words: let `R` be a `ℚ`-algebra and `coeff` a level-trivial coefficient
diagram all of whose transition maps `coeff.map a` are isomorphisms. Then for
every degree `d` and every small level `U`, `ι_U` is injective, and its image is
the set of classes `z` of the colimit with `ρ u z = z` for all `u ∈ U`.

The hypotheses:

- *Level triviality* is needed for the colimit to carry the smooth action at
  all (`cmSmallLevelSmoothCohomology` takes the witness `hcoeff`), and for
  classes from level `U` to be `U`-invariant. Check `6773df61` (below) proves
  this inclusion of the image in the invariants in Lean.
- *Cartesian coefficients.* The finite-level comparison needs the transition
  along each inclusion `W ≤ U` to be an isomorphism; the proposition assumes
  it for all arrows, the usual condition on a coefficient system on the tower.
- *`ℚ`-algebra.* The argument uses levels `W ≤ U` of arbitrarily large index,
  so all these indices must be units of `R`. Harris and Taylor work over
  `ℚ_ℓ^ac`, a `ℚ`-algebra. For torsion coefficients with index prime to the
  characteristic, the finite-level statement applies.

## Why the statement is expected to hold

This argument is derived from the finite-level statement
`HarrisCMLevelInvariantsStatement` and elementary facts about filtered
colimits; neither source states it in this form. Fix `coeff`, `d` and `U` as in
the proposition. Write `res_{K→K'}` for the map of the inclusion arrow
`K' ⟶ K` (element `1`), and `⟨g⟩^♯` for the map of an arrow `K ⟶ K` with
element `g`.

1. *Preliminaries.* Sufficiently small levels are closed under shrinking and
   conjugation (the instances `sufficientlySmall_isDownwardClosed` and
   `sufficientlySmall_isConjStable`). The ordered small levels are therefore
   cofiltered, so the colimit is filtered: `ι_K x = 0` if and only if
   `res_{K→K'} x = 0` for some small `K' ≤ K`, and `ι_K x = ι_K x'` if and only
   if `x` and `x'` agree after restriction to some small `K' ≤ K`.
   `cmSmallLevelCohomology_exists_level_class` proves that every class is
   `ι_K y` for some `K` and `y` (a small level exists here, namely `U`). For a
   small `W ≤ U`, the core `W° = ⋂_{u ∈ U} u W u⁻¹` is a finite intersection,
   because `W` is open and `U` is compact. So `W°` is a compact open subgroup,
   normal in `U` and contained in `W`, hence a small level. Its index in `U` is
   a positive integer, hence a unit of the `ℚ`-algebra `R`. Inclusion arrows
   compose to inclusion arrows (element `1 · 1 = 1`), so
   `res_{U→W°} = res_{W→W°} ∘ res_{U→W}`. By hypothesis,
   `coeff.map (smallCMInclusion D _).op` is an isomorphism. So the finite-level
   statement applies to `W° ≤ U`.
2. *Injectivity.* If `ι_U x = 0`, then `res_{U→W} x = 0` for some small
   `W ≤ U`, so `res_{U→W°} x = 0`, and `x = 0` by injectivity in the
   finite-level statement.
3. *The image consists of invariants.* This is the Lean lemma
   `colimit_invariant` of check `6773df61`, proved with
   `RestrictedLevelColimit.translate_ι_apply_of_mem` and level triviality.
4. *Invariants come from level `U`.* Let `z` be fixed by every `u ∈ U`. Write
   `z = ι_K y`. Replacing `K` by the core in `U` of `K ⊓ U` and `y` by its
   restriction, we may assume that `K ≤ U` is normal in `U`. For `u ∈ U`,
   `uKu⁻¹ = K` as subgroups, hence as levels, and after this identification
   the arrow `restrictedConjArrow small u K` is the arrow `K ⟶ K` with element
   `u`. So `ρ u z = ι_K (⟨u⟩^♯ y)` (by `cmSmallLevelSmoothCohomology_action`),
   and `ρ u z = z` gives a small `K_u ≤ K` with
   `res_{K→K_u}(⟨u⟩^♯ y) = res_{K→K_u} y`. For `k ∈ K`, the arrow with element
   `uk` is `⟨u⟩ ≫ ⟨k⟩`, and `⟨k⟩^♯` is the identity by level triviality, so
   `⟨uk⟩^♯ y = ⟨u⟩^♯ y`: it depends only on the coset `uK`. Let `W` be the
   core in `U` of the intersection of the `K_u` over finitely many coset
   representatives `u`.
   Then `y_W = res_{K→W} y` satisfies `res_{K→W}(⟨u⟩^♯ y) = y_W` for all
   `u ∈ U`. For `g ∈ U`, the arrows satisfy `⟨g⁻¹⟩_W ≫ incl = incl ≫ ⟨g⁻¹⟩_K`
   (element `g⁻¹` on both sides), so
   `⟨g⁻¹⟩_W^♯ y_W = res_{K→W}(⟨g⁻¹⟩_K^♯ y) = y_W`. By the finite-level
   statement for `W ≤ U`, `y_W = res_{U→W} x` for some `x`. Then
   `ι_U x = ι_W (res_{U→W} x) = ι_W y_W = ι_K y = z`.

Nothing here uses finiteness of the sheaves or the degree `d`.

## Provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2. On printed p.96, read on a rendered image of the
page because the text layer omits the displays, they set
"`H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`" over sufficiently small
open compact subgroups `U` of `G(A^∞)`, and state: "If `V ⊂ U` then we see
that `H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`." On
printed p.97 (text layer) they continue: "Thus `H^i(X, L_ξ)` becomes an
admissible `G(A^∞)`-module". The admissibility uses
`H^i(X, L_ξ)^U ≅ H^i_et(X_U ×_F F^ac, L_ξ)`, which Harris and Taylor do not
display; the proposition is this isomorphism, for the Library's objects:

- the colimit is the Library's colimit over small CM PEL levels, conditional
  on the premises above, with its smooth action of `G`;
- the coefficients are any level-trivial cartesian diagram of sheaves of
  modules over a `ℚ`-algebra `R`, not the sheaves `L_ξ` over `ℚ_ℓ^ac`.

| Lean | Source |
| --- | --- |
| colimit over `(OrderedSmallCMLevel D)ᵒᵖ` of `H^d(X̄_U, coeff_U)` | `lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`, Harris–Taylor p.96, as constructed in the Library |
| `ι_U` injective with image `{z \| ∀ u ∈ U, ρ u z = z}` | `H^i(X, L_ξ)^U ≅ H^i_et(X_U ×_F F^ac, L_ξ)`, used for admissibility on p.97; derived from the p.96 comparison |
| `[Algebra ℚ R]` | Harris–Taylor's coefficients are `ℚ_ℓ^ac`-vector spaces |

Neither source states the proposition as a separate result.

## Scope

The statement does not cover:

- admissibility itself (finite generation of the invariants), which needs
  finiteness of the level-`U` cohomology;
- coefficient rings that are not `ℚ`-algebras; for those, the finite-level
  statement is the available form;
- the sheaves `L_ξ`, ℓ-adic coefficients or limits over torsion coefficients;
- Hecke operators, compact supports, or local-global compatibility;
- a proof of any premise. The open premises `square`, `q`, `existence`,
  `geometry` and `hRigid` stay open, and the proved ones are not
  instantiated here.

## Registered sources

- `harris-taylor-2001-geometry-cohomology-simple-shimura`: Harris–Taylor
  2001, PDF SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`
  (printed page = PDF page - 8); III.2, printed p.96 (PDF p.104), read on a
  rendered image, and p.97 (PDF p.105), read in the text layer. Provenance.

The truth argument uses no further source: it is derived from the
finite-level statement, whose Markdown cites SGA 4 IX 5.1.

## Formal dependencies and checks

Direct project import, in Library commit
`eec7519b852f9097606377425625fd5794c87f71` and the workspace:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelCohomology` | Library (no Author line) | `9348395d2f5acbdf1856b569010a2aa79c1fcfd7395a88f2b36e7b93ab560af8` | `13c08eb11012cbe385fd3a316fafa8fb12d7ef3a819a86389b6250f324e41e61` |

Through it the module uses `HarrisTaylorCMSmallLevelIndex` (Author: Worker
57) for `SmallCMLevel` and `OrderedSmallCMLevel`; `EtaleDerivedSections`
(Author: Worker 13) for the cohomology; and the Library modules
`RestrictedLevelColimit` (`ι`, `translate`), `RestrictedLevelTowerCohomology`
(`IsLevelTrivialCoefficients`, `smoothColimitCohomology`) and
`EtaleCohomologyDiagram` (`CoefficientDiagram`), whose Markdown files have no
Author line. It does not import the companion finite-level module.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks against Library `eec7519b`, all on the final Lean file (SHA-256
`2294b0d1f6197d0d22c36d13f915345877fc6b10bdb0a1052846d623168ec773`). None reported errors or warnings.

- `1e9052c7-ef2e-4c67-a18e-2cbb28876aff` built the file from a draft
  directory and inspected `HarrisCMColimitInvariantsStatement`: a
  `Prop`-valued definition with no universe parameters, depending only on
  `propext`, `Classical.choice` and `Quot.sound` (type hash
  `933dcfb8826c61e7e3272f8beaf9a441f4160bccbab82547383005574835d1cc`).
- `6773df61-f66e-4af8-83b3-8c34c0f0f376` compiled a test file
  (`Langlands/Inspect/CMLevelInvariantsPrint.lean`, SHA-256
  `0a2bf3ffa1d7e1a5adc2dfc5a6e6a478caa7a4f3a21f76d26d506ea048b04134`), not part
  of the candidate, against this file and the finite-level statement. It
  printed both definitions with universes and proved `colimit_invariant`:
  for level-trivial `coeff`, `u ∈ U` and `x` at level `U`,
  `ρ u (ι_U x) = ι_U x`. This is the inclusion of the image in the invariants.
  It depends only on the three standard axioms.
- `88f571ea-ab8f-40d6-8edd-403fa3f86d75` compiled a test file
  (`Langlands/Inspect/CMLevelInvariantsPremises.lean`, SHA-256
  `b7bcb2ead3df306593f0fdd14577c0cfed3eaf7e7fcd8ca3489cc706b3fa1809`)
  against this file. For each of the fourteen proved premises in the table
  above, an `example` with the premise type at universe zero is closed by the
  cited theorem. `#print axioms` shows that each theorem depends only on
  `propext`, `Classical.choice` and `Quot.sound`.
- `f11e8712-cfda-488c-af98-528da8c41ce9` built the file with Lake from the workspace and inspected
  `HarrisCMColimitInvariantsStatement`, with the same result and the same type hash.

This establishes a well-formed statement. It does not prove it.
