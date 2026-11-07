# Prime-to-`m` CM cohomology as level invariants

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition, `HarrisCMPrimeToInvariantsStatement`.
It is about the Library's prime-to-`m` cohomology of the geometric CM tower
(module `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`). Fix `m ≠ 0`
and a level `K₀` at the places dividing `m`. The Library forms the colimit,
over the prime-to-`m` levels `K'`, of the cohomology at the levels
`e⁻¹ (K₀ × K')`. It also defines a comparison map from this colimit to the
colimit over all sufficiently small levels. The proposition says: let `R` be
a `ℚ`-algebra, and let the coefficients be a level-trivial diagram of étale
sheaves whose transition maps are isomorphisms. Then in every degree the
comparison is injective, and its image is the set of classes fixed by `K₀`.
In the usual notation this is `H^d(Sh_{K₀}) = H^d(Sh)^{K₀}`, where
`Sh_{K₀}` is the tower with the level at `m` fixed to `K₀`. Nothing is
proved here.

The published statement `HarrisCMColimitInvariantsStatement` (module
`Langlands.Cohomology.HarrisCMColimitInvariants.Statement`) is the same
assertion for one small level `U`. The truth argument below derives this
proposition from it.

## Objects

All arithmetic types live in `Type` (universe zero), as in the Library's
modules. The binders are copied from
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`:

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

The integer `m`, the proof `hm : m ≠ 0`, the level `K₀`, the coefficients
and the degree are quantified inside the proposition.

### Proof status of the premises

The Lean definition keeps every premise as an explicit hypothesis, as the
Library's modules do. A premise being a parameter does not mean that it is
unproved. In Library commit `7e84f6ad2a2083a26977b5113dd0ab93f3f3b0ed`,
fourteen premise types have published proofs, so a user can pass these
theorems as the corresponding arguments. Check `abbebec9` (see the checks
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
that commit:

- `square : MumfordBundlePicardZeroStatement.{0}`, which the Library derives
  only conditionally (`mumfordBundlePicardZero_of_cube`);
- `q : CMRepresentabilityStatement ...`, representability of the CM moduli
  problem;
- `existence : RelativeDualSchemeExistenceStatement.{0}` and
  `geometry : RelativeDualSchemeGeometryStatement.{0}`;
- `hRigid`, coarse rigidity at every small level. This is a condition on the
  levels, not a general theorem: the docstring of `CMGeometricCoarseRigidity`
  says that it "is not inferred from sufficiently small level".

The published statement
[HarrisCMLevelGaloisSmooth](../HarrisCMLevelGaloisSmooth/Statement.md)
records, for Library `ce52163e`, that no theorem there concludes any of these
five types and how far each one is reduced. Between `eec7519b` and
`7e84f6ad`, the Lean files that mention any of the five types are the two
published invariants statements and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology` and
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`. All four use
them only as binders, and none concludes them.

Since `q` is unproved, the proposition is a statement about the objects that
any witness `q` produces. A proof must work for every such witness.

### Notation

Write `G = D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`, the group in which the
Library's levels live. An object `U : SmallCMLevel D` is a compact open
subgroup `U.obj.subgroup` of `G` that is sufficiently small
(`LevelSufficientlySmall`: for some finite place `v` of `ℚ`, every element of
`U` whose image in the `ℚ_v`-points has finite order has trivial image there).

- *The splitting.* `e = cmPrimeToSplit D m hm` is the Library's
  isomorphism of topological groups
  `G ≃ₜ* (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ × (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`.
  The first factor is the group of points over `∏_{v ∣ m} ℚ_v`, the second
  the group of points over the prime-to-`m` finite adeles; `e` comes from the
  corresponding splitting of the finite adeles of `ℚ`
  (`finiteAdelicPointsOpSplit`). For `k` in the first factor and `w` in the
  second, `factorHom e k = e⁻¹ (k, 1)` and `awayHom e w = e⁻¹ (1, w)`
  (module `Langlands.Shimura.SplitLevelTower`).
- *The prime-to-`m` levels.* `K₀` is a level of the first factor (a compact
  open subgroup, `CompactOpenLevel`). `cmPrimeToProperty D m hm K₀` holds for
  a level `K'` of the second factor when `e⁻¹ (K₀ × K')` is sufficiently
  small. The test lemma `mem_awayLevel_iff` of check `08a1612b` shows that
  `g` lies in this level exactly when `(e g).1 ∈ K₀` and `(e g).2 ∈ K'`.
- *Coefficients and cohomology.* `coeff : cmSmallLevelCoefficientDiagram ... R`
  is a coefficient diagram on the geometric tower `U ↦ X̄_U` over all small
  levels, exactly as in `HarrisCMColimitInvariantsStatement`: a sheaf of
  `R`-modules on the small étale site of each `X̄_U`, with transition morphisms
  `coeff.map a` for the arrows `a` of levels. `cmSmallLevelTrivialCoefficients`
  is level triviality: for `k ∈ K`, the self-arrow `⟨k⟩ : K ⟶ K` acts on the
  coefficients as the identity. `H^d(X̄_U, coeff_U)` is the étale cohomology of
  `cmSmallLevelCohomology ... R coeff d`.
- *The two colimits.* The target is `cmSmallLevelColimitCohomology ... R coeff d`,
  the colimit over all small levels ordered by inclusion, as an object with an
  action `ρ` of `G`. Its operators are those of the smooth representation
  `cmSmallLevelSmoothCohomology` used in `HarrisCMColimitInvariantsStatement`
  (lemma `smooth_rho_eq` of check `08a1612b`, proved by `rfl`). The source is
  `cmPrimeToColimitCohomology` of the restricted coefficients
  `cmPrimeToCoefficients ... coeff`: the colimit, over the levels `K'` with
  `cmPrimeToProperty D m hm K₀ K'` ordered by inclusion, of
  `H^d(X̄_{e⁻¹ (K₀ × K')}, coeff)`.
- *The comparison.* `cmPrimeToCohomologyComparison ... m hm K₀ ... R coeff d`
  is a morphism of objects with an action of the prime-to-`m` group, from the
  source to the target restricted along `awayHom e`. By
  `ι_cmPrimeToCohomologyComparison`, its composite with the insertion of level
  `K'` is the insertion `ι_{e⁻¹ (K₀ × K')}` of that level into the colimit
  over all small levels. Here `ι_U = RestrictedLevelColimit.ι (cmSmallLevelCohomology ... R coeff d) U`,
  the insertion used in `HarrisCMColimitInvariantsStatement`.

## The proposition

```lean
def HarrisCMPrimeToInvariantsStatement [Algebra ℚ R] : Prop :=
  letI := D.finite
  letI : Module.Finite ℚ A := Module.Finite.trans F A
  letI : ∀ {U V : SmallCMLevel D} (k : U ⟶ V), Etale ((geometricSchemes).map k) :=
    towerEtale
  ∀ (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
    (coeff : coefficients), trivialCoefficients coeff →
    (∀ {i j : (SmallCMLevel D)ᵒᵖ} (a : i ⟶ j), IsIso (coeff.map a)) →
    ∀ d : ℕ,
      Function.Injective
          (primeToComparison m hm K₀ existence geometry hRigid criterion R coeff d).hom.hom ∧
        Set.range
            (primeToComparison m hm K₀ existence geometry hRigid criterion R coeff d).hom.hom =
          {z | ∀ k ∈ K₀.subgroup,
            ((smallColimitCohomology coeff d).ρ
              (CompactOpenLevel.factorHom (cmPrimeToSplit D m hm) k)).hom z = z}
```

`geometricSchemes`, `towerEtale`, `coefficients`, `trivialCoefficients`,
`smallColimitCohomology` and `primeToComparison` are local notations for
`cmGeometricSchemeTower`, `cmSmallLevelTowerEtale`,
`cmSmallLevelCoefficientDiagram`, `cmSmallLevelTrivialCoefficients`,
`cmSmallLevelColimitCohomology` and `cmPrimeToCohomologyComparison`, applied
to the binders. The three `letI` lines supply instances that the Library's
prime-to-`m` declarations also supply: finiteness of `F` and `A` over `ℚ`, and
étaleness of the tower maps. The definition has no universe parameters.

In words: let `R` be a `ℚ`-algebra, `m ≠ 0`, `K₀` a level at the places
dividing `m`, and `coeff` a level-trivial coefficient diagram all of whose
transition maps `coeff.map a` are isomorphisms. Then for every degree `d`, the
comparison is injective, and a class `z` of the colimit over all small levels
is in its image if and only if `ρ (factorHom e k) z = z` for every `k ∈ K₀`.

The hypotheses:

- *Level triviality* makes classes from level `e⁻¹ (K₀ × K')` fixed by `K₀`.
  The Library proves this inclusion of the image in the invariants as
  `cmPrimeToCohomologyComparison_translate_of_mem`, under
  `[Nonempty (cmPrimeToProperty D m hm K₀).FullSubcategory]`; the test lemma
  `range_subset_invariants` of check `08a1612b` restates it in the form above.
  The proposition needs no such hypothesis: either no small level exists and
  both colimits are zero, or some prime-to-`m` level satisfies the property
  (steps 0 and 1 of the argument below).
- *Cartesian coefficients* and the *`ℚ`-algebra* hypothesis are those of
  `HarrisCMColimitInvariantsStatement`, which the argument applies at the
  levels `e⁻¹ (K₀ × K')`.

## Why the statement is expected to hold

This argument derives the proposition from `HarrisCMColimitInvariantsStatement`
and from elementary facts about filtered colimits and `p`-adic groups;
neither source states it in this form. Fix `m`, `K₀`, `coeff` and `d` as in
the proposition and write `V(K') = e⁻¹ (K₀ × K')`.

0. *The empty case.* If no small level exists, then no `K'` satisfies
   `cmPrimeToProperty D m hm K₀`, both colimits are over empty index
   categories, hence zero, and the proposition holds. Assume from now on that
   a small level `U₁` exists.
1. *Small levels of the form `V(K')`.* Let `p` be an odd prime not dividing
   `m`. A point over `ℚ_p` is a pair `(g, c)` with `g σ(g) = c`, so it is
   determined by the unit `g` of `ℚ_p ⊗ A`. Left multiplication on
   `ℚ_p ⊗ A` therefore embeds the local points at `p`, continuously, into
   `GL_N(ℚ_p)` with `N = dim_ℚ A`. The elements of `GL_N(ℤ_p)` congruent to `1`
   modulo `p` form an open subgroup without nontrivial elements of finite
   order, so its preimage `T_p` is an open subgroup of the local points at `p`
   without such elements. The second component of `e` is the points map of
   the restriction to the prime-to-`m` adeles
   (`finiteAdelicPointsSplit_apply_snd`), so the image at `p` of `g ∈ G`
   depends only on `(e g).2`, through the continuous evaluation of the
   prime-to-`m` points at `p`. For every level `W'` of the second factor, let
   `W''` be the subgroup of `W'` of elements whose image at `p` lies in `T_p`.
   It is open, hence closed in the compact `W'`, so it is a level, and
   `V(W'')` satisfies `LevelSmallAt` at `p`. Hence `cmPrimeToProperty D m hm K₀ W''`
   holds. Levels `W'` exist: the projection of the compact open subgroup
   `e(U₁)` to the second factor is a compact open subgroup, because the
   projection is a continuous open homomorphism. The property is inherited by
   smaller levels (`LevelSufficientlySmall.mono`), and the intersection of two
   levels is a level, so the prime-to-`m` levels form a nonempty directed
   system and the source colimit is filtered: every class of the source is the
   insertion of a class of some level `K'`
   (`RestrictedLevelTowerCohomology.exists_level_class`).
2. *Injectivity.* Let `x` be a class of the source with image `0`. Write
   `x` as the insertion of `y` at level `K'`. By
   `ι_cmPrimeToCohomologyComparison`, the image of `x` is `ι_{V(K')} y`, so
   `ι_{V(K')} y = 0`. `HarrisCMColimitInvariantsStatement` at the small level
   `V(K')` says that `ι_{V(K')}` is injective, so `y = 0` and `x = 0`.
3. *The image consists of invariants.* This is
   `cmPrimeToCohomologyComparison_translate_of_mem`, which applies because
   the index category is nonempty (step 1).
4. *Invariants are in the image.* Let `z` be fixed by `factorHom e k` for all
   `k ∈ K₀`. Write `z = ι_U y` for a small level `U`
   (`cmSmallLevelCohomology_exists_level_class`); by
   `HarrisCMColimitInvariantsStatement` at `U`, `z` is fixed by every element
   of `U`. Let `W'` be the intersection of the projection of `e(U)` to the
   second factor (a level, as in step 1) with the preimage of `U` under the
   continuous homomorphism `awayHom e`. It is an open subgroup of a compact
   group, hence a level. Let `W''` be as in step 1 for this `W'`. For
   `w ∈ W''`, `awayHom e w = e⁻¹ (1, w)` lies in `U`, so it fixes `z`. Every
   element of `V(W'')` is `e⁻¹ (k, w) = factorHom e k * awayHom e w` with
   `k ∈ K₀` and `w ∈ W''`, so it fixes `z`. `V(W'')` is a small level, so
   `HarrisCMColimitInvariantsStatement` at `V(W'')` gives `y'` with
   `z = ι_{V(W'')} y'`. By `ι_cmPrimeToCohomologyComparison`, this is the
   image under the comparison of the insertion of `y'` at level `W''`.

Nothing here uses finiteness of the sheaves or the degree `d`.

## Provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2. On printed p.96, read on a rendered image of the
page because the text layer omits the displays, they set
"`H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`" over sufficiently small
open compact subgroups `U` of `G(A^∞)`, and state: "If `V ⊂ U` then we see
that `H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`." On
printed p.97 (text layer) they continue: "Thus `H^i(X, L_ξ)` becomes an
admissible `G(A^∞)`-module". Taking invariants of `H^i(X, L_ξ)` under a
compact open subgroup that is not itself sufficiently small, such as one
whose component at the places dividing `m` is `K₀` and whose prime-to-`m`
component is arbitrary, is the step the proposition states. Harris and
Taylor do not state it separately.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Proposition 4.10 on printed p.311, read on a rendered image of the
page, ends: "Moreover, as `K(N)^{ℓ,p}` varies the spectral sequences are
`GG(A_f^{ℓ,p})`-equivariant." There the level at `ℓ` and `p` is fixed and the
level away from `ℓ, p` varies, as in the Library's prime-to-`m` tower. This
is motivation only: the proposition concerns the cohomology, not Harris's
spectral sequences.

| Lean | Source |
| --- | --- |
| colimit over all small levels of `H^d(X̄_U, coeff_U)` | `lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`, Harris–Taylor p.96, as constructed in the Library |
| colimit over `K'` of `H^d(X̄_{e⁻¹ (K₀ × K')}, coeff)` | the cohomology with the level at `m` fixed and the level away from `m` varying, as in Harris 1999 Prop. 4.10; constructed in the Library |
| injective comparison with image `{z \| ∀ k ∈ K₀, ρ (factorHom e k) z = z}` | the identification of this cohomology with the `K₀`-invariants; derived from the p.96 comparison |
| `[Algebra ℚ R]` | Harris–Taylor's coefficients are `ℚ_ℓ^ac`-vector spaces |

## Scope

The comparison is not an isomorphism in general. The Library's
`cmPrimeToCohomologyIso` makes it one under `IsRestrictedCofinal`, which says
that every small level contains a small level `e⁻¹ (K₀ × K')`. This fails
as soon as some small level has its component at the places dividing `m`
strictly smaller than `K₀`, for instance `e⁻¹ (K₁ × W'')` with `K₁ ⊊ K₀` and
`W''` as in step 1. The colimit over all small levels can then have classes
not fixed by `K₀`, so the proposition describes the image as the
`K₀`-invariants.

The statement does not cover:

- the full prime-to-`m` tower `cmPrimeToFullSchemeTower` or the Galois
  action of `HarrisTaylorCMPrimeToGaloisCohomology`;
- coefficient rings that are not `ℚ`-algebras;
- the sheaves `L_ξ`, ℓ-adic coefficients, limits over torsion coefficients,
  or Harris's Ext spectral sequences;
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
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  Proposition 4.10, printed p.311 (PDF p.13), read on a rendered image.
  Motivation only.

The truth argument uses no further source beyond the standard facts on
`p`-adic groups named in step 1.

## Formal dependencies and checks

Direct project import, in Library commit
`7e84f6ad2a2083a26977b5113dd0ab93f3f3b0ed` and the workspace:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology` | Library (no Author line) | `862ef504d67ad45868e7d01592961a01b8dc79eeb18cd1e3a80777b4cb68c18a` | `84b9af305fd1488db528c4ec4805f745f867ecbfb17365eefa8dde4503595668` |

Through it the module uses `HarrisTaylorCMSmallLevelCohomology` (the small
levels, coefficients, cohomology and colimit), `SplitLevelTower`
(`factorHom`, `awayHom`) and `RestrictedSplitLevelTowerCohomology` (the away
levels and the comparison). It does not import
`Langlands.Cohomology.HarrisCMColimitInvariants.Statement`, which the truth
argument uses.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks against Library `7e84f6ad`, all on the final Lean file (SHA-256
`4c493313d048a014f62c3b484f95420245fed1ac322a6d526783d3bf858dd31f`). None reported errors or warnings.

- `08a1612b-6099-4010-85ec-3fcfd5a73801` compiled the file from a draft
  directory together with a test file
  (`Langlands/Inspect/CMPrimeToInvariantsPrint.lean`, SHA-256
  `efd46c79a07448996cfea87a91ac430e118eb995f75f28e7a8bb8af89b63dfad`), not
  part of the candidate. It printed `HarrisCMPrimeToInvariantsStatement`: a
  `Prop`-valued definition with no universe parameters. It proved three
  lemmas, each depending only on `propext`, `Classical.choice` and
  `Quot.sound`: `range_subset_invariants` (the image of the comparison lies
  in the `K₀`-fixed classes, assuming some prime-to-`m` level exists),
  `smooth_rho_eq` (the operators of `cmSmallLevelSmoothCohomology` and of
  `cmSmallLevelColimitCohomology` agree, by `rfl`) and `mem_awayLevel_iff`
  (membership in the level `e⁻¹ (K₀ × K')`, by `Iff.rfl`).
- `abbebec9-1b85-470d-95c5-88d656c7301b` compiled a test file
  (`Langlands/Inspect/CMPrimeToInvariantsPremises.lean`, SHA-256
  `334ab636216de02cb19ff1644a72e495892f26e9b82e0bb08f70fd0fcb43b82d`)
  against this file. For each of the fourteen proved premises in the table
  above, an `example` with the premise type at universe zero is closed by the
  cited theorem. `#print axioms` shows that each theorem depends only on
  `propext`, `Classical.choice` and `Quot.sound`.
- `0eb12833-2627-47c6-b906-d94264924117` built the file with Lake from the workspace and inspected
  `HarrisCMPrimeToInvariantsStatement`, with the same result (type hash
  `71837723a2d84d60cc1263f0edd4276f463162e333eb5a2d35d8462a14e36cd5`).

This establishes a well-formed statement. It does not prove it.
