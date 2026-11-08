# Galois smoothness of prime-to-`m` CM cohomology

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition, `HarrisCMPrimeToGaloisSmoothStatement`,
about the Library's functor `cmPrimeToGaloisCohomologyFunctor` (module
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`). Fix `m ≠ 0`
and a level `K₀` at the places dividing `m`. The functor sends a sheaf `M` of
`R`-modules on the small étale site of `Spec F` to the colimit, over the
prime-to-`m` levels `K'` for which `e⁻¹ (K₀ × K')` is sufficiently small, of
`H^d(X̄_{e⁻¹ (K₀ × K')}, M)`, where `X̄_U = X_U ×_{Spec F} Spec F̄` and `M`
is pulled back to `X̄_U`. The colimit carries a smooth action of the
prime-to-`m` group and a commuting action of `F̄ ≃ₐ[F] F̄`.

The proposition says that this Galois action is smooth for the Krull
topology: for every `m`, `K₀`, degree `d`, sheaf `M` and class `x` of the
colimit, some open subgroup of `F̄ ≃ₐ[F] F̄` fixes `x`.

The Markdown of the Galois module says that it "considers no topology on the
Galois group and no continuity of its action." The proposition states that
continuity, in its form for a discrete module. Nothing is proved here.

The published `HarrisCMLevelGaloisSmoothStatement` (module
`Langlands.Cohomology.HarrisCMLevelGaloisSmooth.Statement`) is the same
assertion for the colimit over all sufficiently small levels. The present
proposition is not a formal consequence of it for a general ring `R` (see
"Relation to the published statement" below), but its truth argument applies
unchanged.

## Objects

All arithmetic types live in `Type` (universe zero), as in the Library's
modules. The binders are copied from
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`:

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
  four, through `cmPrimeToTowerEtale`, to prove that the transition maps of
  the prime-to-`m` tower are étale;
- a commutative ring `R : Type`.

There is no finiteness, torsion or characteristic hypothesis on `R`. The
integer `m`, the proof `hm : m ≠ 0`, the level `K₀`, the degree, the sheaf
and the class are quantified inside the proposition.

### Proof status of the premises

The Lean definition keeps every premise as an explicit hypothesis, as the
Library's modules do. A premise being a parameter does not mean that it is
unproved. In Library commit `568f1cff4df2c51ba08b932716bf99235d0032c7`,
fourteen premise types have published proofs, so a user can pass these
theorems as the corresponding arguments. Check `9749efbe` (see the checks
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
records, for Library commit `ce52163e150fe772fdb773627f006a99df1688af`, that
no theorem there concludes any of these five types and how far each one is
reduced. Between `ce52163e` and `568f1cff`, no Lean file that mentions any of
the five types changed. The only added ones are the published statement
modules `HarrisCMColimitInvariants`, `HarrisCMLevelGaloisSmooth` and
`HarrisCMLevelInvariants` and the Library modules
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToCohomology`,
`Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology`,
`Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology` and
`Langlands.Shimura.PEL.HarrisTaylorCMGeometricLatticeInverseImage`. All
seven use the types only as binders or variables, and none concludes them.

Since `q` is unproved, the proposition is a statement about the objects that
any witness `q` produces. A proof must work for every such witness.

### Notation

Write `F̄ = AlgebraicClosure F` and `Γ = F̄ ≃ₐ[F] F̄`, with Mathlib's Krull
topology, the only topology instance on this type (from
`Mathlib.FieldTheory.KrullTopology`). Write
`G = D.rationalInvolution.FiniteAdelicPointsᵐᵒᵖ`, the group in which the
Library's levels live.

- *The splitting.* `e = cmPrimeToSplit D m hm` is the Library's isomorphism
  of topological groups
  `G ≃ₜ* (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ × (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`:
  points over `∏_{v ∣ m} ℚ_v`, and points over the prime-to-`m` finite
  adeles.
- *The prime-to-`m` levels.* `K₀` is a compact open subgroup of the first
  factor (`CompactOpenLevel`). The index category is
  `(cmPrimeToProperty D m hm K₀).FullSubcategory`: the levels `K'` of the
  second factor for which `e⁻¹ (K₀ × K')` is sufficiently small, ordered by
  inclusion. For such `K'` write `U(K')` for the small level
  `(RestrictedSplitLevelTowerCohomology.awayFunctor e small K₀).obj K'`,
  whose subgroup is `e⁻¹ (K₀ × K')` (`awayFunctor_obj_obj`, by `rfl`).
- *The tower.* `cmPrimeToSchemeTower ... q m hm K₀` is an abbreviation for
  `awayLevelTower e K₀ (cmGeometricSchemeTower ... q)`, itself an
  abbreviation for the composite `awayFunctor e small K₀ ⋙
  cmGeometricSchemeTower ... q`, so its value at `K'` is
  `X̄_{U(K')} = X_{U(K')} ×_{Spec F} Spec F̄`. Its transition maps are étale
  (`cmPrimeToTowerEtale`).
- *Structure maps and coefficients.* `p_{K'} = (cmPrimeToArithmeticStructure ... q m hm K₀).app K'`.
  By `cmPrimeToArithmeticStructure_app` (proved by `rfl`) this is the
  structure map `X̄_{U(K')} ⟶ Spec F` of the published statement at the level
  `U(K')`, the projection to `X_{U(K')}` followed by the structure map of
  `X_{U(K')}`. The coefficient at level `K'` is
  `M_{K'} = (EtaleInverseImage.inverseImage p_{K'} R).obj M`, and
  `cmPrimeToArithmeticCoefficients ... M` assembles these with the
  restriction/projection comparisons along the transition maps
  (`RestrictedLevelTowerCohomology.canonicalCoefficients`).
- *Cohomology and colimit.* `H^d(X̄_{U(K')}, M_{K'}) = (EtaleDerivedSections.cohomology X̄_{U(K')} R d).obj M_{K'}`,
  the `d`-th right derived functor of global sections on sheaves of
  `R`-modules on the small étale site, computed with injective resolutions
  (Worker 13's `EtaleDerivedSections`). The diagram
  `(cmPrimeToArithmeticCoefficients ... M).cohomology d` has these values,
  and `ι_{K'} = RestrictedLevelColimit.ι (...) K'` is the insertion of level
  `K'` into its colimit. The functor `cmPrimeToGaloisCohomologyFunctor` is
  `RestrictedLevelTowerCohomology.automorphismActionFunctor` applied to these
  data. Its object at `M` is an object of
  `Action (SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ) Γ`, whose
  underlying smooth representation `V` is, by `rfl`
  (`cmPrimeToGaloisCohomologyFunctor_obj_V`), the colimit cohomology
  `cmPrimeToArithmeticCohomologyFunctor`.
- *The Galois automorphisms.* `cmPrimeToGaloisAction ... q m hm K₀` is
  `awayAutomorphisms e K₀` applied to the Galois action
  `cmSmallLevelGaloisAction ... q` of the published statement: the
  restriction of that action to the levels `U(K')`. Write
  `g_σ^{K'} = (cmPrimeToGaloisAction ... σ).unop.hom.app K'`. By
  `cmPrimeToGaloisAction_hom_app` it is
  `EtaleGaloisAction.baseChangeMap s_{U(K')} σ`, where `s_U` is the
  structure map of `X_U`: the identity on the factor `X_{U(K')}` and
  `Spec σ` on the factor `Spec F̄`. `cmPrimeToGaloisAction_over` says that
  `g_σ^{K'} ≫ p_{K'} = p_{K'}`.
- *The level operators.* `T_σ^{K'} = LevelTowerCohomology.projectionCohomologyMap R p_{K'} p_{K'} g_σ^{K'} e_σ d M`,
  an endomorphism of `H^d(X̄_{U(K')}, M_{K'})`, where `e_σ` is the level-`K'`
  component of `cmPrimeToGaloisAction_over`.
  `cmPrimeToGaloisCohomology_ρ_ι_apply` proves that the operator of `σ` on
  the colimit sends `ι_{K'} y` to `ι_{K'} (T_σ^{K'} y)`.
- *Comparison with the published operators.* The test lemma
  `levelOperator_eq` of check `9749efbe` (below) proves that `T_σ^{K'}` is
  the level-`U(K')` operator `T_σ` of
  [HarrisCMLevelGaloisSmooth](../HarrisCMLevelGaloisSmooth/Statement.md),
  built from `cmSmallLevelGaloisAction` and
  `cmSmallLevelArithmeticGeometricStructure` at `U(K')`. It uses the test
  lemma `galoisAction_app_eq` (the two automorphisms agree) and the Library's
  `LevelTowerCohomology.projectionCohomologyMap_congr`.
- `SmoothRep.hom` (Library, `Langlands.Representation.Category.Basic`)
  extracts the underlying intertwining map of a morphism of smooth
  representations. The Galois operator is a morphism in
  `SmoothRep R (D.rationalInvolution.PrimeToPoints m)ᵐᵒᵖ`, so it commutes
  with the prime-to-`m` action (`cmPrimeToGaloisCohomology_commutes`).

## The proposition

```lean
def HarrisCMPrimeToGaloisSmoothStatement : Prop :=
  ∀ (m : ℕ) (hm : m ≠ 0) (K₀ : CompactOpenLevel (D.rationalInvolution.DividingPoints m)ᵐᵒᵖ)
    (d : ℕ) (M : EtaleDerivedSections.ModuleSheaf (Spec (CommRingCat.of F)) R)
    (x : ((primeToGaloisCohomologyFunctor m hm K₀ existence geometry hRigid criterion R
      d).obj M).V),
    ∃ V : OpenSubgroup Galois, ∀ σ ∈ V,
      SmoothRep.hom (((primeToGaloisCohomologyFunctor m hm K₀ existence geometry hRigid
        criterion R d).obj M).ρ σ) x = x
```

`Galois` is local notation for `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`
and `primeToGaloisCohomologyFunctor` for `cmPrimeToGaloisCohomologyFunctor`
applied to `D`, `C` and the premises through `q`. The definition has no
universe parameters and no derived-category instances: the operators are
restriction-based.

In words: for every `m ≠ 0`, every level `K₀` at the places dividing `m`,
every degree `d`, every sheaf `M` of `R`-modules on the small étale site of
`Spec F`, and every class `x` of `colim_{K'} H^d(X̄_{e⁻¹ (K₀ × K')}, M)`,
there is an open subgroup `V` of `Γ` such that every `σ ∈ V` fixes `x`.

### Level-wise form

Check `9749efbe` (below) defines the level-wise form

```lean
∀ m hm K₀ d M (K' : (cmPrimeToProperty D m hm K₀).FullSubcategory)
  (y : H^d(X̄_{U(K')}, M_{K'})),
  ∃ V : OpenSubgroup Galois, ∀ σ ∈ V, ι_{K'} (T_σ^{K'} y) = ι_{K'} y
```

(written out in Lean with the actual names) and proves:

- `statement_imp_levelwise`: the proposition implies the level-wise form;
- `levelwise_imp_statement`: assuming
  `∀ m hm K₀, Nonempty (cmPrimeToProperty D m hm K₀).FullSubcategory`, the
  level-wise form implies the proposition.

The second direction uses
`RestrictedLevelTowerCohomology.canonicalCohomology_exists_level`: if the
index category is nonempty, every class of the colimit is `ι_{K'} y` for some
`K'` and `y`. For a triple `m, hm, K₀` without prime-to-`m` levels the
colimit is over the empty category, hence the zero module, and the
proposition holds there with `V = ⊤`. This last remark is derived and was not
checked in Lean.

So the proposition says exactly: the class in the colimit of each
level-`K'` class `y` is fixed by an open subgroup, where `σ` acts at level
`K'` by `T_σ^{K'}`, which is the operator `T_σ` of the published statement at
the level `e⁻¹ (K₀ × K')`.

## Why the statement is expected to hold

This argument is derived; neither source states the proposition. Fix `m`,
`K₀`, `d`, `M`, a level `K'` and `y ∈ H^d(X̄_{U(K')}, M_{K'})`. By the
level-wise form it suffices to find an open subgroup `V` of `Γ` with
`T_σ^{K'} y = y` for all `σ ∈ V`.

By `levelOperator_eq`, `T_σ^{K'}` is the operator `T_σ` at the small level
`U = U(K')` of the published statement, on the same module
`H^d(X̄_U, p_U^* M)`. The truth argument of
[HarrisCMLevelGaloisSmooth](../HarrisCMLevelGaloisSmooth/Statement.md),
steps 1 to 6, proves at a fixed level `U` that `T_σ y = y` for every `σ` in
the fixing subgroup of some finite subextension `E` of `F̄ / F`, which is open
for the Krull topology. In outline:

1. `X_U` is quasi-compact and quasi-separated, because the witness `q U`
   makes its structure map projective and `Spec F` is affine.
2. `X̄_U` is the limit of the base changes `X_E = X_U ×_{Spec F} Spec E`
   over the finite subextensions `E`, with affine transition maps
   (SGA 4 VII 5.1).
3. SGA 4 VII Corollaire 5.8 makes `colim_E H^d(X_E, -) ⟶ H^d(X̄_U, -)` an
   isomorphism for the pulled-back coefficients, so `y` is pulled back from
   a class on some `X_E`. The Library's general pullback
   `cohomologyPullbackWithCoefficients` is the pullback map of SGA 4: both
   are morphisms of δ-functors in the coefficient sheaf that agree in degree
   zero, and the source is a universal δ-functor (Tôhoku Proposition 2.2.1).
   Along étale maps it agrees with the restriction-based map
   (`cohomologyPullbackWithCoefficients_restriction`), so `T_σ` is a general
   pullback.
4. For `σ` fixing `E`, the automorphism `g_σ` commutes with the projection
   `X̄_U ⟶ X_E`. Pullbacks compose
   (`sheafDerivedPullbackWithCoefficients_comp`), and the coefficient
   isomorphisms are coherent (`inverseImageComp_assoc`), so `T_σ y = y`.

Then `ι_{K'} (T_σ^{K'} y) = ι_{K'} y`, which is the level-wise form, and the
proposition follows. The open subgroup depends on `y`, hence on `K'`, but on
nothing else, and the argument uses no finiteness of `M`, the ring `R` or the
degree `d`.

### Relation to the published statement

The proposition is not a formal consequence of
`HarrisCMLevelGaloisSmoothStatement` for a general `R`. That statement gives
`ι_U (T_σ y) = ι_U y` in the colimit over all small levels, and the
Library's comparison `cmPrimeToCohomologyComparison` sends `ι_{K'}` to
`ι_{U(K')}`. Deducing `ι_{K'} (T_σ^{K'} y) = ι_{K'} y` from this needs the
comparison to be injective, and a class can become zero at a small level
that is not of the form `e⁻¹ (K₀ × K'')`.

When `R` is a `ℚ`-algebra, the deduction does go through, by the following
derived argument that was not checked in Lean. The comparison commutes with
the Galois operators (`cmPrimeToGaloisCohomologyComparison_apply`, with the
arithmetic coefficients `cmSmallLevelArithmeticCoefficients M`). These
coefficients are level-trivial
(`cmSmallLevelArithmeticCoefficients_trivial`), and their transition maps are
components of the isomorphisms `restrictionProjectionIso`
(`cmSmallLevelArithmeticCoefficients_map`). So the injectivity part of
`HarrisCMPrimeToInvariantsStatement` (module
`Langlands.Cohomology.HarrisCMPrimeToInvariants.Statement`, a statement
candidate by the same author, `a8fc38cf-2b8f-4e40-a716-56f0f5917041`, which
is not in Library `568f1cff`) applies to them. The direct argument above
needs no such hypothesis.

The Library module `Langlands.Geometry.EtaleGaloisTower` (no Author line)
constructs smooth Galois actions, for the Krull topology, on the colimit over
finite Galois subextensions `E` of the cohomology of `X_E`. Its Markdown says
that it does not prove that this colimit is isomorphic to the cohomology of
`X ×_{Spec K} Spec L`. It therefore does not prove this proposition, whose
cohomology is that of `X̄_U` itself.

The Library module `Langlands.Shimura.PEL.HarrisTaylorCMDecompositionCohomology`
(no Author line, new in `568f1cff`) composes
`cmPrimeToGaloisCohomologyFunctor` with the restriction to the absolute
Galois group of a completion `F_w` (`cmPrimeToDecompositionCohomologyFunctor`).
Its Markdown says: "No topology on the Galois groups and no continuity of
actions is considered." It does not prove this proposition either.

## Provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), Proposition 4.10 on printed p.311, read on a rendered image of the
page, ends: "Moreover, as `K(N)^{ℓ,p}` varies the spectral sequences are
`GG(A_f^{ℓ,p})`-equivariant." There the level at `ℓ` and `p` is fixed and
the level away from `ℓ, p` varies, as in the Library's prime-to-`m` tower.
§5, printed p.313, works
with "λ-adic representations σ of Gal(F̄/F)".

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p.96, read on a rendered image because the
text layer omits the display, set
"`H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`" over sufficiently small
open compact subgroups `U` of `G(A^∞)`. On printed p.97 (text layer, where
the slash is rendered as "j") they conclude: "Thus `H^i(X, L_ξ)` becomes an
admissible `G(A^∞)`-module, in fact an admissible/continuous
`G(A^∞) × Gal(F^ac/F)`-module."

The proposition is the Galois-continuity part of that sentence, for a
discrete module and for the tower with the level at the places dividing `m`
fixed. It is an analogue for the Library's objects:

- the coefficients are arbitrary sheaves `M` on `Spec F` pulled back to each
  level, not the sheaves `L_ξ` attached to an algebraic representation `ξ`;
- coefficients are discrete `R`-modules, not `Q̄_ℓ`-vector spaces;
- the Library's levels are the Harris–Taylor CM PEL levels, conditional on
  the premises above, and its prime-to-`m` group is not identified with
  Harris's `GG(A_f^{ℓ,p})`.

Neither source states this proposition as a separate result.

| Lean | Source |
| --- | --- |
| colimit over the prime-to-`m` levels `K'` of `H^d(X̄_{e⁻¹ (K₀ × K')}, M)` | the cohomology with the level at `ℓ, p` fixed and the level away from them varying, Harris 1999 Prop. 4.10; constructed in the Library |
| `∃ V : OpenSubgroup Galois, ∀ σ ∈ V, ρ σ x = x` | Harris–Taylor p.97 ("continuous"); Harris 1999 §5, p.313 (λ-adic representations); truth from SGA 4 VII Corollaire 5.8 at each level |
| `∀ m hm K₀ d M x` | every fixed level at `m`, degree, coefficient sheaf on `Spec F` and class |

## Scope

The statement does not cover:

- admissibility for the prime-to-`m` group, or the Hecke modules
  `cmPrimeToGaloisHeckeModuleFunctor` of the same Library module;
- the full prime-to-`m` tower `cmPrimeToFullSchemeTower`;
- the sheaves `L_ξ`, ℓ-adic or rational coefficients, limits over torsion
  coefficients, or Harris's spectral sequences;
- compact supports, intersection cohomology, or local-global compatibility;
- any topology on the cohomology modules other than the discrete one;
- a proof of any premise. The open premises `square`, `q`, `existence`,
  `geometry` and `hRigid` stay open, and the proved ones are not
  instantiated here.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  Proposition 4.10, printed p.311 (PDF p.13), read on a rendered image, and
  §5, printed p.313 (PDF p.15). Provenance only.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`: Harris–Taylor
  2001, PDF SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`
  (printed page = PDF page - 8); III.2, printed p.96 (PDF p.104, read on a
  rendered image) and p.97 (PDF p.105, read in the text layer). Provenance
  only.
- `sga4-1972-tome2-verdier-v-original-scan`: SGA 4 Tome 2, Lecture Notes in
  Mathematics 270, original scan, PDF SHA-256
  `7c5b8cef5a99d22785501eead8353641064f858c51ce361b00b310b2bcc46585`
  (PDF page = printed page + 2): Exposé VII (Grothendieck) 5.1, printed
  pp.356-357; Corollaire 5.8, printed p.362. Used only in the truth
  argument.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), retained file
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
  Proposition 2.2.1, printed p.141 (PDF p.23). Used only in the truth
  argument.

## Formal dependencies and checks

Direct project import, in Library commit
`568f1cff4df2c51ba08b932716bf99235d0032c7` and the workspace (unchanged
since `7e84f6ad2a2083a26977b5113dd0ab93f3f3b0ed`):

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Shimura.PEL.HarrisTaylorCMPrimeToGaloisCohomology` | Library (no Author line) | `a185d877105c950f281ff405593ef815e4b177e1c639f5c431f3c0a700a8dcb1` | `49abedef0f75b5667fb2d058d30e29a1873f3eb3b8da6102e56d685088381ea6` |

The module also imports Mathlib's `Mathlib.FieldTheory.KrullTopology`.
Through the import it uses `HarrisTaylorCMSmallLevelIndex` (Author: Worker
57) for the small levels; `EtaleGaloisAction` (Author: Worker 13) for
`baseChangeMap`; `EtaleDerivedSections` (Author: Worker 13) for the
cohomology; and the Library modules `HarrisTaylorCMPrimeToCohomology`
(`cmPrimeToSplit`, `cmPrimeToProperty`, `cmPrimeToSchemeTower`,
`cmPrimeToTowerEtale`), `HarrisTaylorCMSmallLevelGaloisCoefficients`,
`RestrictedSplitLevelTowerCohomology` (`awayFunctor`),
`RestrictedReindexTowerAutomorphisms` (`awayAutomorphisms`),
`RestrictedLevelTowerCanonicalCoefficients`
(`automorphismActionFunctor`, `canonicalCohomology_exists_level`),
`LevelTowerCanonicalCoefficients` (`projectionCohomologyMap`,
`projectionCohomologyMap_congr`), `RestrictedLevelColimit` and
`Representation.Category.Basic`, whose Markdown files have no Author line.
The truth argument also uses the published statement
`Langlands.Cohomology.HarrisCMLevelGaloisSmooth.Statement`, which this
module does not import.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks against Library `568f1cff`, all on the final Lean file (SHA-256
`1360198eeba5a7c711b0d4851a78455f608d7f5a7206c8f59250c869e78d7aad`). None
reported errors or warnings.

- `9749efbe-4c1e-4c33-bc70-6e1757be6427` built the file with Lake from a
  draft directory together with two test files that are not part of the
  candidate.
  - `Langlands/Inspect/CMPrimeToGaloisSmoothPrint.lean` (SHA-256
    `c2ce510bd354295191a2b3a24e00c616e0eeb76ffdf74015a880e6ab9f1c04ec`)
    printed `HarrisCMPrimeToGaloisSmoothStatement` with universes: a
    `Prop`-valued definition with no universe parameters. It defined the
    level-wise form above and proved four lemmas, each depending only on
    `propext`, `Classical.choice` and `Quot.sound`:
    `statement_imp_levelwise`, `levelwise_imp_statement`,
    `galoisAction_app_eq` and `levelOperator_eq`.
  - `Langlands/Inspect/CMPrimeToGaloisSmoothPremises.lean` (SHA-256
    `cea46ae3edbd3eaf0096b5c60bd5bf1fd0931ae703c25faa5919b515d1981c5c`):
    for each of the fourteen proved premises in the table above, an
    `example` with the premise type at universe zero is closed by the cited
    theorem. `#print axioms` shows that each theorem depends only on
    `propext`, `Classical.choice` and `Quot.sound`.
- `98657cb8-1a3d-456d-b635-eb3cf4f69f8f` built the file with Lake from the
  workspace and inspected `HarrisCMPrimeToGaloisSmoothStatement`: a
  `Prop`-valued definition with no universe parameters, depending only on
  `propext`, `Classical.choice` and `Quot.sound` (type hash
  `588bf787909aadd0c9edc516c8ac66578b6127a052a2612a94d08bf69337d05b`).

The same files passed the same checks against Library `7e84f6ad`
(`01ba42dd-27eb-4cbf-9ed3-c869ef790fc7`,
`c1f66fd2-e92f-4ddf-80ed-52d5931ca211` and
`3b11d1de-817f-4457-9773-8ad3af7a6434`, with the same type hash).

This establishes a well-formed statement. It does not prove it.
