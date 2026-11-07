# Galois smoothness of CM cohomology over all small levels

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states one proposition, `HarrisCMLevelGaloisSmoothStatement`,
about the Library's functor `cmSmallLevelGaloisCohomologyFunctor` (module
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients`). That
functor sends a sheaf `M` of `R`-modules on the small étale site of `Spec F`
to the colimit, over all sufficiently small CM levels `U`, of
`H^d(X̄_U, p_U^* M)`, where `X̄_U = X_U ×_{Spec F} Spec F̄`. The colimit
carries a smooth action of the finite-adelic group and a commuting action of
`F̄ ≃ₐ[F] F̄`.

The proposition says that this Galois action is smooth for the Krull
topology: for every degree `d`, every `M` and every class `x` of the
colimit, some open subgroup of `F̄ ≃ₐ[F] F̄` fixes `x`.

The Markdown of the Galois-coefficients module says: "`Gamma` is used as an
algebraic group here. No topology on it, continuity of its action, or adic
limit is constructed." The proposition states that continuity, in its form
for a discrete module. Nothing is proved here.

## Objects

All arithmetic types live in `Type` (universe zero), as in the Library's
modules. The binders are copied from
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients`. They
are:

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
  four, through `cmSmallLevelTowerEtale`, to prove that the transition maps
  of the geometric tower are étale;
- a commutative ring `R : Type`.

There is no finiteness, torsion or characteristic hypothesis on `R`.

### Proof status of the premises

The Lean definition keeps every premise as an explicit hypothesis, as the
Library's modules do. That a premise is a parameter does not mean that it is
unproved. In Library commit `ce52163e150fe772fdb773627f006a99df1688af`,
fourteen of the premise types have published proofs, so a user can pass these
theorems as the corresponding arguments. Check `f0cecafe` (see the checks
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
that commit: a search of its Lean sources found no theorem whose conclusion
is the premise type. The later Library commit
`0d9cba336dd98294a5d7f48d772eb708aae40708` adds no Lean file that mentions
any of these five premise types.

- `square : MumfordBundlePicardZeroStatement.{0}`. The Library derives it only
  conditionally. `Langlands.AbelianScheme.MumfordPicardZero.mumfordBundlePicardZero_of_cube`
  (module `Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction`)
  proves it from `FieldCubePullbackStatement` and
  `FieldLineBundleTrivialityStatement`. The second is proved
  (`Langlands.AlgebraicGeometry.Picard.fieldLineBundleTriviality`). The first
  is derived only from the unproved `FieldCubeIsomorphismStatement`, by
  `Langlands.GroupScheme.fieldCubePullbackOfIsomorphism` (module
  `Langlands.AbelianScheme.FieldCubePullbackAssembly`).
- `q : CMRepresentabilityStatement ...`, representability of the CM moduli
  problem. Its division-algebra case is stated separately as
  `DivisionCMRepresentabilityStatement`, which is also unproved there.
- `existence : RelativeDualSchemeExistenceStatement.{0}` and
  `geometry : RelativeDualSchemeGeometryStatement.{0}`.
- `hRigid`, coarse rigidity at every small level. This is a condition on the
  levels, not a general theorem. The docstring of
  `CMGeometricCoarseRigidity` says that it "is not inferred from sufficiently
  small level", and every Library module that uses it takes it as a
  hypothesis.

Since `q` is unproved, the proposition is a statement about the objects that
any witness `q` produces. A proof must work for every such witness.

### Notation

Write `F̄ = AlgebraicClosure F` and `Γ = F̄ ≃ₐ[F] F̄`, with Mathlib's Krull
topology, the only topology instance on this type (from
`Mathlib.FieldTheory.KrullTopology`). For a small CM level `U`:

- `X_U = (cmSchemeTower ... q).obj U`, the scheme chosen from `q`, with its
  structure morphism `s_U = (cmSmallLevelArithmeticStructure ... q).app U :
  X_U ⟶ Spec F`, the structure morphism of the represented over-tower. The
  witness `q U` provides this smooth structure morphism and an
  `IsHProjective` witness for it (`HarrisTaylorCMRepresentabilityStatement`,
  fields `smooth` and `projective`).
- `X̄_U = (cmGeometricSchemeTower ... q).obj U`, the fiber product
  `X_U ×_{Spec F} Spec F̄`, with first projection
  `π_U = (cmGeometricProjection ... q).app U : X̄_U ⟶ X_U`.
- `p_U = (cmSmallLevelArithmeticGeometricStructure ... q).app U = π_U ≫ s_U :
  X̄_U ⟶ Spec F`. This is the definition
  `cmSmallLevelArithmeticGeometricStructure = cmGeometricProjection ≫
  cmSmallLevelArithmeticStructure`.
- `M_U = (EtaleInverseImage.inverseImage p_U R).obj M`, the coefficient at
  level `U` (`cmSmallLevelArithmeticCoefficients_obj`). The inverse image is
  a left Kan extension followed by sheafification, left adjoint to the
  direct image.
- `H^d(X̄_U, M_U) = (EtaleDerivedSections.cohomology X̄_U R d).obj M_U`, the
  `d`-th right derived functor of global sections on
  `Sheaf (Scheme.smallEtaleTopology X̄_U) (ModuleCat.{0} R)`, computed with
  injective resolutions (Worker 13's `EtaleDerivedSections`).

The colimit:

- `cmSmallLevelCohomologyDiagram ... (cmSmallLevelArithmeticCoefficients M) d`
  is a functor `(OrderedSmallCMLevel D)ᵒᵖ ⥤ ModuleCat.{0} R`, with value
  `H^d(X̄_U, M_U)` at `U`. `OrderedSmallCMLevel D` is the preorder of
  sufficiently small compact open levels under inclusion.
  `cmSmallLevelCohomologyDiagram_eq_restricted` identifies the diagram with
  the Library's `RestrictedLevelColimit.diagram`. For `V ⊆ U`, the
  transition `H^d(X̄_U, M_U) ⟶ H^d(X̄_V, M_V)` is the cohomology map
  `cohomologyMapWithCoefficients` along the étale tower map `X̄_V ⟶ X̄_U`,
  followed by the coefficient transition, which
  `cmSmallLevelArithmeticCoefficients_map` identifies with the
  `restrictionProjectionIso` of the two structure maps.
- The underlying module of `((cmSmallLevelGaloisCohomologyFunctor ... R d).obj M).V`
  is definitionally the colimit of this diagram: the equivalence check below
  passes a class of the statement directly to
  `cmSmallLevelCohomology_exists_level_class`, whose argument has the
  colimit type. Write `ι_U` for the colimit insertion
  `RestrictedLevelColimit.ι (...) U`.

The Galois action:

- `g_σ = ((cmSmallLevelGaloisAction ... q σ).unop.hom).app U : X̄_U ⟶ X̄_U`.
  `cmSmallLevelGaloisAut_hom_app` proves that it is
  `EtaleGaloisAction.baseChangeMap s_U σ = pullback.map ... (𝟙 X_U)
  (specMap σ) ...`, with `specMap σ = Spec.map σ`. So `g_σ` is the identity
  on the factor `X_U` and `Spec σ` on the factor `Spec F̄`. Since `Spec` is
  contravariant, `cmSmallLevelGaloisAction` takes values in the opposite
  automorphism group.
- `e_σ : g_σ ≫ p_U = p_U` is the level-`U` component of
  `cmSmallLevelGaloisAction_over`.
- `T_σ = LevelTowerCohomology.projectionCohomologyMap R p_U p_U g_σ e_σ d M`,
  an endomorphism of `H^d(X̄_U, M_U)`. By definition
  (`LevelTowerCanonicalCoefficients`, line 103) it is
  `EtalePullback.cohomologyMapWithCoefficients g_σ R d
  ((restrictionProjectionIso R p_U p_U g_σ e_σ).hom.app M)`: the
  restriction-based cohomology map along the isomorphism (hence étale) `g_σ`,
  followed by the canonical coefficient isomorphism. By
  `restrictionProjectionIso_hom_app`, that coefficient isomorphism is the
  inverse of the comparison between inverse image and restriction along
  `g_σ`, followed by `projectionInverseImageIso R p_U p_U g_σ e_σ`, which is
  `inverseImageComp R p_U g_σ ≪≫ inverseImageCongr R e_σ`.
- `cmSmallLevelGaloisCohomology_ρ_ι_apply` proves that the operator of `σ`
  on the colimit sends `ι_U y` to `ι_U (T_σ y)`.
- `SmoothRep.hom` (Library, `Langlands.Representation.Category.Basic`)
  extracts the underlying intertwining map of a morphism of smooth
  representations. The Galois operator is a morphism in `SmoothRep R G`, so
  it commutes with the finite-adelic action
  (`cmSmallLevelGaloisCohomology_commutes`).

## The proposition

```lean
def HarrisCMLevelGaloisSmoothStatement : Prop :=
  ∀ (d : ℕ) (M : EtaleDerivedSections.ModuleSheaf (Spec (CommRingCat.of F)) R)
    (x : ((cmSmallLevelGaloisCohomologyFunctor D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q existence geometry
      hRigid criterion R d).obj M).V),
    ∃ V : OpenSubgroup Galois, ∀ σ ∈ V,
      SmoothRep.hom (((cmSmallLevelGaloisCohomologyFunctor D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q existence geometry
        hRigid criterion R d).obj M).ρ σ) x = x
```

Here `Galois` is local notation for
`AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`. The definition has no
universe parameters and no derived-category instances: the operators are
restriction-based.

In words: for every degree `d`, every sheaf `M` of `R`-modules on the small
étale site of `Spec F`, and every class `x` of
`colim_U H^d(X̄_U, p_U^* M)`, there is an open subgroup `V` of `Γ` such that
every `σ ∈ V` fixes `x`.

### Level-wise form

Check `63d0dfe7` (below) defines the level-wise form

```lean
∀ (d : ℕ) (M) (U : SmallCMLevel D) (y : H^d(X̄_U, M_U)),
  ∃ V : OpenSubgroup Galois, ∀ σ ∈ V, ι_U (T_σ y) = ι_U y
```

(written out in Lean with the actual names) and proves:

- `statement_imp_levelwise`: the proposition implies the level-wise form;
- `levelwise_imp_statement [Nonempty (SmallCMLevel D)]`: the level-wise form
  implies the proposition.

The second direction uses `cmSmallLevelCohomology_exists_level_class`: if a
small level exists, every class of the colimit is `ι_U y` for some `U` and
`y`. Without small levels, `OrderedSmallCMLevel D` is empty, the colimit is
the zero module, and the proposition holds with `V = ⊤`. This last remark
is derived and was not checked in Lean.

So the proposition says exactly: the class in the colimit of each
level-`U` class `y` is fixed by an open subgroup, where `σ` acts at level
`U` by `T_σ`.

## Why the statement is expected to hold

This argument is derived. It combines the cited results of SGA 4 with
Library facts and is not a quotation. It is the smoothness argument of
[HarrisCMCohomology](../HarrisCMCohomology/Statement.md), applied at each
level to the coefficient `s_U^* M` in place of a torsion coefficient on
`X_U`.

Fix `U` and `y ∈ H^d(X̄_U, M_U)`. It suffices to find an open subgroup `V`
with `T_σ y = y` for all `σ ∈ V`. Then `ι_U (T_σ y) = ι_U y`, which is the
level-wise form, and the proposition follows by the equivalence above.

1. *`X_U` is quasi-compact and quasi-separated.* The witness in `q` makes
   `s_U` projective, hence proper, hence quasi-compact and separated. Since
   `Spec F` is affine, `X_U` is quasi-compact and quasi-separated.
2. *Reduction to finite subextensions.* Let `E` range over the intermediate
   fields of `F̄ / F` that are finite-dimensional over `F`. The subgroups
   `E.fixingSubgroup` are open for the Krull topology
   (`IntermediateField.fixingSubgroup_isOpen`). It suffices to find one `E`
   whose fixing subgroup fixes `y`.
3. *`X̄_U` is a limit.* `F̄` is the filtered union of the fields `E`. Put
   `X_E = X_U ×_{Spec F} Spec E`, with projections `u_E : X_E ⟶ X_U` and
   `p_E : X̄_U ⟶ X_E`, so that `p_E ≫ u_E = π_U`. Each `X_E` is finite over
   `X_U`, hence quasi-compact and quasi-separated. The transition maps are
   base changes of the affine maps `Spec E' ⟶ Spec E`, hence affine. The
   limit of the system is `X̄_U` (SGA 4 VII 5.1).
4. *The limit theorem.* Put `A = s_U^* M` on `X_U`. SGA 4 VII Corollaire 5.8,
   with `i₀` the index `F`, `X_{i₀} = X_U` and `F_{i₀} = A`, says that the
   canonical map `colim_E H^d(X_E, u_E^* A) ⟶ H^d(X̄_U, π_U^* A)` is an
   isomorphism. Each component is pullback along `p_E` followed by the
   canonical isomorphism `p_E^* u_E^* A ≅ π_U^* A`, and
   `π_U^* A = π_U^* s_U^* M ≅ p_U^* M = M_U` canonically. Hence `y` is the
   pullback along `p_E` of a class `c_E ∈ H^d(X_E, (u_E ≫ s_U)^* M)`,
   followed by the canonical coefficient isomorphism
   `p_E^* (u_E ≫ s_U)^* M ≅ M_U`. The Lean cohomology agrees with that of
   SGA 4 (step 5 of the finiteness argument of HarrisCMCohomology). The
   Library's general pullback `cohomologyPullbackWithCoefficients` (module
   `Langlands.Geometry.EtaleGeometricCoefficientPullback`) is the pullback
   map of SGA 4: both are morphisms of δ-functors in the coefficient sheaf
   that agree in degree zero, and the source is a universal δ-functor
   (Tôhoku Proposition 2.2.1). The general pullback needs
   `HasDerivedCategory` instances; Mathlib's `HasDerivedCategory.standard`
   supplies them, and they do not change the cohomology modules.
5. *`T_σ` is a general pullback.* `cohomologyPullbackWithCoefficients_restriction`
   (same module) proves that, along an étale map, the restriction-based map
   `cohomologyMapWithCoefficients g R d α` equals the general pullback
   `cohomologyPullbackWithCoefficients g R d` with the coefficient map
   precomposed by the comparison between inverse image and restriction. For
   `T_σ`, this comparison cancels against its inverse in
   `restrictionProjectionIso_hom_app`. So `T_σ` is the general pullback along
   `g_σ` with coefficient map `(inverseImageComp R p_U g_σ).hom.app M ≫
   (inverseImageCongr R e_σ).hom.app M`, the canonical isomorphism
   `g_σ^* p_U^* M ≅ (g_σ ≫ p_U)^* M = p_U^* M`.
6. *Classes from `X_E` are fixed by `E.fixingSubgroup`.* Let `σ` fix `E`
   pointwise. Then `g_σ ≫ p_E = p_E`: on the factor `X_U` both sides are the
   identity, and `Spec σ` followed by `Spec F̄ ⟶ Spec E` is
   `Spec F̄ ⟶ Spec E` because `σ` is the identity on `E`. Pullbacks compose:
   the Library proves `sheafDerivedPullbackWithCoefficients_comp`, and
   `sheafDerivedPullbackWithCoefficients_homology` transports it to
   `cohomologyPullbackWithCoefficients`. So `T_σ y` is the pullback of `c_E`
   along `g_σ ≫ p_E = p_E`, with a coefficient map built from the canonical
   isomorphisms `inverseImageComp` and `inverseImageCongr`. That map is
   again the canonical isomorphism `p_E^* (u_E ≫ s_U)^* M ≅ M_U`. This
   follows from the associativity coherence of these isomorphisms
   (`inverseImageComp_assoc`, module
   `Langlands.Geometry.EtaleInverseImageCoherence`) and their compatibility
   with equality transport. Hence `T_σ y = y`. This step is derived; the
   schemes `X_E` are not Library objects, and the cited lemmas hold for
   arbitrary morphisms of schemes.

The open subgroup depends on `y`, and through `y` on the level `U`. Nothing
here uses finiteness of `M`, the ring `R` or the degree `d`. The Library's
`projectionCohomologyMap_comp` composes only étale maps, and `p_E` is not
étale in general, so the argument uses the general pullback.

## Provenance

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p.96, construct a lisse étale
`Q_ℓ^ac`-sheaf `L_ξ` on `X_U` from a finite-dimensional representation `ξ`
of `G` on a `Q_ℓ^ac`-vector space, for sufficiently small open compact
subgroups `U` of `G(A^∞)`. They then set
"`H^i(X, L_ξ) = lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`". This display was read
on a rendered image of the page; the text layer omits it. On printed
p.97 they conclude: "Thus `H^i(X, L_ξ)` becomes an admissible
`G(A^∞)`-module, in fact an admissible/continuous
`G(A^∞) × Gal(F^ac/F)`-module." The quotation is from the text layer, where
the slash is rendered as "j".

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), §5, printed p.313, works with "λ-adic representations σ of
Gal(F̄/F)".

The Lean colimit has the shape of the Harris–Taylor display: a colimit over
sufficiently small levels of the cohomology of `X_U ×_{Spec F} Spec F̄`, with
`Gal(F̄/F)` acting through the second factor. The proposition is the
Galois-continuity part of the p.97 sentence, for a discrete module. It is an
analogue for the Library's objects:

- the coefficients are arbitrary sheaves `M` on `Spec F` pulled back to each
  level, not the sheaves `L_ξ` attached to an algebraic representation `ξ`;
- coefficients are discrete `R`-modules, not `Q̄_ℓ`-vector spaces;
- the Library's levels are the Harris–Taylor CM PEL levels, conditional on
  the premises above.

Neither source states this proposition as a separate result.

| Lean | Source |
| --- | --- |
| colimit over `(OrderedSmallCMLevel D)ᵒᵖ` of `H^d(X̄_U, p_U^* M)` | Harris–Taylor III.2, p.96 (`lim_{→U} H^i_et(X_U ×_F F^ac, L_ξ)`), as constructed in the Library |
| `∃ V : OpenSubgroup Galois, ∀ σ ∈ V, ρ σ x = x` | Harris–Taylor p.97 ("continuous"); Harris 1999 §5, p.313 (λ-adic representations); truth from SGA 4 VII Corollaire 5.8 at each level |
| `∀ d M x` | every degree, every coefficient sheaf on `Spec F`, every class |

## Scope

The statement does not cover:

- admissibility for the finite-adelic group, or any comparison of the
  `U`-invariants with the level-`U` cohomology. Harris–Taylor state the
  isomorphism `H^i_et(X_U ×_F F^ac, L_ξ) ≅ H^i_et(X_V ×_F F^ac, L_ξ)^{U/V}`
  on p.96 for their `Q_ℓ^ac`-sheaves; nothing is stated here about invariants
  for a general ring `R`;
- the coefficient sheaves `L_ξ`, ℓ-adic or rational coefficients, or limits
  over torsion coefficients;
- Hecke operators, compact supports, or intersection cohomology;
- any topology on the cohomology modules other than the discrete one;
- local-global compatibility;
- a proof of any premise. The open premises `square`, `q`, `existence`,
  `geometry` and `hRigid` stay open, and the proved ones are not
  instantiated here.

## Registered sources

- `sga4-1972-tome2-verdier-v-original-scan`: SGA 4 Tome 2, Lecture Notes in
  Mathematics 270, original scan, PDF SHA-256
  `7c5b8cef5a99d22785501eead8353641064f858c51ce361b00b310b2bcc46585`.
  Read on the scanned pages (PDF page = printed page + 2): Exposé VII
  (Grothendieck) 5.1, printed pp.356-357; Théorème 5.7, printed p.361;
  Corollaire 5.8, printed p.362. Used only in the truth argument.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), retained file
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
  Proposition 2.2.1, printed p.141 (PDF p.23). Used only in the truth
  argument.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`: Harris–Taylor
  2001, PDF SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`
  (printed page = PDF page - 8); III.2, printed p.96 (PDF p.104, read on a
  rendered image) and p.97 (PDF p.105, read in the text layer). Provenance
  only.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  §5, printed p.313 (PDF p.15). Provenance only.

## Formal dependencies and checks

Direct project import, byte-identical in Library commits
`ce52163e150fe772fdb773627f006a99df1688af` and
`0d9cba336dd98294a5d7f48d772eb708aae40708` and in the workspace. The two
commits have the same files in the import closure of this module (the later
commit only adds files outside it and edits three modules outside it):

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisCoefficients` | Library (no Author line) | `c3cb1700389e02f7f2a558e8fa8883c79c11e2ef6b3e37b3ffe5e76c0d86fecc` | `faba77cb8a8ca89c9bf60f10e9b1e94ffd8f5eee1e810c411acb90981dc9e3e4` |

The module also imports Mathlib's `Mathlib.FieldTheory.KrullTopology`.
Through the import it uses `HarrisTaylorCMSmallLevelIndex` (Author: Worker
57) for `SmallCMLevel` and `OrderedSmallCMLevel`; `EtaleGaloisAction`
(Author: Worker 13) for `baseChangeMap`; `EtaleDerivedSections` (Author:
Worker 13) for the cohomology; and the Library modules
`HarrisTaylorCMSmallLevelCohomology`, `RestrictedLevelColimit`,
`LevelTowerCanonicalCoefficients`, `EtaleDerivedPullback`,
`EtaleInverseImage` and `Representation.Category.Basic`, whose Markdown
files have no Author line. The truth argument cites
`EtaleGeometricCoefficientPullback` and `EtaleInverseImageCoherence`, which
are in the import closure but have no Author line, and is otherwise
independent of the Lean file.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks, against Library `ce52163e` unless stated otherwise, all on the final Lean file (SHA-256
`b3107f973c18f83da777b21c74ead9d1eae46df75aae254fdeda1afc1ffa7f5a`). None
reported errors.

- `6274524d-9895-4fab-a349-1efba2b932fb` built the file from a draft
  directory and inspected `HarrisCMLevelGaloisSmoothStatement`: a
  `Prop`-valued definition with no universe parameters, depending only on
  `propext`, `Classical.choice` and `Quot.sound`. No warnings.
- `63d0dfe7-6700-4a17-a446-2a921864aa5e` compiled a test file
  (`Langlands/Inspect/CMLevelGaloisPrint.lean`, SHA-256
  `02677949e31a203229a97f5c0387ae5e9922e65bbe928a6b7a0ebbc6d0215033`)
  against this Lean file, and its output was read. It printed the
  definition with universes, defined the level-wise form above, and proved
  `statement_imp_levelwise` and
  `levelwise_imp_statement [Nonempty (SmallCMLevel D)]`, both depending only
  on the three standard axioms. Its one warning is a linter suggestion
  (`letI` to `let`) in the test file.
- `f0cecafe-c032-4763-8230-7685b70d936a` compiled a test file
  (`Langlands/Inspect/CMLevelGaloisPremises.lean`, SHA-256
  `8ea8469afd44d5e40c829b7ad921f375ca2275fc61959afcb1ba87e1275e1508`)
  against this Lean file. For each of the fourteen proved premises in the
  table above, an `example` with the premise type at universe zero is closed
  by the cited theorem. `#print axioms` shows that each theorem depends only
  on `propext`, `Classical.choice` and `Quot.sound`.
- `b061e96c-2ac0-4ce2-b64e-e509e345b33b` built the file with Lake from the
  workspace and inspected `HarrisCMLevelGaloisSmoothStatement`: a
  `Prop`-valued definition with no universe parameters, depending only on
  `propext`, `Classical.choice` and `Quot.sound`. No warnings.
- `b8da015c-e6c7-4ba0-9a65-1f8e3be4e130` repeated this workspace Lake build
  over Library `0d9cba33` with the final files, with the same result and the
  same type hash (`79daf658c5d4281bfa206ad2a29ff04ca1a26a23545684448bb31992f06e05e8`).
  No errors or warnings.

This establishes a well-formed statement. It does not prove it.
