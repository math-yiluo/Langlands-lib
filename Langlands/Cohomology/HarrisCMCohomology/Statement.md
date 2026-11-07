# Finiteness and Galois smoothness of geometric CM torsion cohomology

Author: Worker 3, for the Harris and Berkovich cohomological
theorem-statement framework (task `b91b0934-0122-4c05-b359-4e7ed64bbe3d`).

This module states two propositions about Worker 57's étale cohomology of
the geometric CM levels with torsion coefficients. Fix a small CM level `U`,
write `F̄ = AlgebraicClosure F` and `X̄_U = X_U ×_{Spec F} Spec F̄`, and let
`B_r` be the `r`-th stage of Worker 57's original stable-lattice torsion
coefficient system pulled back to `X̄_U`.

- `HarrisCMCohomologyFiniteStatement`: every cohomology module
  `H^d(X̄_U, B_r)` is finite.
- `HarrisCMGaloisCohomologySmoothStatement`: the action of
  `F̄ ≃ₐ[F] F̄` on every `H^d(X̄_U, B_r)` that Worker 57 constructs is
  smooth for the Krull topology: every class is fixed by an open subgroup.
- `HarrisCMCohomologyStatements`: the conjunction of the two, the single
  declaration named in the submission.

Worker 57's Markdown for the Galois action says that it "does not prove
continuity for the profinite Galois topology". The second proposition states
that continuity, in its form for a discrete module. Nothing is proved here.

## Objects

All arithmetic types live in `Type` (universe zero), as in Worker 57's
modules. The binders are copied from
`Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology`. They are:

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
- `U : SmallCMLevel D` and `[Module.Finite ℚ A]`;
- a number field `K`, a finite-dimensional `K`-vector space `W`, an
  algebraic representation
  `ρ : (D.rationalInvolution.baseChange K).AlgebraicRepresentation W`, a
  rational finite place `p`, a natural number `m` with `hm : m ≠ 0`, and the
  premises `existence`, `geometry` and `hRigid` (coarse rigidity at `U.obj`).

### Proof status of the premises

The Lean definitions keep every premise as an explicit hypothesis, as Worker
57's modules do. That a premise is a parameter does not mean that it is
unproved. In Library commit `9b0747799373d61d5b3c3e8fdf95710b5d862db4`,
thirteen of the premise types have published proofs, so a user can pass these
theorems as the corresponding arguments. Check `d9bd054e` (see the checks
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

These proof modules are not imported here. Five premises have no proof in
that commit: a search of its Lean sources found no theorem whose conclusion
is the premise type.

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
- `hRigid`, coarse rigidity at the level `U.obj`. This is a condition on the
  level, not a general theorem. The docstring of `CMGeometricCoarseRigidity`
  says that it "is not inferred from sufficiently small level", and every
  Library module that uses it takes it as a hypothesis.

Since `q` is unproved, both propositions are statements about the objects
that any witness `q` produces. A proof must work for every such witness.

### Notation

Write, as in Worker 57's Markdown:

- `X_U = (cmSchemeTower ... q).obj U`, the scheme chosen from `q`. The
  witness `q U` provides a smooth structure morphism `X_U ⟶ Spec F` and an
  `IsHProjective` witness for it
  (`HarrisTaylorCMRepresentabilityStatement`, fields `smooth` and
  `projective`).
- `X̄_U = (cmGeometricSchemeTower ... q).obj U`. By construction
  `cmGeometricSchemeTower = cmGeometricOverTower ⋙ Over.forget (Spec F̄)`,
  and `cmGeometricSchemeTower_isPullback` proves that `X̄_U` is the fiber
  product `X_U ×_{Spec F} Spec F̄` along `cmGeometricFieldMap`. Let
  `π : X̄_U ⟶ X_U` be the first projection
  `(cmGeometricProjection ... q).app U`.
- `R = HarrisCoefficientIntegers K p`, the product of the coefficient
  valuation rings above `p`.
- `T = cmHarrisCoefficientSystem ... q U ρ p m hm existence geometry hRigid`,
  a functor from `ℕᵒᵖ` to sheaves of `R`-modules on the small étale site of
  `X_U`. Write `A_r = T.obj r`.
- `S̄ = cmHarrisGeometricCoefficientSystem ... = T ⋙ inverseImage π R`
  and `B_r = S̄.obj r = π^* A_r`. Here `EtaleInverseImage.inverseImage π R`
  is the Library's inverse image of small-étale sheaves of `R`-modules: a left
  Kan extension followed by sheafification, left adjoint to the direct image.
- `H_d = EtaleDerivedSections.cohomology X̄_U R d`, the `d`-th right derived
  functor of global sections on `Sheaf (Scheme.smallEtaleTopology X̄_U)
  (ModuleCat.{0} R)`, computed with injective resolutions (Worker 13).
- `cmHarrisGeometricCoefficientCohomologySystem ... d = S̄ ⋙ H_d`, a
  functor `ℕᵒᵖ ⥤ ModuleCat.{0} R`. Its value at `r` is `H_d(B_r)`.

The Galois action:

- `G = F̄ ≃ₐ[F] F̄`, with Mathlib's Krull topology, the only topology
  instance on this type.
- `g_σ = (cmGeometricGaloisMap ... q σ).app U : X̄_U ⟶ X̄_U` is
  `pullback.lift` of the first projection and of the second projection
  followed by `cmGeometricGaloisBaseMap σ = Spec.map σ`. So it is the
  identity on the factor `X_U` and `Spec σ` on the factor `Spec F̄`.
  Worker 57 proves `g_σ ≫ π = π` (`cmGeometricGaloisMap_app_projection`)
  and `g_(σ * τ) = g_σ ≫ g_τ` (`cmGeometricGaloisMap_mul`).
- `Ψ_σ = cmHarrisGeometricCoefficientGaloisIso ... σ`. By
  `cmHarrisGeometricCoefficientGaloisIso_hom_app` and the definition of
  `cmGeometricGaloisInverseImageIso`, its components are
  `Ψ_σ.hom.app r = (inverseImageComp R π g_σ).hom.app A_r ≫
  (inverseImageCongr R (g_σ ≫ π = π)).hom.app A_r`. This is the canonical
  isomorphism `g_σ^* (π^* A_r) ≅ (g_σ ≫ π)^* A_r = π^* A_r`.
- `cmHarrisGeometricGaloisCohomologyAction ... d : ℕᵒᵖ ⥤ Action (ModuleCat R) G`
  is Worker 57's action. Its object at `r` has underlying module
  `H_d(B_r)`, and `cmHarrisGeometricGaloisCohomologyAction_obj_ρ` identifies
  the operator of `σ` with
  `cohomologyPullbackWithCoefficients g_σ R d (Ψ_σ.hom.app r)`. By definition
  this is `(cohomologyPullback g_σ R d).app B_r ≫ H_d.map (Ψ_σ.hom.app r)`:
  pullback along `g_σ` into `H_d(g_σ^* B_r)`, followed by the canonical
  coefficient isomorphism back to `H_d(B_r)`. Worker 57 records the law
  `ρ (σ * τ) = ρ τ ≫ ρ σ`, so this is a left action.
- `Rep.ActionToRep R G` is Mathlib's functor from `Action (ModuleCat R) G` to
  `Rep R G`. Its `.ρ` is the representation `G →* (H_d(B_r) →ₗ[R] H_d(B_r))`
  whose value at `σ` is the operator above.
- `Langlands.IsSmooth ρ` (Library, `Representation.Smooth.Definitions`):
  every vector `v` has an open subgroup `V` with `ρ σ v = v` for all `σ ∈ V`.
- The action construction needs the instances
  `[HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf X̄_U R)]` and
  `[HasDerivedCategory.{wR} (ModuleCat.{0} R)]`. They are binders of the
  smoothness statement only. They fix sizes of localizations and do not
  change the module `H_d(B_r)`.

## The propositions

```lean
def HarrisCMCohomologyFiniteStatement : Prop :=
  ∀ (degree : ℕ) (r : ℕᵒᵖ),
    Finite ((cmHarrisGeometricCoefficientCohomologySystem D C preservation composition
      unitCoherence associativity comparison symmetry stability square universality
      dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
      existence geometry hRigid degree).obj r)

def HarrisCMGaloisCohomologySmoothStatement : Prop :=
  ∀ (degree : ℕ) (r : ℕᵒᵖ),
    Langlands.IsSmooth ((Rep.ActionToRep Rcoeff Galois).obj
      ((cmHarrisGeometricGaloisCohomologyAction D C preservation composition
        unitCoherence associativity comparison symmetry stability square universality
        dualityNaturality polarizationStability compatibility h htor q U ρ p m hm
        existence geometry hRigid degree).obj r)).ρ

def HarrisCMCohomologyStatements : Prop :=
  HarrisCMCohomologyFiniteStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid ∧
    HarrisCMGaloisCohomologySmoothStatement D C preservation composition unitCoherence
      associativity comparison symmetry stability square universality dualityNaturality
      polarizationStability compatibility h htor q U ρ p m hm existence geometry hRigid
```

Here `Rcoeff` is local notation for `HarrisCoefficientIntegers K p` and
`Galois` for `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`.

In words: for every degree `d` and every coefficient stage `r`,

1. the `R`-module `H^d(X̄_U, B_r)` has finitely many elements;
2. every class in `H^d(X̄_U, B_r)` is fixed by an open subgroup of
   `F̄ ≃ₐ[F] F̄`, where `σ` acts by pullback along `g_σ` followed by `Ψ_σ`.

`Finite` applies to the carrier of the module. The finiteness statement
does not need the derived-category instances, so it comes before them in the
file and has no universe parameters. The smoothness statement has the two
universe parameters `wS` and `wR` of those instances. The conjunction
`HarrisCMCohomologyStatements` comes after the instances, so it has the same
binders as the smoothness statement, including the two instances, and the
universe parameters `wS` and `wR`. Its first component does not use the
instances.

## Why the statements are expected to hold

These arguments are derived. They combine the cited results of SGA 4 with
Library facts and are not quotations.

### Finiteness

1. *`X̄_U` is proper over a separably closed field.* `F̄` is algebraically
   closed, hence separably closed. The Library instance
   `cmGeometricOverTower_isProper` (module
   `Langlands.Shimura.PEL.HarrisTaylorCMGeometricProjective`, not imported
   here) proves that `X̄_U ⟶ Spec F̄` is proper, from the `IsHProjective`
   witness in `q`.
2. *The coefficient sheaves on `X_U` are locally constant with finite value.*
   Let `Y_r` be the original coefficient cover at stage `r`, an étale
   `X_U`-scheme. `cmHarrisCoefficientSystemTrivialization r` gives an
   isomorphism between the restriction of `A_r` to `Y_r` and the restriction
   of the constant sheaf with value `M_r`, the coefficient module at stage
   `r`. `cmHarrisCoefficientEtaleDiagram_coversTop r` proves that `Y_r`
   covers the final object of the small étale site of `X_U`, so `Y_r ⟶ X_U`
   is an étale covering. `cmHarrisCoefficientDiagram_finite` proves that
   `M_r` is finite. So `A_r` is locally constant with finite value.
3. *The coefficient sheaves on `X̄_U` are constructible and torsion.* The
   witness in `q` makes `X_U ⟶ Spec F` projective, hence proper, hence
   quasi-compact and separated. Since `Spec F` is affine, `X_U` is
   quasi-compact and quasi-separated. SGA 4 IX Proposition 2.4(i), applied
   to the decomposition of `X_U` into one piece, shows that `A_r` is
   constructible. By IX 2.3.1 this holds for `A_r` as a sheaf of sets, as a
   sheaf of groups and as a sheaf of `ℤ`-modules, since its stalks are
   finite. The Library inverse image is left adjoint to the direct image, so
   it agrees with the inverse image of SGA 4. By IX Proposition 2.4(iii),
   `B_r = π^* A_r` is constructible. It is torsion:
   `cmHarrisGeometricCoefficientSystem_powSMul_eq_zero` proves that
   multiplication by `m^r` is zero on `B_r`, and `m ≠ 0`.
4. *Finiteness.* SGA 4 XIV Corollaire 1.2: for a scheme `X` proper over the
   spectrum of a separably closed field and a constructible torsion abelian
   sheaf `F` on `X`, the groups `H^q(X, F)` are finite for every `q ≥ 0`.
   Apply it to `X̄_U` and the underlying abelian sheaf of `B_r`.
5. *Comparison of sites and coefficients.* This is step 4 of
   [EtaleGaloisSmooth](../EtaleGaloisSmooth/Statement.md). Mathlib's
   `smallEtaleTopology` is the étale site of SGA 4 VII 1.2. An injective
   sheaf of `R`-modules is flasque (SGA 4 V 4.6), flasqueness depends only
   on the underlying abelian sheaf (V 4.4), and flasque sheaves are acyclic
   (V 4.1). So the injective resolution used by `H_d` is an acyclic
   resolution of the underlying abelian sheaves, and it computes their
   cohomology (Tôhoku §2.4, Remark 3). Hence the carrier of `H_d(B_r)` is in
   bijection with the finite group of step 4.

No hypothesis on `m`, `p`, `K` or the characteristic is used beyond
`m ≠ 0`. XIV 1.2 has no condition relating the torsion to the
characteristic, and `F̄` has characteristic zero.

### Smoothness

1. *Reduction to finite subextensions.* Let `E` range over the intermediate
   fields of `F̄ / F` that are finite-dimensional over `F`. The subgroups
   `E.fixingSubgroup` are open for the Krull topology
   (`IntermediateField.fixingSubgroup_isOpen`). It suffices to find, for
   each class `c ∈ H^d(X̄_U, B_r)`, such an `E` whose fixing subgroup fixes
   `c`.
2. *`X̄_U` is a limit.* `F̄` is algebraic over `F`, so it is the filtered
   union of the fields `E`. Put `X_E = X_U ×_{Spec F} Spec E`, with
   projections `u_E : X_E ⟶ X_U` and `p_E : X̄_U ⟶ X_E`, so that
   `p_E ≫ u_E = π`. Each `X_E` is quasi-compact and quasi-separated, by base
   change from step 3 of the finiteness argument. The transition maps are
   base changes of the affine maps `Spec E' ⟶ Spec E`, hence affine. The limit
   of the system is `X̄_U` (SGA 4 VII 5.1).
3. *The limit theorem.* SGA 4 VII Corollaire 5.8, with `i₀` the index `F`,
   `X_{i₀} = X_U` and `F_{i₀} = A_r`, says that the canonical map
   `colim_E H^d(X_E, u_E^* A_r) ⟶ H^d(X̄_U, π^* A_r)` is an isomorphism.
   Each component is pullback along `p_E` followed by the canonical
   isomorphism `p_E^* u_E^* A_r ≅ π^* A_r`. Hence `c = p_E^*(c_E)` for some
   `E` and some `c_E ∈ H^d(X_E, u_E^* A_r)`. Step 5 of the finiteness
   argument identifies the Lean cohomology with that of SGA 4. The Lean
   `cohomologyPullback` is the pullback map of SGA 4: both are morphisms of
   δ-functors in the coefficient sheaf that agree in degree zero, and the
   source is a universal δ-functor (Tôhoku Proposition 2.2.1).
4. *Classes from `X_E` are fixed by `E.fixingSubgroup`.* Let `σ` fix `E`
   pointwise. Then `g_σ ≫ p_E = p_E`: on the factor `X_U` both sides are the
   identity, and `Spec σ` followed by `Spec F̄ ⟶ Spec E` is
   `Spec F̄ ⟶ Spec E` because `σ` is the identity on `E`. The operator of
   `σ` is pullback along `g_σ` followed by the canonical isomorphism `Ψ_σ`.
   Pullbacks compose: the Library proves
   `sheafDerivedPullbackWithCoefficients_comp`, and
   `sheafDerivedPullbackWithCoefficients_homology` transports it to
   `cohomologyPullbackWithCoefficients`. So `σ · p_E^*(c_E)` is pullback
   along `g_σ ≫ p_E = p_E` with a coefficient map built from the canonical
   inverse-image isomorphisms `inverseImageComp` and `inverseImageCongr`.
   That map is again the canonical isomorphism `p_E^* u_E^* A_r ≅ π^* A_r`.
   This follows from the associativity coherence of these isomorphisms
   (`inverseImageComp_assoc`) and their compatibility with equality
   transport. Hence `σ · c = p_E^*(c_E) = c`. This step is derived; the
   schemes `X_E` are not Library objects, and the cited lemmas hold for
   arbitrary morphisms of schemes.

By step 1, `c` is a smooth vector. Nothing here uses finiteness of `A_r`,
the ring `R` or the degree `d`. The argument only needs `X_U` quasi-compact
and quasi-separated over `F`.

## Provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*
(1999), §4, printed p.311, descends the constant étale sheaf on
`S(GG, X_{n-1})_{K(N_m)}` to a lisse étale sheaf on
`S(GG, X_{n-1})_{K(N)}` and obtains the spectral sequence (4.9), whose
abutment is the cohomology `H^{i+j}(S_K(N), ·)` with coefficients in that
lisse sheaf. The proof of Proposition 4.10, printed p.312, says: "Since the
right-hand side of the spectral sequence (4.9) is a finite group for all
`m`, the complexes in (4.10.2) satisfy a Mittag-Leffler condition". §5,
printed p.313, works with "λ-adic representations σ of Gal(F̄/F)", and
Theorem 5.7 concerns the representation of `Gal(F̄/F)` on
`H^{n-1}(S_K(N), W)[π]`. At a finite torsion coefficient stage, continuity
of an action on a discrete module is exactly the smoothness stated here.

Harris–Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), III.2, printed p.97, say of the cohomology `H^i(X, L_ξ)`
defined on p.96: "Thus `H^i(X, L_ξ)` becomes an admissible
`G(A^∞)`-module, in fact an admissible/continuous
`G(A^∞) × Gal(F^ac/F)`-module." The quotation is from the text layer, where
the slash is rendered as "j". Worker 57's construction follows Harris–Taylor
III.1-III.2.

Both statements are analogues for the Library's objects. Harris's `S_K(N)`
and sheaves `F_m` are not the Library's `X̄_U` and `B_r`. Worker 57's levels
are the Harris–Taylor CM PEL levels, conditional on the premises above. The
statements are at one fixed level `U` and one fixed coefficient stage `r`,
before any limit over levels or coefficients. Neither source states them as
separate results.

| Lean | Source |
| --- | --- |
| `Finite (H_d(B_r))` | Harris 1999, proof of Proposition 4.10, p.312 (finiteness of the abutment of (4.9)); truth from SGA 4 XIV Corollaire 1.2 |
| `X̄_U = X_U ×_{Spec F} Spec F̄`, `B_r = π^* A_r` | Harris–Taylor III.2, pp.94-96, as constructed by Worker 57 |
| `Langlands.IsSmooth` for the Krull topology on `F̄ ≃ₐ[F] F̄` | Harris–Taylor p.97 ("continuous"); Harris 1999 §5, p.313 (λ-adic representations); truth from SGA 4 VII Corollaire 5.8 |
| `∀ degree r` | Every degree and every coefficient stage |

## Scope

The statements do not cover:

- limits over levels `U`, ℓ-adic or rational coefficients, or the inverse
  limit over `r`;
- Hecke operators, compact supports, or intersection cohomology;
- any topology on the cohomology modules other than the discrete one;
- local-global compatibility, Harris 1999 Theorem 5.7 itself, or the
  spectral sequence (4.9);
- a proof of any premise. The open premises `square`, `q`, `existence`,
  `geometry` and `hRigid` stay open, and the proved ones are not
  instantiated here.

## Registered sources

- `sga4-1972-tome2-verdier-v-original-scan`: SGA 4 Tome 2, Lecture Notes in
  Mathematics 270, original scan, PDF SHA-256
  `7c5b8cef5a99d22785501eead8353641064f858c51ce361b00b310b2bcc46585`.
  Read on the scanned pages (PDF page = printed page + 2):
  - Exposé V (Verdier): Definition 4.1, 4.4 and 4.6, printed pp.29-30;
  - Exposé VII (Grothendieck): 1.2, printed p.343;
  - VII 5.1, printed pp.356-357;
  - VII Théorème 5.7, printed p.361;
  - VII Corollaire 5.8, printed p.362.
- `sga4-1973-tome3-deligne-xvii-original-scan`: SGA 4 Tome 3, Lecture Notes
  in Mathematics 305, original scan, PDF SHA-256
  `702fa23766ccec841d31ce0f21dfaacff8d8d31d4153de386587a27a4c01107a`.
  Read on the scanned pages (PDF page = printed page + 3):
  - Exposé IX (Artin): Définition 2.3, 2.3.1 and Proposition 2.4,
    printed pp.8-9;
  - Exposé XIV (Artin): Corollaire 1.2, printed p.145.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), retained file
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
  Proposition 2.2.1, printed p.141 (PDF p.23), and §2.4, Remark 3 after
  Theorem 2.4.1, printed p.148 (PDF p.30). Used only in the truth arguments.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris
  1999, PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  §4, printed pp.311-312 (PDF pp.13-14), and §5, printed p.313 (PDF p.15).
  Provenance only.
- `harris-taylor-2001-geometry-cohomology-simple-shimura`: Harris–Taylor
  2001, PDF SHA-256
  `5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`
  (printed page = PDF page - 8); III.2, printed p.97 (PDF p.105), read in
  the text layer. Provenance only.

## Formal dependencies and checks

Direct project imports, byte-identical in Library commits
`6f182f920309bbe9e9e43bd7181d7e25d5c02acd` and
`9b0747799373d61d5b3c3e8fdf95710b5d862db4` and in the workspace:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Shimura.PEL.HarrisTaylorCMGeometricCohomology` | Worker 57 | `9bda75d25c33eee453fa43c68881e124d706aea5ca9c3f0f90358d703d9ad824` | `a3ed52de2897e8989a71b2a01edb087310e622ae6dae6d6004c100dc09dea97b` |
| `Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCohomology` | Worker 57 | `e7f01f64e60e606662cb0adeebb1c8c49573b552311129ee4ff8c5bbb3213f27` | `66fae2ad97f30b2658051f14135ae87e7e339b1455f95fcda9ff597be7ec9cde` |
| `Langlands.Representation.Smooth.Definitions` | Library | `435abfa2c0b05c1b6ea8107e3278687e7091e481540508d6647befc0f515aabb` | `4b7364038949eb59db10c95354f290fcba77110c1ed33a227a2b6c92f4afd569` |

The module also imports Mathlib's `Mathlib.FieldTheory.KrullTopology`.
Through the imports it uses Worker 13's `EtaleDerivedSections` and
`EtaleDerivedGlobalPullback`, and the Library's `EtaleInverseImage` and
`EtaleGeometricCoefficientPullback`. The truth arguments also cite
`HarrisTaylorCMGeometricProjective` and `EtaleInverseImageCoherence`, which
are not imported.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks, all with no errors or warnings. The first five ran before the
conjunction `HarrisCMCohomologyStatements` was added. The file then held
only the two component definitions, unchanged since.

- `dc8bfcaa-0382-411f-823a-560cf1427e12` built the file from a draft
  directory against Library `7c489c8a` and inspected
  `HarrisCMGaloisCohomologySmoothStatement`: a `Prop`-valued definition
  depending only on `propext`, `Classical.choice` and `Quot.sound`.
- `9f71a614-b496-4cc9-adb1-1d0cd5f1d56d` inspected
  `HarrisCMCohomologyFiniteStatement` in the same way, with the same three
  axioms.
- `67067043-19d3-476e-9760-19b41cc653a2` compiled a test file against the
  same Lean file, and its output was read. It printed both definitions with
  universes: the finiteness statement has no universe parameters and no
  derived-category binders, and the smoothness statement has the universe
  parameters `wS` and `wR`. It proves by `Iff.rfl` that the finiteness
  statement says `Finite` of
  `(EtaleDerivedSections.cohomology X̄_U R degree).obj (S̄.obj r)`. It proves
  that the smoothness statement is equivalent to: for all `degree`, `r` and
  `v`, some open subgroup `V` has
  `cohomologyPullbackWithCoefficients g_σ R degree (Ψ_σ.hom.app r) v = v`
  for all `σ ∈ V`.
- `7b24577e-75f0-419a-8949-83d441083466` rebuilt the draft against Library
  `6f182f92`.
- `cee79411-4fb7-492c-8401-e7a5c69bdb76` built the file with Lake from the
  workspace, against Library `6f182f92`, and inspected
  `HarrisCMGaloisCohomologySmoothStatement`: a `Prop`-valued definition with
  universe parameters `wS` and `wR`, depending only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `abdad739-6c23-4917-a2a1-f051eee81e43` built the final file from a draft
  directory against Library `6f182f92` and inspected
  `HarrisCMCohomologyStatements`: a `Prop`-valued definition with universe
  parameters `wS` and `wR`, depending only on `propext`, `Classical.choice`
  and `Quot.sound`.
- `624913c1-f278-47c6-b685-e08ef189bc99` built the final file with Lake from
  the workspace, against Library `6f182f92`, and inspected
  `HarrisCMCohomologyStatements` with the same result.
- `d9bd054e-2711-4cac-adb5-b7f136bb54ec` compiled a test file against this
  Lean file and Library `9b074779`. For each of the thirteen proved premises
  in the table above, an `example` with the premise type at universe zero is
  closed by the cited theorem. `#print axioms` shows that each theorem
  depends only on `propext`, `Classical.choice` and `Quot.sound`.
- `3a562bdb-db99-42ce-a3d9-6467a158c4fc` built the file with Lake from the
  workspace, against Library `9b074779`, and inspected
  `HarrisCMCohomologyStatements`: a `Prop`-valued definition with universe
  parameters `wS` and `wR`, depending only on `propext`, `Classical.choice`
  and `Quot.sound`. The Lean file is unchanged since `abdad739`.

This establishes well-formed statements. It does not prove them.
