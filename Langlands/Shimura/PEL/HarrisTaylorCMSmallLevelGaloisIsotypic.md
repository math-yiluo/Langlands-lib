# Isotypic parts and multiplicity spaces of towers over sufficiently small CM levels, and their Galois representations

This internal construction applies the generic modules
`Langlands.Shimura.ScalarExtensionFixedVectors` and
`Langlands.Shimura.ContinuousIsotypicGaloisRepresentation` to the towers of
`Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisTower`. The input is a
level-trivial presheaf `H` of `K`-modules on the sufficiently small CM levels,
with an action of `Gal(F̄/F)` at every level. Extend the scalars of the tower
`colim_U H(U)` to a field `M` over `K`. For a representation `τ` of the
finite-adelic similitude group `G(A_f)` over `M`, the module defines four
spaces, each with its action of `Gal(F̄/F)`:

- the `τ`-isotypic part;
- its fixed vectors at a level;
- the multiplicity space;
- the Hecke multiplicity space at a level.

It proves that the evaluation map onto the isotypic part is surjective and
Galois-equivariant. Under the fixed-vector comparison it identifies the fixed
vectors at the level of `U` with `M ⊗[K] H(U)` as Galois actions. If moreover
`H(U)` is finite-dimensional with continuous orbit maps, the fixed vectors of
the isotypic part and the two multiplicity spaces, when finite-dimensional,
are continuous Galois representations of `F` over `M`. At places where `H(U)`
is unramified, their Euler polynomials are the reversed characteristic
polynomials of geometric Frobenius. All declarations are in namespace
`Langlands.Shimura.SmallLevelGaloisTower`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §5, printed p. 312, considers "the `JL(π_f)`-isotypic component of
`H^{n-1}(S_K(N), W)`, which we denote `H^{n-1}(S_K(N), W)[π]`". Here `JL(π_f)`
is an irreducible admissible representation of `GG(A_f)` and `K(N)` a level.
On printed p. 313 he considers `λ`-adic representations `σ` of `Gal(F̄/F)`
unramified at almost all places, and defines their local factors (5.6) by the
eigenvalues `β` of `σ(Fr_w)` for a geometric Frobenius `Fr_w`. Kottwitz (1992),
*On the λ-adic representations associated to some simple Shimura varieties*,
§1, printed p. 655, uses the Hecke multiplicity space
`W^i(π_f) = Hom_{H_K}(π_f^K, H^i(S_K, F))`, with the commuting Galois action
on `W^i(π_f) ⊗ L_λ`.

The intended input `H` is the `λ`-adic cohomology
`U ↦ H^d(S_U ×_F F̄, W)_λ` of the CM tower with Harris's coefficient systems,
with `K = K_λ`. Then `towerExtendScalars M H hH` is
`H^d(S, W)_λ ⊗_{K_λ} M`, and `towerIsotypicFixedVectors M H hH τ U` is
Harris's `H^{n-1}(S_K(N), W)[π]` for `d = n - 1`, `τ = JL(π_f)` and level
`K(N)`. This module does not use that input: `H` is an arbitrary level-trivial
presheaf. The module proves no finiteness, continuity, unramifiedness or
fixed-vector comparison; all of these are hypotheses. No statement of Harris
or Kottwitz is formalized here.

## Inputs

- `Langlands.Shimura.PEL.HarrisTaylorCMSmallLevelGaloisTower`: for an
  involution `σ` of a finite-dimensional `ℚ`-algebra `B` and a level-trivial
  `H : σ.SmallLevelCategoryᵒᵖ ⥤ Action (ModuleCat K) Γ` (`hH : IsLevelTrivial H`):
  - `towerAction H hH : Action (SmoothRep K σ.FiniteAdelicPoints) Γ`, the
    colimit of `H` over the sufficiently small levels, on which
    `g ∈ σ.FiniteAdelicPoints` acts as `op g⁻¹`;
  - `towerFixedLeg H hH U`, the `Γ`-equivariant map from `H(U)` to the vectors
    fixed by the ordinary level `inverseOpposite U`;
  - the proposition `TowerFixedVectorComparison H` that these maps are
    bijective for every level, and the isomorphism `towerFixedLegIso` under it.
- `Langlands.Shimura.ScalarExtensionFixedVectors`:
  - `extendScalarsActionFunctor M Γ`, extension of scalars `X ↦ M ⊗[K] X` on
    `Action (SmoothRep K G) Γ`;
  - `fixedVectorsBaseChangeIso`, the isomorphism of Galois actions
    `M ⊗[K] X^H ≅ (M ⊗[K] X)^H`;
  - `finite_fixedVectors_extendScalars`,
    `hasContinuousOrbits_fixedVectors_extendScalars` and
    `isUnramifiedAlong_fixedVectors_extendScalars`.
- `Langlands.Shimura.ContinuousIsotypicGaloisRepresentation`:
  - `isotypicFixedVectorsObjects`, `multiplicityObjects` and
    `heckeMultiplicityContinuousObjects`, with their Euler polynomial lemmas;
  - `coe_isotypicFixedVectorsObjects_representation_apply`.
- `Langlands.Shimura.ContinuousOrbitTransfer`:
  `hasContinuousOrbits_of_surjective` and `isUnramifiedAlong_of_surjective`.
  The published `Langlands.Shimura.ContinuousOrbitGaloisAction` provides
  `HasContinuousOrbits`: every orbit map `g ↦ g · x` is continuous for the
  module topology.
- `Langlands.Shimura.IsotypicGaloisAction`:
  - `isotypicActionFunctor τ Γ`, the isotypic part `isotypicPart τ ρ`, which
    is the sum of the images of all intertwining maps `τ → ρ`;
  - `multiplicityActionFunctor τ Γ`, the space of intertwining maps
    `Hom_G(τ, X)`, with `Γ` acting by composition;
  - `isotypicEvaluation τ A : V ⊗ Hom_G(τ, A) → A[τ]`, `u ⊗ φ ↦ φ u`, with
    `isotypicEvaluation_surjective`, `isotypicEvaluation_galois`,
    `multiplicityRepresentation` and `isotypicGaloisRepresentation`.
- `Langlands.Shimura.HeckeMultiplicityGaloisRepresentation`:
  `heckeMultiplicityActionFunctor K T Γ`, the space of Hecke-linear maps
  `Hom_{H(K)}(T, X^K)` over the published `LevelHecke.LevelHeckeAlgebra M K`,
  with `Γ` acting by composition.
- `Langlands.Shimura.LatticeGaloisRepresentation`: `baseChangeAction`, the
  Galois action on `M ⊗[K] A` for a Galois action `A` over `K`.
- `Langlands.Shimura.DecompositionGroupAction`: `IsUnramifiedAt`,
  `IsUnramifiedAlong` (unramified along a closure embedding `ι` at `v`),
  `isUnramifiedAt_iff_along`, `geometricFrobenius`.
- `Langlands.GaloisRepresentation`: `Objects F M`, the continuous
  finite-dimensional Galois representations of `F` over `M`, and
  `HasEulerPolynomialAt`.

## Declarations

Throughout, `B` is a finite-dimensional `ℚ`-algebra with an involution `σ`.
`F` and `K` are fields, `Γ = Field.absoluteGaloisGroup F`, and `M` is a field
with `[Algebra K M]`. Further, `H : σ.SmallLevelCategoryᵒᵖ ⥤ Action (ModuleCat K) Γ`
with `hH : IsLevelTrivial H`. For a sufficiently small level `U`, write
`K_U = inverseOpposite U`, the ordinary compact open subgroup of
`σ.FiniteAdelicPoints` attached to `U`. Let `τ : Representation M σ.FiniteAdelicPoints V`
be a representation on an `M`-module `V`; no smoothness or irreducibility is
assumed.

### Spaces

- `towerExtendScalars M H hH` is
  `(extendScalarsActionFunctor M Γ).obj (towerAction H hH)`: the tower
  `M ⊗[K] colim_U H(U)` as a smooth representation of `σ.FiniteAdelicPoints`
  over `M`, with the commuting action of `Γ`. Write `X_M` for it.
- `towerIsotypic M H hH τ` is the `τ`-isotypic part of `X_M`, with the
  restricted actions of `σ.FiniteAdelicPoints` and `Γ`.
- `towerIsotypicFixedVectors M H hH τ U` is the vectors of the `τ`-isotypic
  part fixed by `K_U`, with the action of `Γ`.
- `towerMultiplicity M H hH τ` is `Hom_{G(A_f)}(τ, X_M)`, with `Γ` acting by
  composition.
- `towerHeckeMultiplicity M H hH τ U` is
  `Hom_{H(K_U)}(τ^{K_U}, X_M^{K_U})`, with `Γ` acting by composition. Here
  `H(K_U)` is the published level Hecke algebra of `K_U` over `M`, and
  `τ^{K_U}` and `X_M^{K_U}` are modules over it by the published
  `instModuleFixedVectors`.
- `towerIsotypicEvaluation_surjective`: the evaluation map
  `V ⊗ Hom_{G(A_f)}(τ, X_M) → X_M[τ]` is surjective.
- `towerIsotypicEvaluation_galois`: for every `γ ∈ Γ`, the evaluation map
  intertwines `id ⊗ γ` on `V ⊗ Hom_{G(A_f)}(τ, X_M)`, with `γ` acting by
  composition, and the action of `γ` on `X_M[τ]`.

### Fixed vectors at a level

- `towerFixedLeg_comm`: the leg `towerFixedLeg H hH U` commutes with the
  actions of `Γ`.
- `towerFixedLeg_surjective h U`: under
  `h : TowerFixedVectorComparison H`, the leg of level `U` is surjective onto
  the `K_U`-fixed vectors of the tower.
- Under `h`, with `[Module.Finite K H(U)]`, `hU : HasContinuousOrbits H(U)`, or
  `hu : IsUnramifiedAt (ModuleCat K) v H(U)` for a finite place `v` of a number
  field `F`, the same holds for the `K_U`-fixed vectors of the tower:
  `finite_towerFixedVectors`, `hasContinuousOrbits_towerFixedVectors`, and
  `isUnramifiedAlong_towerFixedVectors` (along every closure embedding `ι` at
  `v`).
- For `X_M^{K_U}`, with `hKM : Continuous (algebraMap K M)` for continuity:
  `finite_towerExtendScalarsFixedVectors`,
  `hasContinuousOrbits_towerExtendScalarsFixedVectors`, and
  `isUnramifiedAlong_towerExtendScalarsFixedVectors`.
- `baseChangeActionMapIso M e`: for an isomorphism `e : A ≅ B` of Galois
  actions over `K`, the induced isomorphism
  `baseChangeAction A ≅ baseChangeAction B` of Galois actions over `M`, by
  `LinearEquiv.baseChange`.
- `towerExtendScalarsFixedVectorsIso M h U`: under `h`, the isomorphism of
  Galois actions between `M ⊗[K] H(U)` (`baseChangeAction`) and `X_M^{K_U}`.
  It is `baseChangeActionMapIso` of `towerFixedLegIso` followed by
  `fixedVectorsBaseChangeIso`. Through it, `towerHeckeMultiplicity M H hH τ U`
  corresponds to Kottwitz's Hecke multiplicity space
  `Hom_{H(K_U)}(τ^{K_U}, H(U) ⊗_K M)`, for the Hecke module structure on
  `H(U) ⊗_K M` transported from `X_M^{K_U}`. The module states no Hecke-linear
  property of this isomorphism; the Hecke algebra acts only on `X_M^{K_U}`.

### Galois representations

Assume topologies on `K` and `M` with `M` a topological ring, and
`hKM : Continuous (algebraMap K M)`. Assume `h : TowerFixedVectorComparison H`,
a level `U`, and `hU : HasContinuousOrbits H(U)`. Here `hH` is an explicit
argument.

- `towerIsotypicFixedVectorsObjects M hH hKM h U hU τ : Objects F M`, for
  `[Module.Finite K H(U)]`, is the Galois representation on
  `towerIsotypicFixedVectors M H hH τ U`, through `isotypicFixedVectorsObjects`.
  `coe_towerIsotypicFixedVectorsObjects_representation_apply`: `γ` acts on a
  fixed vector of the isotypic part as on `X_M`.
- `towerMultiplicityObjects M hH hKM h U hU τ hgen : Objects F M` is the
  Galois representation on `towerMultiplicity M H hH τ`, through
  `multiplicityObjects`. It needs `[Module.Finite M Hom_{G(A_f)}(τ, X_M)]` and
  `hgen`: `V` is spanned by the translates `τ g u` of the `K_U`-fixed vectors
  `u`. Under `hgen`, `finite_multiplicity` of
  `ContinuousIsotypicGaloisRepresentation` gives the finiteness when
  `τ^{K_U}` and `X_M^{K_U}` are finite-dimensional.
- `towerHeckeMultiplicityObjects M hH hKM h U hU τ : Objects F M` is the
  Galois representation on `towerHeckeMultiplicity M H hH τ U`, through
  `heckeMultiplicityContinuousObjects`. It needs the Hecke multiplicity space
  to be finite-dimensional over `M` (instance argument).
  `finite_heckeMultiplicity` of `ContinuousIsotypicGaloisRepresentation` gives
  this when `τ^{K_U}` is finitely generated
  over the Hecke algebra and `X_M^{K_U}` is finite-dimensional.
- `towerMultiplicityObjects_representation_apply` and
  `towerHeckeMultiplicityObjects_representation_apply`: the representation is
  the action of `Γ` on the space.
- Euler polynomials. Let `F` be a number field, `v` a finite place of `F`,
  `ι` a closure embedding at `v`, and `hu : IsUnramifiedAt (ModuleCat K) v H(U)`.
  Then `hasEulerPolynomialAt_towerIsotypicFixedVectorsObjects`,
  `hasEulerPolynomialAt_towerMultiplicityObjects` and
  `hasEulerPolynomialAt_towerHeckeMultiplicityObjects` state that the
  representation has Euler polynomial at `v` equal to
  `(geometricFrobenius (ModuleCat M) v A ι).hom.charpoly.reverse`, where `A` is
  the space of the representation. This is the reversed characteristic
  polynomial `det(1 − X · σ(Fr_v))` of the geometric Frobenius along `ι`. For
  the isotypic fixed vectors, the statement uses the finiteness of
  `X_M^{K_U}` from `finite_towerExtendScalarsFixedVectors`, which the
  characteristic polynomial needs.

## Provenance

This is an internal construction. It applies the generic modules
`ScalarExtensionFixedVectors`, `ContinuousIsotypicGaloisRepresentation` and
`ContinuousOrbitTransfer` to the towers of `HarrisTaylorCMSmallLevelGaloisTower`.
The objects are those of Harris (1999), §5:

- printed p. 312 (PDF p. 14), "the `JL(π_f)`-isotypic component of
  `H^{n-1}(S_K(N), W)`, which we denote `H^{n-1}(S_K(N), W)[π]`";
- printed p. 313 (PDF p. 15), `λ`-adic representations unramified at almost
  all places and the local factor (5.6) through the eigenvalues of `σ(Fr_w)`
  for a geometric Frobenius `Fr_w`.

The source is `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`,
PDF SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`. The Hecke
multiplicity space is that of Kottwitz (1992), §1, printed p. 655:
`W^i(π_f) = Hom_{H_K}(π_f^K, H^i(S_K(C), F))` with the commuting Galois
action. The source is `kottwitz-1992-lambda-adic-simple-shimura`, SHA-256
`749af5541a59187e6f9d1089dec9a0e591a2059173da739c7384ff3a7d0dd799`.

The Euler polynomial is the Library's `HasEulerPolynomialAt`, the reversed
characteristic polynomial of a geometric Frobenius. Its roots are the inverses
of the eigenvalues `β` in (5.6). The normalization of (5.6) by `|β|` is not
formalized. The fixed-vector comparison (Harris–Taylor 2001, III.2) is the
hypothesis `TowerFixedVectorComparison`, not a theorem.
