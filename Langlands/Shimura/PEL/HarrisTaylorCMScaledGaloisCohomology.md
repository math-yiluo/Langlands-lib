# Harris's coefficient systems on the geometric CM tower over scaled levels, with Galois action

This module takes the published coefficient diagram
`cmHarrisScaledCoefficientDiagram` of Harris's coefficient systems over scaled
levels and torsion stages, which lives on the CM schemes `X_U` over the reflex
field `F`. It pulls the diagram back to the geometric levels
`X̄_U = X_U ×_F F̄`, adding the action of `Gal(F̄/F)`. Its cohomology is a
diagram of Galois actions over scaled levels and stages. The limit over the
stages is the `ℓ`-power torsion limit of the cohomology with coefficients in
`W`, as a functor of the scaled level. After extension of scalars to `K_λ` it
is the `λ`-adic cohomology as a functor of the scaled level. The module also
adds a generic functor, extension of scalars of Galois actions.

The declarations are in namespace `Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`,
except `baseChangeActionFunctor` and its two lemmas, which are in
`Langlands.Shimura.LatticeGaloisRepresentation`.

## Motivation and scope

Harris (1999), *Galois properties of cohomological automorphic forms on
GL(n)*, §4, printed p. 311, puts `ℒ_m = ℒ ⊗_𝒪 𝒪_m` for a stable lattice `ℒ`
of the algebraic representation `W`. The inverse system of the corresponding
lisse sheaves `ℒ̃_m` defines the lisse `ℓ`-adic sheaf `W̃ = lim ℒ̃_m ⊗_𝒪 L_ℓ`
on the geometric fibre `S̄_K(N)`. Proposition 4.10 (printed p. 311) gives a
spectral sequence abutting to `H^{i+j}(S̄_K(N), W̃)` and states that, as
`K(N)^{ℓ,p}` varies, the spectral sequences are `GG(A_f^{ℓ,p})`-equivariant;
both `ℓ` and `p` are excluded there. Harris states no such equivariance for
the `ℓ`-component, and none is attributed to him here: the action of
transporters with nontrivial `ℓ`-component, through the scaled lattice maps
described below, is a construction internal to the Library.
Printed pp. 312-313 consider the `JL(π_f)`-isotypic component of
`H^{n-1}(S̄_K(N), W̃)` and the `λ`-adic representations of `Gal(F̄/F)` it
carries. Following Milne,
*Étale cohomology*, Chapter V, §1, printed pp. 163-165, the cohomology of an
`ℓ`-adic sheaf `F = (F_r)` is `H^d(X, F) = lim_r H^d(X, F_r)` (p. 164), and the
corresponding sheaf of vector spaces is `F ⊗ Q_ℓ` (p. 164), also over the
integers of a finite extension of `Q_ℓ` (p. 165).

The published `cmHarrisLambdaCohomology` builds this space at one fixed small
level `U`. For a transporter `g` from a level `V` to `U`, the image
`ρ(g) ℒ_U` of the lattice need not lie in `ℒ_V`; only `ℓ^e ρ(g) ℒ_U` does, for
some exponent `e`. The published
category `CMScaledLevel D ρ p` of scaled levels records this: an object is a
small level with an exponent, and a morphism `f : X ⟶ Y` is a transporter of
the levels for which the difference of exponents is admissible. The published
`cmHarrisScaledCoefficientDiagram` is the diagram of coefficient sheaves over
`(CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ`, whose transitions are the transport maps of
the scaled lattice maps. This module carries that diagram to geometric fibres
and takes cohomology, the torsion limit and the extension of scalars, so that
transporters act on the `λ`-adic cohomology.

The module stops there. It does not normalize by powers of `ℓ`, does not
construct a functor on small levels or an action of the finite adelic group,
and does not compare its values with the fixed-level
`cmHarrisGeometricGaloisCohomologyAction`, `cmHarrisEllAdicCohomology` or
`cmHarrisLambdaCohomology`. These comparisons are separate constructions. No
statement of Harris is formalized.

## Inputs

The binders `E`, `F`, `A`, `D`, `L`, `C`, the named premises `preservation`
through `htor`, `q`, `[Module.Finite ℚ A]`, `K`, `W`, `ρ`, `p`, `existence`,
`geometry` and `hRigid` are those of the published
`Langlands.Shimura.PEL.HarrisTaylorCMLevelTransport`. In particular
`hRigid : ∀ U : SmallCMLevel D, CMGeometricCoarseRigidity ... U.obj` is the
rigidity hypothesis at every small level. Below `...` abbreviates
`D C preservation ... htor q p ρ existence geometry hRigid`, with the trailing
arguments omitted for the declarations that do not take them. Throughout,
`Galois = AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`, which is
definitionally `Field.absoluteGaloisGroup F`. `R = HarrisCoefficientIntegers K p`
and `ℓ = harrisCoefficientPrime p`. For a scaled level `X`, `U` is its level
`X.level`.

The cohomology declarations take two further instance binders: for every small
level `U`, `HasDerivedCategory.{wS}` for the module sheaves over `R` on the
geometric level `(cmGeometricSchemeTower ... q).obj U`, and
`HasDerivedCategory.{wR} (ModuleCat.{0} R)`.

- From `Langlands.Shimura.PEL.HarrisTaylorCMLevelTransport`:
  `cmScaledSchemeDiagram`, `cmScaledSchemeDiagram_etale` and
  `cmHarrisScaledCoefficientDiagram`, as described above.
- From `Langlands.Shimura.PEL.HarrisTaylorCMScaledLevels`: `CMScaledLevel D ρ p`
  and `CMScaledLevel.Hom.hom`, the transporter of a morphism.
- From `Langlands.Shimura.PEL.HarrisTaylorCMGeometricCoefficients`:
  `cmSchemeTower`, `cmGeometricSchemeTower` and `cmGeometricProjection`, the
  CM schemes `X_U`, the geometric levels `X̄_U` and the projections
  `π_U : X̄_U ⟶ X_U`, as functors of the small level and a natural
  transformation.
- From `Langlands.Shimura.PEL.HarrisTaylorCMGeometricGalois` and
  `Langlands.Shimura.PEL.HarrisTaylorCMGeometricGaloisCoefficients`:
  `cmGeometricGaloisMap ... q σ`, the natural transformation whose component
  `g_σ : X̄_U ⟶ X̄_U` is the automorphism of `X̄_U` given by `σ` on the field
  factor, with `cmGeometricGaloisMap_app_one`, `cmGeometricGaloisMap_app_mul`
  (`g_σ ≫ g_τ = g_(σ * τ)`) and
  `cmGeometricGaloisMap_app_projection` (`g_σ ≫ π_U = π_U`).
- From `Langlands.Geometry.EtaleCoefficientEquivalence`:
  `CoefficientDiagram.ofRestriction`, which turns a coefficient diagram for
  etale restriction into one for inverse images.
- From `Langlands.Geometry.EtaleGeometricCoefficientReindex`:
  `CoefficientDiagram.reindex`.
- From `Langlands.Geometry.EtaleCoefficientDiagramPullback`:
  `CoefficientDiagram.pullback R π`, the inverse image of a coefficient diagram
  along a morphism `π` of contravariant scheme diagrams. Its transition is the
  square comparison of inverse images followed by the inverse image of the
  old transition.
- From `Langlands.Geometry.EtaleGeometricActionDiagram`:
  `CoefficientDiagram.cohomologyAction`, which for a coefficient diagram over
  `J × SingleObj G` gives the cohomology as a functor `J ⥤ Action (ModuleCat R) G`,
  and `CoefficientDiagram.cohomologyAction_obj_V`.
- From `Langlands.Shimura.LatticeGaloisRepresentation`: `baseChangeAction`.
- From `Langlands.Shimura.PEL.HarrisTaylorCMLambdaAdicRepresentation`:
  `harrisCoefficientComponentAlgebra K p l`, the algebra structure of
  `K_λ = FiniteCompletion K l.1` over `R` through the `λ`-component.

## Definitions

### Extension of scalars as a functor

- `LatticeGaloisRepresentation.baseChangeActionFunctor (L := L)`: for a field
  `K`, a commutative ring `O` and a field `L` with `[Algebra O L]`, the functor
  `Action (ModuleCat O) (Field.absoluteGaloisGroup K) ⥤
  Action (ModuleCat L) (Field.absoluteGaloisGroup K)`. It sends `V` to
  `baseChangeAction (L := L) V`, the Galois action on `L ⊗_O V`. It sends an
  equivariant map `f` to `L ⊗ f`. Equivariance, `map_id` and `map_comp` follow
  from `LinearMap.baseChange_comp` and `LinearMap.baseChange_id`.
- `baseChangeActionFunctor_obj` and `baseChangeActionFunctor_map_hom` state the
  values on objects and morphisms (`rfl`).

### Scheme diagrams

- `CMScaledGaloisIndex D p ρ` is the index category
  `((CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) × SingleObj Galois`: scaled levels, torsion
  stages and Galois elements.
- `cmScaledArithmeticGaloisSchemes ... q p ρ` is
  `Prod.fst ⋙ cmScaledSchemeDiagram ... q p ρ`: the CM scheme `X_U` at the
  vertex `((X, k), *)`, with the Galois factor ignored.
- `cmScaledGeometricGaloisSchemes ... q p ρ` sends `((X, k), *)` to the
  geometric level `X̄_U`. An arrow `(f, σ) : ((X, k), *) ⟶ ((Y, k'), *)`,
  where `f.unop : Y ⟶ X`, goes to the opposite of
  `g_σ ≫ T̄(f) : X̄_{U_Y} ⟶ X̄_{U_X}`. Here `g_σ` is the Galois map at the level
  of `Y` and `T̄(f)` is the geometric tower map of the transporter of
  `f.unop`. The identity law uses `cmGeometricGaloisMap_app_one`. The
  composition law uses `cmGeometricGaloisMap_app_mul` and the naturality of
  `cmGeometricGaloisMap` with respect to tower maps.
- `cmScaledGeometricGaloisProjection ... q p ρ` is the morphism of
  contravariant scheme diagrams from the arithmetic to the geometric diagram
  with components `π_U`. Naturality is the naturality of
  `cmGeometricProjection` together with `g_σ ≫ π_U = π_U`.
- Lemmas: `cmScaledGeometricGaloisSchemes_obj` and `_map`,
  `cmScaledArithmeticGaloisSchemes_obj` and `_map`, and
  `cmScaledGeometricGaloisProjection_app` state these values (`rfl`).

### Coefficient diagrams

- `cmHarrisScaledArithmeticGaloisCoefficientDiagram ... q p ρ existence geometry hRigid`
  is `CoefficientDiagram.ofRestriction` of `cmHarrisScaledCoefficientDiagram`,
  reindexed along `Prod.fst`. The etale instances for the transitions come from
  `cmScaledSchemeDiagram_etale`. Its vertex `((X, k), σ)` is the stage-`k`
  coefficient sheaf at the level of `X`. Arrows with the same scaled-level and
  stage component have the same transition, whatever their Galois component.
- `cmHarrisScaledGeometricGaloisCoefficientDiagram ...` is
  `CoefficientDiagram.pullback R (cmScaledGeometricGaloisProjection ...)` of the
  arithmetic diagram: the inverse image along the geometric projections. The
  transition of an arrow `(f, σ)` is the comparison of inverse images across
  the commuting square `π_{U_Y} ≫ T(f) = (g_σ ≫ T̄(f)) ≫ π_{U_X}`
  (`squareInverseImageMap`), followed by the inverse image along `π_{U_Y}` of
  the transition of the arithmetic diagram, the transport map of `f`. The
  module does not compare these transitions for `f = 𝟙` with the coefficient
  comparisons of the published fixed-level Galois action.
- `cmHarrisScaledGeometricGaloisCoefficientDiagram_obj` (`rfl`): the vertex
  `((X, k), σ)` is the inverse image along `π_U` of
  `(cmHarrisCoefficientSystem ... X.level ρ p ℓ hℓ existence geometry (hRigid _)).obj k`.

### Cohomology

- The instance `cmScaledGeometricGaloisSchemes_hasDerivedCategory` gives
  `HasDerivedCategory.{wS}` at each vertex of the geometric scheme diagram,
  from the instance binder at the level of the vertex.
- `cmHarrisScaledGaloisCohomologyAction ... degree :
  ((CMScaledLevel D ρ p)ᵒᵖ × ℕᵒᵖ) ⥤ Action (ModuleCat R) Galois` is
  `CoefficientDiagram.cohomologyAction degree` of the geometric coefficient
  diagram. At `(X, k)` the action of `σ` is the pullback, with the transition
  of the diagram as coefficient map, along the scheme map of `(𝟙, σ)`,
  `g_σ ≫ T̄(𝟙)`, which equals `g_σ` by the identity law of the tower. An arrow
  `(f, k' ≤ k)` gives the pullback along the scheme map of `(f, 1)`,
  `g_1 ≫ T̄(f)`, which equals `T̄(f)`, with the transition of the diagram.
- `cmHarrisScaledGaloisCohomologyAction_obj_V`: the module at `(X, k)` is
  `H^d(X̄_U, π_U^* W_k)`, the cohomology
  `(EtaleDerivedSections.cohomology (cmGeometricSchemeTower ... q).obj U R degree).obj`
  of the inverse image along `π_U` of the stage-`k` coefficient sheaf at `U`.
- `cmHarrisScaledAdicCohomology ... degree :
  (CMScaledLevel D ρ p)ᵒᵖ ⥤ Action (ModuleCat R) Galois` is
  `Functor.curry.obj (cmHarrisScaledGaloisCohomologyAction ... degree) ⋙ lim`:
  at a scaled level `X` it is the `ℓ`-power torsion limit
  `lim_k H^d(X̄_U, W_k)` in `Action (ModuleCat R) Galois`, and a morphism of
  scaled levels gives the induced map of limits.
  `cmHarrisScaledAdicCohomology_obj` states the value at `X` (`rfl`).
- `cmHarrisScaledLambdaCohomology ... l degree :
  (CMScaledLevel D ρ p)ᵒᵖ ⥤ Action (ModuleCat K_λ) (Field.absoluteGaloisGroup F)`
  is `cmHarrisScaledAdicCohomology ... degree ⋙ baseChangeActionFunctor (L := K_λ)`,
  with the algebra structure `harrisCoefficientComponentAlgebra K p l`. At `X`
  it is `K_λ ⊗_R lim_k H^d(X̄_U, W_k)` with the Galois action extended
  `K_λ`-linearly, and a morphism goes to `K_λ ⊗` the map of limits.

The value at a scaled level depends only on its level. The exponent enters
only the morphisms, through the transport maps of the scaled lattice maps
`x ↦ ℓ^e ρ(g) x`.

## Lean notes

The module sets `maxHeartbeats` to 800,000 for the whole file. It uses the
options `backward.isDefEq.respectTransparency false`,
`backward.isDefEq.respectTransparency.types false` and
`backward.defeqAttrib.useBackward true`, as the generic coefficient-diagram
modules do. It also sets `quotPrecheck false` for its local notations, and
`autoImplicit false`.

## Provenance

This module is a derived construction. It implements the cohomology of the
geometric fibre with coefficients in Harris's `ℓ`-adic sheaf `W̃`, with its
Galois action and its functoriality in the level, of Harris (1999), printed
pp. 311-313. It follows Milne, Chapter V, §1, printed pp. 163-165, for the
`ℓ`-adic cohomology as the limit of the torsion cohomology and for the
passage to vector spaces. The scaled levels, the coefficient diagram over
them, the geometric levels and the Galois maps are the Library's. The
packaging as one diagram over scaled levels, stages and Galois elements is
internal to the Library. `baseChangeActionFunctor` is a generic helper: the
functorial form of the published `baseChangeAction`.
