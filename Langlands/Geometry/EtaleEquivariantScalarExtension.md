# Equivariant sheafified scalar extension

The module `Langlands.Geometry.EtaleEquivariantScalarExtension` constructs
extension of coefficient scalars on the existing category of geometrically
equivariant small-etale module sheaves. It constructs the adjunction to
`scalarRestrictionFunctor`, including the equivariant unit and counit and a
universal lifting interface. All declarations lie in
`Langlands.Geometry.EtaleCohomologyAction`.

## Parameters and provenance

Let `R` and `S` be arbitrary commutative rings in `Type u`, let
`φ : R →+* S`, and let `X : Scheme.{u}`. Module carriers also lie in universe
`u`. Let `G : Type w` be a group and let `ρ : G →* (Aut X)ᵐᵒᵖ` be the
existing geometric action datum. No topology on `G` or on the coefficient
rings is required. The scheme and coefficient universes are the shared
universe used by the ordinary sheafified extension construction.

This is an internal categorical construction from the published
`EtaleScalarExtension`, `EtaleScalarExtensionPullback`,
`EtaleScalarRestriction`, and translation-equivariant category modules.
It is not a transcription of a theorem from Harris or Berkovich. Its role
in the larger framework is to supply actual change-of-coefficients functors
for sheaves carrying a moving-space action. The action laws, unit and counit
equivariance, and triangle identities are proved from those constructions;
none is an additional input hypothesis.

Write `L` for `sheafExtendScalars φ X`, `Q` for
`sheafRestrictScalars φ X`, and `T_g^R`, `T_g^S` for the corresponding
`translateBy` functors. Translation is restriction along the etale
isomorphism `(aut ρ g).hom`. Write `β_g(F) : T_g^S(L F) ⟶ L(T_g^R F)`
for the forward component of `sheafExtendScalarsPullbackIso`, and write
`τ_F` for `tensorToSheafExtension φ X F`. The underlying object `L F`
is the sheafification of the presheaf with section module
`S ⊗[R,φ] F(U)`; it is not assumed to equal that presheaf.

## Construction of the action

An object `F : EquivariantSheaf R ρ` has structure maps
`a_g : T_g^R F.obj ⟶ F.obj`. `scalarExtensionAct` defines the new map by

`a'_g = β_g(F.obj) ≫ L.map a_g`.

Thus the extended action is constructed using the actual geometric
pullback comparison. `tensorToSheafExtension_act` states that, before
sheafification, it is exactly the tensor extension of `a_g`:

`T_g(τ_F) ≫ a'_g.hom = (a_g.hom whiskered by extendScalars φ) ≫ τ_F`.

Here and in the next equations, translation on presheaves means
precomposition by the opposite small-etale site functor. The proof combines
the tensor equation for `β_g` with naturality of `τ` in the coefficient
sheaf.

The auxiliary lemmas `tensorToSheafExtension_oneIso` and
`tensorToSheafExtension_compIso_inv` establish compatibility of `τ` with
the translation unit and inverse composition constraints. If `e_R`, `e_S`
are the unit components, the first equation is

`T_1(τ_F) ≫ e_S(L F).hom = (e_R(F).hom whiskered by extendScalars φ) ≫ τ_F`.

If `c_R`, `c_S` are the composition constraints, the second equation is

`T_(g*h)(τ_F) ≫ c_S(g,h).inv(L F).hom =`
`(c_R(g,h).inv(F).hom whiskered by extendScalars φ) ≫ T_g(T_h(τ_F))`.

Both proofs unfold the existing geometric constraints componentwise and
apply presheaf naturality of `τ` to the associated site isomorphism. These
are naturality equations for actual maps of presheaves.

`scalarExtensionAct_one` proves `a'_1 = e_S(L F)`.
`scalarExtensionAct_mul` proves the existing cocycle convention

`a'_(g*h) = c_S(g,h).inv(L F) ≫ T_g^S.map a'_h ≫ a'_g`.

For each proof, `sheafExtensionPullback_hom_ext` reduces equality of maps
out of the translated extension to equality after its tensor map. The
unit proof then uses `F.act_one` and the unit-constraint equation above.
The multiplication proof uses the inverse composition-constraint equation,
expands the two action maps through their tensor equations, and applies
`F.act_mul`. No surjectivity of tensor-to-sheafification on sections is
assumed in this extensionality argument.

`scalarExtensionObj` packages the resulting equivariant sheaf.
`scalarExtensionAct_naturality` proves that `L.map a.hom` is equivariant
for every equivariant morphism `a`. Its proof uses `a.comm` and naturality
of `β_g`. `scalarExtensionFunctor` then defines

`EquivariantSheaf R ρ ⥤ EquivariantSheaf S ρ`.

Its identity and composition equations follow from those of `L`, using
extensionality of equivariant morphisms. `scalarExtensionForgetIso` is the
identity natural isomorphism comparing extension followed by forgetting
equivariance with forgetting equivariance followed by `L`.

## The adjunction

`scalarExtensionUnit_comm` proves that the ordinary unit
`η_F : F ⟶ Q(L F)` is equivariant. Expanding `a'_g` on the right reduces
the equation to compatibility of `η` with geometric pullback, followed by
naturality of `η` at `a_g`. The underlying map sends a section `m` to the
sheafification image of `1 ⊗ m`, as specified by the imported ordinary
unit formula.

`scalarExtensionCounit_comm` proves that the ordinary counit
`ε_E : L(Q E) ⟶ E` is equivariant. Tensor extensionality reduces its
equivariance square to the tensor equation for the action and the
published equation `tensorToSheafExtension_counit`. On each small-etale
object, the remaining equation is naturality of
`ModuleCat.extendRestrictScalarsAdj φ`'s counit at the component of
`E.act g`. This is the sectionwise tensor-evaluation map before
sheafification.

`scalarExtensionUnit` and `scalarExtensionCounit` package these maps as
natural transformations of equivariant sheaves. Their naturality follows
from that of the ordinary unit and counit. `scalarExtensionRestrictionAdj`
constructs the adjunction

`scalarExtensionFunctor φ ρ ⊣ scalarRestrictionFunctor φ ρ`.

Each triangle identity follows from the corresponding triangle identity
of `sheafExtendRestrictScalarsAdj φ X` after applying extensionality of
equivariant morphisms. The module supplies the resulting `IsLeftAdjoint`
instance for `scalarExtensionFunctor φ ρ`.

## Universal property

`scalarExtensionHomEquiv` is the adjunction's equivalence between
morphisms `L^G F ⟶ E` of equivariant `S`-sheaves and morphisms
`F ⟶ Q^G E` of equivariant `R`-sheaves. The lemmas
`scalarExtensionHomEquiv_hom` and `scalarExtensionHomEquiv_symm_hom`
identify its forward and inverse underlying sheaf maps with the published
ordinary `sheafExtensionHomEquiv` and `sheafExtensionLift`. These
identifications are definitional consequences of the chosen unit and counit.

`scalarExtensionLift` names the inverse correspondence.
`scalarExtensionUnit_lift` proves its factorization through the unit, and
`scalarExtensionLift_unique` proves uniqueness among equivariant maps
satisfying that equation. Both reduce to the ordinary universal property
on underlying sheaves. `scalarExtensionLift_precomp` and
`scalarExtensionLift_postcomp` give naturality in the source and target,
respectively, directly from the adjunction's hom-equivalence naturality.

## Scope

The constructed categories use the existing translation-equivariance
convention for an abstract group acting on a scheme. This module does not
assert smoothness or continuity of actions. It does not establish
exactness, preservation of injectives, commutation with global sections or
higher cohomology, compact-support comparisons, or any Harris-specific
cohomological theorem. Equivariant geometric pullback comparisons,
coherence for identity and composite coefficient homomorphisms,
coefficient diagrams, ideal reduction, and inverse systems remain
separate constructions. This unit is one prerequisite for the broader
Harris framework, not a completion of that framework.
