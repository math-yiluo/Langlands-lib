# Sheafified tensor extension on the small etale site

The namespace is `Langlands.Geometry.EtaleCohomologyAction`. This module
constructs tensor extension of coefficient sheaves on the actual small etale
site of a scheme, proves its adjunction to the existing scalar restriction
functor, and exposes the unit, counit and universal lifts.

## Provenance and inputs

This is an internal construction from the published `EtaleScalarRestriction`
and the pinned Mathlib categorical constructions. It does not transcribe an
external theorem. In `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean`,
`ModuleCat.extendScalars` tensors modules and morphisms, and
`ModuleCat.extendRestrictScalarsAdj` supplies the extension/restriction adjunction.
In `Mathlib/CategoryTheory/Sites/PreservesSheafification.lean`,
`Sheaf.composeAndSheafify` postcomposes the underlying presheaf and sheafifies.
`Mathlib/CategoryTheory/Sites/Adjunction.lean` lifts the module adjunction to
sheaves and identifies its unit and counit. These constructions are instantiated
here with the actual small etale topology; the adjunction and comparison maps
are constructed, not supplied as input fields.

The parameters are arbitrary commutative rings `R S : Type u`, a ring
homomorphism `φ : R →+* S`, and `X : Scheme.{u}`. Module carriers also lie in
`Type u`. The published abbreviation
`EtaleDerivedSections.ModuleSheaf X R` is
`Sheaf X.smallEtaleTopology (ModuleCat.{u} R)`. The needed sheafification and
sheaf-composition instances are inferred from the existing scheme/site/module
infrastructure; there is no additional sheafification hypothesis in the public
construction. No flatness, injectivity or surjectivity of `φ` is assumed.
The rings carry no added topology.

## Tensor extension and its adjunction

Write `T = sheafRestrictScalars φ X`. For an R-module sheaf F, let

\[
 P_F(U)=S\otimes_{R,\varphi}F(U).
\]

This is the presheaf `F.obj ⋙ ModuleCat.extendScalars φ`. The S-module structure
on the tensor product is the standard one on its first factor. Its restriction
maps and the maps induced by coefficient morphisms are obtained by tensoring
the corresponding R-linear maps with the identity of S.

`sheafExtendScalars φ X`, denoted L below, is the functor

\[
 F\longmapsto a(P_F),
\]

where a is sheafification on `X.smallEtaleTopology`. In particular, no assertion
is made that the tensor presheaf itself is always a sheaf, or that evaluating
L F is the same as the raw tensor product. The natural presheaf morphism
`tensorToSheafExtension φ X F`, denoted τ_F, is precisely `toSheafify` from P_F
to the underlying presheaf of L F.

`sheafExtendRestrictScalarsAdj` constructs `L ⊣ T` by applying
`Sheaf.adjunction` to the module tensor/restriction adjunction. It also supplies
an `IsLeftAdjoint` instance for L. Both triangle identities belong to this
constructed adjunction; they are not assumptions on F or on the ring map.

## Unit and counit formulas

`sheafExtensionUnit` is the natural morphism η from the identity functor to
`L ⋙ T`. `sheafExtensionUnit_hom` identifies its underlying presheaf morphism:
first apply the module unit sectionwise, then restrict the S-linear
sheafification map to R. Thus `sheafExtensionUnit_app_apply` proves, at each
`U : X.Etaleᵒᵖ` and `m : F.obj.obj U`,

\[
 \eta_{F,U}(m)=\tau_{F,U}(1\otimes m).
\]

`sheafExtensionCounit` is the natural morphism ε from `T ⋙ L` to the identity
functor on S-module sheaves. `sheafExtensionCounit_hom` identifies its underlying
presheaf map as `sheafifyLift` of the sectionwise module counit
`S ⊗_R E(U) → E(U)`, which sends `s ⊗ e` to `s • e` (the R-action on E(U) here
is restricted along φ). The natural-transformation equation
`tensorToSheafExtension_counit` proves

\[
 \tau_{T E}\,;\,\varepsilon_E
   =\text{the sectionwise module counit}.
\]

Here a semicolon means first the map on the left, then the map on the right.
`sheafExtensionCounit_app_one_tmul` in particular proves

\[
 \varepsilon_{E,U}(\tau_{T E,U}(1\otimes e))=e.
\]

The two presheaf descriptions specialize Mathlib's sheaf-adjunction formulas.
The unit's element formula follows by evaluating the presheaf formula.
The counit equation uses `toSheafify_sheafifyLift`; its element formula evaluates
that equation and applies the module counit formula on `1 ⊗ e`.

## Universal morphisms

`sheafExtensionHomEquiv φ X F E` is the bijection

\[
 \operatorname{Hom}_S(LF,E)\simeq\operatorname{Hom}_R(F,TE).
\]

`sheafExtensionHomEquiv_apply` identifies its forward direction as
`g ↦ η_F ≫ T.map g`. `sheafExtensionLift φ X f` is the inverse image of a given
`f : F ⟶ T.obj E`. Its defining equation is proved by
`sheafExtensionUnit_lift`:

\[
 \eta_F\,;\,T(\operatorname{lift}(f))=f.
\]

`sheafExtensionLift_unique` proves that every `g : L.obj F ⟶ E` satisfying this
same equation equals the constructed lift. The factorization uses the inverse
law of the hom-set equivalence, and uniqueness uses its injectivity; the unit
equation is not assumed for the constructed lift.

For `a : F' ⟶ F` and `b : E ⟶ E'`, the two naturality lemmas are

\[
 \operatorname{lift}(a\,;\,f)=L(a)\,;\,\operatorname{lift}(f),
 \qquad
 \operatorname{lift}(f\,;\,T(b))=\operatorname{lift}(f)\,;\,b.
\]

They are `sheafExtensionLift_precomp` and `sheafExtensionLift_postcomp`,
obtained from naturality of the inverse adjunction hom-set equivalence.

## Scope

This unit constructs ordinary sheaf tensor extension on a fixed scheme and its
universal coefficient maps. Geometric equivariance, compatibility with change
of scheme or coefficient-ring composition, varying-scheme coefficient diagrams,
ideal-reduction identifications, inverse systems, derived scalar comparisons,
compact supports, smoothness and the Harris specialization remain separate
obligations. In particular, the adjunction alone is not an assertion of exactness
of tensor extension, preservation of injectives by scalar restriction, or
commutation of tensor extension with global sections or higher cohomology.
