# Affine sections of the actual structure-sheaf direct image over a field

For any field `k : Type u`, let `f : X → Spec k` be proper and let
`Y → X`, `p : Y → T`, `t : T → Spec k` be an actual Cartesian square.
The scheme `T` is arbitrary. For every affine open `U` of `T`,
`FieldGlobalFunctions.directImageAffineSectionsIso` constructs the canonical
`Γ(T,U)`-module isomorphism

`Γ(T,U) ⊗_k Γ(X,O_X) ≅ Γ(U,p_* O_Y)`.

The scalar action on `Γ(X,O_X)` is supplied by the actual structure map `f`.
The field map to `Γ(T,U)` is `Spec.preimage (hU.fromSpec ≫ t)`, so its
spectrum map is precisely the composite from this affine open to `Spec k`.
The target `directImageSections p U` evaluates the actual structure-module
pushforward `(Scheme.Modules.pushforward p).obj (SheafOfModules.unit _)` on
`U`. In particular its scalars act by the actual ring map `p.app U`.
There is no hypothesis that `Γ(X,O_X)` equals `k`.

The preliminary construction `affineRestrictSectionsIso` works for every
scheme morphism `p`, without a field or properness hypothesis. It identifies
relative global sections of the structure module on the actual inverse-image
open `p⁻¹ U` with direct-image sections on `U`. Its underlying additive
isomorphism is `(p ⁻¹ᵁ U).topIso`. To prove linearity, the implemented proof
uses naturality of `Scheme.Opens.toSpecΓ` and its map on top sections to show

`structureRingHom (affineRestrict p hU) = p.app U ≫ (p ⁻¹ᵁ U).topIso.inv`.

The field comparison pastes the actual open-restriction pullback square from
`DerivedSections.isPullback_affineRestrict` with the given square. It applies
the published `FieldGlobalFunctions.baseChangeIso` to that affine base change,
then composes with `affineRestrictSectionsIso`. The lemma
`directImageAffineSectionsIso_hom` records exactly this composition, so the
isomorphism is built from the canonical scalar-sections base-change map.

The actual module `FieldGlobalFunctions.sections f` is finite over `k` by
`FieldGlobalFunctions.finite`. Mathlib's `Module.Finite.base_change` shows
that its scalar extension is finite over `Γ(T,U)`. Transport along the
constructed isomorphism proves `finite_directImageAffineSections`.
Quantifying over all affine opens gives `hasFiniteAffineSections_directImage`
in the existing `HasFiniteAffineSections` interface. The latter assertion
places no Noetherian or quasi-compactness hypothesis on `T`.

These constructions are internal consequences of the published canonical
field base-change and global-functions finiteness results, together with
Mathlib's actual open restriction, pushforward and tensor-product finiteness
APIs. The universe `u` is arbitrary. This file constructs affine-open module
comparisons and proves finite affine sections; it does not yet assemble them
into a global sheaf isomorphism or establish Picard representability.
