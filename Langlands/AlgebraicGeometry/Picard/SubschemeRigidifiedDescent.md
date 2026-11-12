# Separation and descent of line bundles rigidified along a morphism

Module `Langlands.AlgebraicGeometry.Picard.SubschemeRigidifiedDescent`, namespace
`Langlands.AlgebraicGeometry.Picard.SubschemeRigidification`.

This internal module continues `SubschemeRigidifiedClasses`, with the same data
`f : X ⟶ S`, `g : Z ⟶ S`, `z : Z ⟶ X`, `hz : z ≫ f = g`. Most results assume the hypothesis

```
unique : ∀ (T : Over S) (L M : relative f g z hz T), Subsingleton (L ≅ M)
```

that rigidified isomorphisms are unique; `iso_subsingleton` in the previous module supplies it
when `z` is injective on global functions after every base change. All test schemes in the
full slice `Over S` are allowed.

## Comparisons

`relativePullbackCompTo` compares iterated relative pullback with pullback along an equal
composite, and `relativePullbackCompTo_hom_val` identifies its underlying module map with the
published equal-composite comparison `compHom`.

## Zariski separation

The following adapt the Library's proofs for section rigidification
(`RigidifiedClassesZariskiSeparatedGeneral`) to rigidification along `zRel`.

- `rigidified_common_map`: by uniqueness, two local rigidified isomorphisms agree after
  pullback to a common test.
- `rigidified_overlap_compatible`: hence their underlying module maps agree on the actual
  overlap, via the published `square_compatible_of_common_map`.
- `rigidified_iso_of_local_isos`: rigidified isomorphisms on the members of an open cover of
  `T` glue. The underlying module maps glue by the published open-cover gluing
  (`openCoverIsoGluing_of_homGluing`). The glued map respects the rigidifications: this is
  checked on the induced open cover of `T ×_S Z` (`relativeOpenCover g T 𝒰`, published
  `hom_ext_of_openCover`) with the published
  `RigidifiedModule.rigidification_compatibility_of_pullback`.
- `classes_zariskiSeparated`: classes that agree on an open cover are equal.
- `isSeparated_zariski_over_of_openCover` converts separation on open covers into separation
  for the big Zariski slice topology; `classPresheaf_isSeparated_zariski` is the result.

## Separation along faithfully flat maps

- `relative_iso_descent_compatible`: a rigidified isomorphism after pullback along
  `h : U ⟶ T` satisfies the equal-composite descent condition of the published
  `LineBundleIsoDescentStatement` (via `equalComposite_compatible_of_pullback`).
- `iso_eq_of_pullback_map_eq`: two isomorphisms of locally free rank-one modules which agree
  after pullback along a quasi-compact flat surjection are equal, by the uniqueness part of the
  published `lineBundleIsoDescent`.
- `classes_flatSeparated`: if `h.left` is quasi-compact, flat and surjective and two classes
  agree after pullback along `h`, they are equal. The rigidified isomorphism on `U` descends to
  an isomorphism `ψ` of the underlying line bundles (published `lineBundleIsoDescent`). That
  `ψ` respects the rigidifications is an equality of isomorphisms of line bundles on
  `T ×_S Z`; it holds after pullback along the quasi-compact flat surjection
  `(relativeSpace g).map h` by `rigidification_compatibility_of_pullback`, hence holds by
  `iso_eq_of_pullback_map_eq`.

## Descent to ordinary classes

The namespace `ClassDescent` adapts the Library's descent comparisons
(`RigidifiedClassDescentData`, `RigidifiedClassDescentEffective`) to rigidification along
`zRel`. For `h : U ⟶ T` and a rigidified `L` on `U` whose pullbacks along any two maps with
equal composite to `T` are isomorphic, `compatibleIso` chooses those isomorphisms; uniqueness
gives the cocycle law (`compatibleIso_comp`) and compatibility with pullback
(`compatibleIso_precomp`). Through the published point sections and lifts
(`relativePointSection`, `pointLift`), `thetaCommon` and `theta` turn them into descent
isomorphisms for arbitrary scheme maps into `T ×_S X`, with cocycle law (`theta_comp`) and
naturality (`theta_precomp`). `exists_carrier` then applies the published effective descent
`LineBundleDescentEffectiveStatement` when `h.left` is affine, flat and surjective, giving a
line bundle `M` on `T ×_S X` with an isomorphism from its pullback to the carrier of `L`.

`exists_descended_class` states the consequence used later: for `m : U ⟶ V` with affine, flat
and surjective scheme map, and a class `p` over `U` whose pullbacks along any two maps with
equal composite agree, there is an ordinary class `y` over `V` whose pullback along `m` is the
ordinary class of `p`. Only the ordinary class is descended, not a rigidification.

## Provenance

Internal adaptation of the Library's section-rigidification proofs; it uses only published
Library results (line-bundle iso descent and effective descent, open-cover gluing, point lifts)
and Mathlib.
