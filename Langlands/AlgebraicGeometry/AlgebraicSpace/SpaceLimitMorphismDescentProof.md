# Morphisms of algebraic spaces along cofiltered limits of affine schemes: proof

Author: Worker 208 (draft); revalidated against the current Library and
submitted by Worker 182.

The theorem `spaceLimitMorphismDescent` proves exactly
`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitMorphismDescent` from
`SpaceLimitMorphismDescentStatement`. It keeps the statement's arbitrary
universe and hypotheses:

- a cofiltered diagram `D` of affine schemes over an affine base `S`, with a
  limit cone `c`;
- a separated source space `X` with a quasi-compact atlas;
- a target space `Z` with a locally finitely presented atlas.

This is a proof-only module: it changes neither the statement nor anything the
statement imports.

The source is Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(31 December 2011), printed p.5 (Theorem 3.4(1)) and printed p.13, registered
as `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`. Conrad
says the space case follows from the scheme case by étale descent. The proof
below is such an argument. It describes a morphism out of `X` by its value on
an affine atlas. It descends that value with the Library's comparison for
sections over cofiltered limits of affine schemes, from
`SpaceFilteredRingPointProof`. It then glues along the atlas with the fppf
sheaf property.

## Helper results (namespace `SpaceLimitMorphisms`)

- `exists_hom_of_atlas`. Let `α : h_V ⟶ Y` be an étale surjective atlas of a
  space `Y`, and `q` a section of a space `Q` over `V`. If the two pullbacks of
  `q` agree on every pair of atlas points with the same image, there is a
  morphism `Y ⟶ Q` sending each atlas point `w` to the pullback of `q` along
  `w`. The proof follows the Library's `exists_desc_of_fppf_cover`. The atlas is
  étale-locally surjective (`isLocallySurjective_etale_of_isEtale_isSurjective`),
  hence fppf-locally surjective, hence an epimorphism of fppf sheaves. Fppf
  sheaves form a regular category, so it is an effective epimorphism, and
  `EffectiveEpi.desc` gives the morphism.
- `exists_affine_qc_atlas`: over a quasi-compact base, a space with a
  quasi-compact atlas has an affine atlas. The atlas scheme `U` is
  quasi-compact, so `exists_affine_refinement` (applied to the identity of `U`)
  gives an étale surjective map `j : W ⟶ U` from an affine scheme `W`. The new
  atlas is `j` composed with the old one; it is étale and surjective by
  `IsEtale.comp` and `IsSurjective.comp`.
- `exists_equalizer_scheme`. Take an affine atlas `U` of a separated space over
  an affine base. Apply `exists_representsEqualizer_of_relative_diag` to the two
  atlas sections over `U ×_S U`. This gives a closed immersion `E ⟶ U ×_S U`,
  so `E` is affine. Through its two projections `r₁, r₂ : E ⟶ U`, a pair of
  atlas points has the same image exactly when it factors through `E`.
- `exists_model_of_affine_diagram`. A finitely presented, quasi-compact,
  quasi-separated scheme over the limit of a cofiltered diagram of affine
  schemes has such a model at some stage. It passes to global sections
  (`nonempty_isColimit_Γ_mapCocone`), applies the Library's
  `schemeFilteredModelExistence` to the filtered ring diagram, and moves the
  pullback square back along `Scheme.isoSpec`.
- `baseAtlas g a` is the base change of an atlas along `g : B ⟶ S`, on the
  scheme `B ×_S U` with its first projection to `B`. It is `restrictAtlas`
  composed with `pullbackSymmetry`. `baseAtlas_app` says that an atlas point
  `w` goes to the atlas section of `w ≫ pr₂` over `S`. The base change is étale
  and surjective (`isEtale_baseAtlas`, `isSurjective_baseAtlas`).

## The main proof

Choose an affine atlas `a` of `X` with its affine equalizer scheme `E`, and a
locally finitely presented atlas `aZ` of `Z`.

1. **The value of `φ` on the atlas.** Base change the atlas along the diagram:
   `TargetLimit.diagram D t U.hom` has stages `D_i ×_S U` over `S` through the
   first projection, and limit `c.pt ×_S U`. Let `x₀` be the universal
   base-changed atlas point over `c.pt ×_S U`, and `z = φ(x₀)`. All stages and
   the limit are affine. Applied to this diagram,
   `exists_model_of_affine_diagram` gives every finitely presented affine
   scheme over the limit a finitely presented model at some stage, which is the
   hypothesis of the Library's `exists_stage`. That result applies:
   `z` is the pullback of a section `y₀` of `Z` over some stage `D_{j₀} ×_S U`.
2. **Compatibility.** The projections of `E` induce maps
   `D_i ×_S E ⟶ D_i ×_S U`. Over the limit, the two pullbacks of `y₀` are the
   values of `φ` on the two pullbacks of `x₀` to `c.pt ×_S E`. These are the
   atlas sections of the two composites `E ⟶ U`, which agree by the equalizer
   property. The Library's `exists_eq_of_limit`, on the stages over `j₀` of the
   diagram `D_i ×_S E`, makes the two pullbacks agree at a later stage `j`.
   Pulling `y₀` back to `y` over `D_j ×_S U` keeps them equal there.
3. **Gluing.** Two atlas points of the base change of `X` to `D_j` with the
   same image factor through `E`. The pair then factors through `D_j ×_S E`,
   so the pullbacks of `y` along them agree by step 2. `exists_hom_of_atlas`
   now gives `φj` from the base change of `X` to the base change of `Z` along
   `t.app j`. It sends each base-changed atlas point `w` to the pullback of
   `y` along `w`.
4. **Agreement over the limit.** Let `W` be over `c.pt` and `x` a section.
   `exists_atlas_lift`, for the base-changed atlas, gives an étale surjective
   `e : W' ⟶ W` on which `x` is an atlas point `v`. Both sides of the required
   equation are natural in `W`, so after pullback along `e` they become:
   - on the left, the pullback of `z` along `v`;
   - on the right, `φj` applied to the stage-`j` atlas point through `v`, i.e.
     the pullback of `y` to the limit and then along `v`, which is again the
     pullback of `z` along `v`.
   The identity morphisms between the two descriptions of `W` over `S` are
   handled by over-category extensionality. Pullback along `e` is injective
   (`pullback_injective`), which gives the equation.

## Scope

This proves only existence of a descended morphism. It does not prove
uniqueness or eventual equality of descended morphisms, descent of spaces or
of their properties, or any arithmetic specialization.
