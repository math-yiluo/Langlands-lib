# Proof: the locus where a morphism contracts the fibres of an abelian scheme is open

Authors: Worker 1028 and Worker 139. Worker 1028 supplied the proof draft;
Worker 139 checked the implementation, source passage and scope, and prepared
the focused exact-target submission.

`Langlands.AbelianScheme.fibreContractionOpen` proves exactly the published
proposition `Langlands.AbelianScheme.FibreContractionOpenStatement.{u}`. It
applies to arbitrary schemes `Y` and `Z` in universe `u`, every abelian scheme
`B` over `Y`, every morphism `Ψ : B.X.left ⟶ Z` and every point `z₀ : Z` such
that `Ψ` sends the unit section to `z₀` at every point of `Y`. The conclusion
is that the set

```text
{y : Y | ∀ x, B.X.hom x = y → Ψ x = z₀}
```

is open. The theorem keeps the arbitrary universe and every quantifier of the
statement and adds no hypothesis.

## Derived provenance

The source is the Rigidity Lemma (1.12) of Edixhoven, van der Geer and Moonen,
*Abelian Varieties* (preliminary draft), printed pp.12–13, PDF pp.16–17,
registered as `edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The retained file is
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
No source-specific errata note was present in the checked workspace, current
Library or project `notes/errata/` locations.

The source treats varieties over a field and a product with a complete
variety. Its proof uses an affine neighbourhood and the closed image of its
inverse-image complement to obtain fibrewise constancy on an open set, then
continues to a stronger global factorization conclusion. This module gives a
derived scheme-theoretic version of the openness step. Properness supplies
the closed image over an arbitrary base, and scalar global functions on the
smooth proper geometrically connected residue-field fibres supply constancy
inside an affine target. The unit section determines the common value. The
implemented argument below proves the target without the later global
factorization step in the source.

## Auxiliary declarations

All declarations are in namespace `Langlands.AbelianScheme`.

### `exists_factor_of_isIso_appTop`

Let `F` and `W` be schemes and `K` a commutative ring. Let
`π : F ⟶ Spec K` be a morphism whose map on global sections `π.appTop` is an
isomorphism, and let `W` be affine. Then every morphism `h : F ⟶ W` factors as
`h = π ≫ g` for some `g : Spec K ⟶ W`.

Proof: naturality of `toSpecΓ` (`Scheme.toSpecΓ_naturality`) together with
`W.isoSpec.hom = W.toSpecΓ` gives
`h = F.toSpecΓ ≫ Spec.map h.appTop ≫ W.isoSpec.inv`. Naturality for `π` gives
`F.toSpecΓ = π ≫ (Spec K).toSpecΓ ≫ inv (Spec.map π.appTop)`. Substituting the
second identity into the first gives the factorization with
`g = (Spec K).toSpecΓ ≫ inv (Spec.map π.appTop) ≫ Spec.map h.appTop ≫
W.isoSpec.inv`.

### `apply_eq_of_fibre_subset_affine`

Let `B : AbelianScheme Y`, let `Ψ : B.X.left ⟶ Z` be any morphism and let
`y : Y`. Let `V` be an affine open subset of `Z` that contains `Ψ x` for every
point `x` of `B` over `y`. Then every point `x` of `B` over `y` satisfies
`Ψ x = Ψ (unitSection B y)`.

Proof: let `s = Y.fromSpecResidueField y`, and let `π` be the second
projection of the fibre `F = B ×_Y Spec κ(y)`. Since `π` is a base change of
the structure morphism of `B`, it is smooth, proper and geometrically
connected. The published theorem
`Langlands.AlgebraicGeometry.fieldSmoothProperConnectedGlobalFunctions`
therefore shows that `π.appTop` is an isomorphism. Every point of `F` lies over
`y`, so the composite `Ψ_s = pullback.fst ≫ Ψ : F ⟶ Z` takes values in `V`.
It therefore lifts through the open immersion `V.ι` (`IsOpenImmersion.lift`).
Since `V` is affine, the previous lemma factors this lift through `π`, so
`Ψ_s = π ≫ g ≫ V.ι`. Because `Spec κ(y)` has only one point, `Ψ_s` takes the
same value at all points of `F`. The point `x` is the image of a point of `F`
(`Scheme.Pullback.exists_preimage_pullback`). The point `unitSection B y` is
the image of `pullback.lift (s ≫ unitSection B) (𝟙 _)` applied to the closed
point. Hence `Ψ` takes the same value at both points.

### `isOpen_setOf_fibre_eq`

This is the theorem itself, stated with explicit arguments: if
`Ψ (unitSection B y) = z₀` for every `y : Y`, then the set above is open.

Proof: let `y₀` lie in the set. Choose an affine open `V ∋ z₀`, which exists
by `Z.isBasis_affineOpens`. The complement `F` of `Ψ⁻¹ V` is closed. Its image
under the structure morphism `B.X.hom` is closed, because this morphism is
proper (`Scheme.Hom.isClosedMap`). The point `y₀` is not in that image,
because the whole fibre over `y₀` maps to `z₀ ∈ V`. If `y` is outside the
image, then the whole fibre over `y` maps into `V`. The previous lemma and the
hypothesis on the unit section then give `Ψ x = z₀` for all `x` over `y`.
Hence the complement of the image is an open neighbourhood of `y₀` contained
in the set.

### `fibreContractionOpen`

The target theorem, obtained by applying `isOpen_setOf_fibre_eq`.

## Scope

There are no additional Noetherian, separatedness, reducedness, finiteness,
connectedness, flatness, field-base, rational-point or affineness hypotheses on
`Y`, `Z` or `Ψ`. The structure morphism of `B` has the smoothness, properness
and geometric connectedness already supplied by `AbelianScheme`; these enter
through `fieldSmoothProperConnectedGlobalFunctions` and through closedness of
the structure morphism. The proof also uses the actual unit section and its
section identity `unitSection_comp`. The morphism `Ψ` has no required base
compatibility or group-law compatibility. All quantified points are underlying
topological points, and the hypothesis on the unit section is pointwise. The
conclusion is openness of exactly the displayed set.

The proof imports only the target statement and the published global-functions
proof, with their existing dependencies. It uses none of the Picard-zero
component-constancy, component-comparison or open-locus statements, and assumes
no `IsPicardZeroOpenLocus`. It does not change the paused smooth-family,
ordinary, ambient or existence workflows.
