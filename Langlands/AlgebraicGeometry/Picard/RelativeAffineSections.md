# Sections of relative spaces over affine bases

Module `Langlands.AlgebraicGeometry.Picard.RelativeAffineSections`, namespace
`Langlands.AlgebraicGeometry.Picard.RelativeAffineSections`. Author: Worker 967
(task `14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual
Picard families). Everything is proved in the file, with no hypotheses beyond
those in the signatures.

## Notation

`R : Type u` is a commutative ring and `f : X ⟶ Spec R` a morphism of schemes.
For an `R`-algebra `S`:

- `relSpace f S` is the Library's relative space
  `(relativeSpace f).obj (affineBase R S)`, i.e. `Spec S ×_R X`;
- `relProj f S : relSpace f S ⟶ Spec S` is the Library's `relativeProjection`;
- for an `R`-algebra map `s : S →ₐ[R] S'`, `relMap f s : relSpace f S' ⟶ relSpace f S`
  is the relative-space map of the Library's `affineBaseMap s`;
- `structureHom f S V : CommRingCat.of S ⟶ Γ(relSpace f S, V)` is
  `(Scheme.ΓSpecIso _).inv ≫ (relProj f S).appLE ⊤ V le_top`. This is the same
  formula as the ported FLT `Scheme.TwoAffineOpenCover.algebraOfHom (relProj f S) V`.

## Declarations

- `relMap_comp`: `relMap f (t.comp s) = relMap f t ≫ relMap f s`, from the
  Library's `affineBaseMap_comp`.
- `isPullback_relMap`: the square `relMap f s`, `relProj f S'`, `relProj f S`,
  `Spec.map s` is Cartesian (the Library's `relativeProjection_isPullback`).
- `isPushout_sections f s V hV`: for an affine open `V` of `relSpace f S`, the square
  of rings formed by `structureHom f S V`, `s`, `(relMap f s).appLE V (relMap f s ⁻¹ᵁ V) le_rfl`
  and `structureHom f S' (relMap f s ⁻¹ᵁ V)` is a pushout in `CommRingCat`. Proof:
  Mathlib's `isIso_pushoutSection_of_isAffineOpen` and `isIso_pushoutSection_iff`
  for the Cartesian square and the affine opens `⊤`, `⊤`, `V`. The global sections
  of the spectra are then identified with the rings via `Scheme.ΓSpecIso` and its
  naturality.
- `algebraIsPushout_sections`: the same statement as Mathlib's
  `Algebra.IsPushout S A Γ(relSpace f S, V) Γ(relSpace f A, relMap f s ⁻¹ᵁ V)`, for any
  algebra instances whose algebra maps are the four maps above (hypotheses
  `h₁`–`h₄`). Proof: `CommRingCat.isPushout_iff_isPushout` and
  `Algebra.IsPushout.symm`.
- `flat_structureHom`: if `f` is flat and `V` is affine, `structureHom f S V` is flat.
  `relProj f S` is a base change of `f`, hence flat
  (`MorphismProperty.of_isPullback`). Then `HasRingHomProperty.appLE` gives a
  flat `appLE`, composed with the isomorphism `ΓSpecIso`.
- `ker_appLE_eq_map`: for a surjective `q : A →ₐ[R] B` and an affine open `V` of
  `relSpace f A`, the kernel of `(relMap f q).appLE V (relMap f q ⁻¹ᵁ V) le_rfl` is
  `Ideal.map (structureHom f A V) (RingHom.ker q)`. Proof: the pushout above for
  `q` and `ker_algebraMap_eq_map` of `Langlands.Algebra.PushoutIdealTensor`.
- `preimage_relMap_eq`: let `s s' : S →ₐ[R] A` and `t : A →ₐ[R] A'` satisfy
  `t.comp s = t.comp s'`, and let `relMap f t` be surjective on points. Then
  `relMap f s ⁻¹ᵁ V = relMap f s' ⁻¹ᵁ V` for every open `V`. This applies to two
  lifts that agree modulo a nilpotent ideal of a local Artinian ring.

## Provenance

Internal infrastructure derived from Mathlib's base change of affine sections and
the Library's relative spaces. No literature statement is formalized.
