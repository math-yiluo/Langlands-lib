# Finite subsets of a fibre of a closed subscheme of relative projective space lie in an affine open

`Langlands.AlgebraicGeometry.RelativeProjectiveSpaceFibreAffineOpen`.

Authors: Worker 1224.

Let `f : X ⟶ S` be a morphism of schemes that factors through a closed immersion
`i : X ⟶ RelativeProjectiveSpace S n`. This module shows that every finite set of
points of `X` lying in one fibre of `f` is contained in an affine open of `X`. The
proof of `Langlands.AbelianScheme.FiniteEtaleQuotientExistenceStatement` uses it to
find affine opens containing the orbits of a finite subgroup acting on a projectively
embedded abelian scheme. Worker 934 fixed the statement as the interface for that
assembly.

## Provenance

This module is derived infrastructure for this task. Its main input is
`AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj`, which is
already in the Library in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj`
(ported from the Anthropic FLT formalisation). That theorem says: if a scheme maps
by an affine morphism to `Proj 𝒜` for a graded ring `𝒜`, then every finite set of
its points lies in an affine open. This module reduces the fibre statement to that
theorem. It uses the Library definitions `RelativeProjectiveSpace`, `toBase` and
`toIntegral` from `Langlands.AlgebraicGeometry.RelativeProjectiveSpace`, and the
integral model `ProjectiveSpace (ULift ℤ) n = Proj (projectiveSpaceGrading (ULift ℤ) n)`
from `Langlands.AlgebraicGeometry.ProjectiveSpace`.

## Declarations

All schemes are in one universe `u`. The declarations are in the namespace
`Langlands.AlgebraicGeometry.RelativeProjectiveSpace`.

### `isAffineHom_preimage_ι_toIntegral`

Let `V` be an affine open of `S`. Then the composite of the open immersion
`(toBase S n ⁻¹ᵁ V).ι` with `toIntegral S n` is an affine morphism to the integral
model `ProjectiveSpace (ULift ℤ) n`.

Proof. `RelativeProjectiveSpace S n` is the pullback of `S ⟶ ⊤_` and
`ProjectiveSpace (ULift ℤ) n ⟶ ⊤_` (with `toBase` and `toIntegral` as projections).
Pasting it with the restriction square `isPullback_morphismRestrict (toBase S n) V`
shows that the composite is a base change of the map `V.ι ≫ terminal.from S` from
`V` to the terminal scheme. That map is affine, found by instance search, since `V`
and the terminal scheme are affine. Affine morphisms are stable under base change
(`MorphismProperty.of_isPullback`).

### `exists_isAffineOpen_forall_mem_of_fibre`

Let `f : X ⟶ S`, let `i : X ⟶ RelativeProjectiveSpace S n` be a closed immersion
with `i ≫ toBase S n = f`, let `F` be a finite set of points of `X` and let `s` be a
point of `S` with `f x = s` for all `x ∈ F`. Then there is an affine open `W` of `X`
that contains every point of `F`.

Proof.

1. Choose an affine open `V` of `S` containing `s`
   (`exists_isAffineOpen_mem_and_subset`). Put
   `U = i ⁻¹ᵁ (toBase S n ⁻¹ᵁ V)`. Every point of `F` lies in `U`, since
   `toBase S n (i x) = f x = s ∈ V`.
2. Let `φ : U ⟶ Proj (projectiveSpaceGrading (ULift ℤ) n)` be the composite of the
   restriction `i ∣_ (toBase S n ⁻¹ᵁ V)`, the open immersion
   `(toBase S n ⁻¹ᵁ V).ι` and `toIntegral S n`. The restriction of a closed
   immersion is a closed immersion, hence affine, and the remaining composite is
   affine by `isAffineHom_preimage_ι_toIntegral`. So `φ` is affine.
3. Apply `AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_isAffineHom_proj` to
   `φ` and the finite set `F.subtype (· ∈ U)` of points of `U`. It gives an affine
   open `W` of `U` containing all of them.
4. The image `U.ι ''ᵁ W` is an affine open of `X`
   (`IsAffineOpen.image_of_isOpenImmersion`) and contains every point of `F`.

The statement has no hypotheses on `S`; in particular `S` need not be Noetherian.
