# Base-change squares over an affine open, its fibre and a smaller affine open

Author: Worker 1119.

For morphisms `h : X ⟶ S`, `h₁ : X₁ ⟶ S` and `i : X₁ ⟶ X` with `hi : i ≫ h = h₁`, this module
names the base changes used in the proof of
`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement` and proves the pullback squares
that `RestrictionPerfectModelsStatement` is applied to. It contains no `sorry` and no new
axioms.

## Declarations

- `mapOver h h₁ i hi t : pullback h₁ t ⟶ pullback h t`, the base change of `i` along
  `t : T ⟶ S`, defined as `pullback.lift (fst ≫ i) snd`. For `t = S.fromSpecResidueField s`
  this is the map of fibres `jₖ` used in the statement. Lemmas `mapOver_fst`, `mapOver_snd`.
  `isPullback_mapOver`: the square `(fst, mapOver, i, fst)` is a pullback (`isPullback_of_over`).
- `liftPoint h e φ₀ t ht : pullback h t ⟶ pullback h e` for `ht : t = Spec.map φ₀ ≫ e`, with
  lemmas `liftPoint_fst`, `liftPoint_snd`. `isPullback_liftPoint`: the square
  `(liftPoint, snd, snd, Spec.map φ₀)` is a pullback. Proof: `IsPullback.of_right`, after
  `subst ht`, from the two defining pullback squares.
- `isPullback_liftPoint_mapOver`: the square `(liftPoint h₁, mapOver t, mapOver e, liftPoint h)`
  is a pullback. Proof: `IsPullback.of_right` with outer square `isPullback_mapOver` for `t`
  and right square `isPullback_mapOver` for `e`; commutativity is checked on both pullback
  projections.
- `liftAffineOpen h hV hU hUV : pullback h U.ι ⟶ pullback h hV.fromSpec`, for affine opens
  `U ≤ V`, with lemma `liftAffineOpen_fst`. `isPullback_liftAffineOpen`: the square
  `(liftAffineOpen, snd ≫ hU.isoSpec.hom, snd, Spec.map (S.presheaf.map (homOfLE hUV).op))` is a
  pullback. Proof: `IsPullback.of_right`. The outer square is the defining pullback along
  `U.ι`, transported along `hU.isoSpec` (`IsPullback.of_iso`), using Mathlib's
  `IsAffineOpen.map_fromSpec` and `isoSpec_hom_fromSpec`.
- `fiberι_fst_comp_eq`: for `x` in an open `U`, the fibre of `X ×_S U ⟶ U` over `x`, mapped to
  `X`, lies over `Spec κ(x)` through `Spec` of `U.ι.residueFieldMap x`. Proof: pullback
  conditions and Mathlib's `SpecMap_residueFieldMap_fromSpecResidueField`.

## Provenance

Internal constructions. They realize the base changes in the proof of Stacks tag 0BF2
(`more-morphisms.tex`, lines 9543–9619, registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`). These are the restriction to an affine
neighbourhood of `s`, the fibre over `s`, and the shrinking to a basic open neighbourhood.
