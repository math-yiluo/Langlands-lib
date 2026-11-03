# fpqc descent of flatness, separatedness, properness and finiteness

Author: Worker 712.

Module `Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent`, namespace
`Langlands.AlgebraicGeometry.FpqcDescent`. All declarations are in the universe
of `Scheme.{u}` for arbitrary `u`. The covering class is Mathlib's fpqc class
`@Surjective ⊓ @Flat ⊓ @QuasiCompact`. A `DescendsAlong P Q` instance says:
if `f : X ⟶ Z` satisfies `Q`, `g : Y ⟶ Z` is arbitrary, and the base change
`pullback.fst f g` satisfies `P`, then `g` satisfies `P`.

Mathlib already provides this descent for `Surjective`, `UniversallyClosed`,
`LocallyOfFiniteType` and `LocallyOfFinitePresentation`, and for isomorphisms
(`Morphisms.FlatDescent`, `Morphisms.LocalFlatDescent`). This module adds the
four properties below. They are the standard fpqc descent results for
morphisms of schemes (classically EGA IV_2, Proposition 2.7.1); the Lean
proofs are internal and follow the routes described here.

## Flatness

- `flat_codescendsAlong_faithfullyFlat :
  RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat`. For ring maps
  `R → S` and `R → T` with `R → T` faithfully flat, if the pushout map
  `T → T ⊗[R] S` is flat then `R → S` is flat. The proof is Mathlib's
  `Module.Flat.of_flat_tensorProduct`.
- Instance `descendsAlong_flat_surjective_inf_flat_inf_quasicompact :
  DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @QuasiCompact)`, obtained from
  the preceding ring-level statement by Mathlib's
  `HasRingHomProperty.descendsAlong_flat`.

## Separatedness and properness

- `isSeparated_eq_diagonal_universallyClosed :
  @IsSeparated = MorphismProperty.diagonal @UniversallyClosed`. A morphism is
  separated exactly when its diagonal is universally closed. One direction is
  the closed-immersion-implies-universally-closed instance. Conversely, the
  diagonal is always a preimmersion, and a universally closed diagonal has
  closed range, so `IsClosedImmersion.of_isPreimmersion` makes it a closed
  immersion.
- Instance `descendsAlong_isSeparated_surjective_inf_flat_inf_quasicompact`
  for `IsSeparated`. After the rewrite above it is Mathlib's instance that
  `P.diagonal` descends along `Q` whenever `P` does, applied to the existing
  fpqc descent of `UniversallyClosed`.
- Instance `descendsAlong_isProper_surjective_inf_flat_inf_quasicompact` for
  `IsProper`. Mathlib's `isProper_eq` writes properness as
  `IsSeparated ⊓ UniversallyClosed ⊓ LocallyOfFiniteType`, and descent of an
  intersection is the intersection of the three descent instances.

## Finiteness

- `finite_preimage_singleton_of_pullback_fst (f : X ⟶ Z) (g : Y ⟶ Z)
  [Surjective f] (h : ∀ x, (pullback.fst f g ⁻¹' {x}).Finite) (z : Z) :
  (g ⁻¹' {z}).Finite`. Choose `x` over `z`. Every point of the fibre of `g`
  over `z` is the image under `pullback.snd f g` of a point of the fibre of
  `pullback.fst f g` over `x` (`Scheme.Pullback.exists_preimage_pullback`), so
  that fibre is the image of a finite set.
- Instance `descendsAlong_isFinite_surjective_inf_flat_inf_quasicompact` for
  `IsFinite`. Given an fpqc `f` and a finite base change
  `pullback.fst f g`, properness of `g` descends by the preceding instance.
  The finite base change has finite fibres
  (`Scheme.Hom.finite_preimage_singleton`), so `g` has finite fibres by the
  preceding lemma. Since `g` is locally of finite type,
  `LocallyQuasiFinite.of_finite_preimage_singleton` makes it locally
  quasi-finite. Mathlib's Zariski main theorem consequence
  `IsFinite.iff_isProper_and_locallyQuasiFinite` (Stacks 02LS) then makes `g`
  finite. This route needs no separate descent of affineness.

There are no hypotheses beyond those displayed: no Noetherian, finite
presentation or locally Noetherian condition is imposed on the schemes or on
`g`.
