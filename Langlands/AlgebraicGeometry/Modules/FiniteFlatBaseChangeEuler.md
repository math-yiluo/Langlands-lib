# Euler characteristics after twisting or finite flat base change, under finite support

Lean module: `Langlands.AlgebraicGeometry.Modules.FiniteFlatBaseChangeEuler`,
namespace `Langlands.AlgebraicGeometry.Modules.DerivedSections`.

Author: Worker 998.

## Role and provenance

This is internal infrastructure for task `981f6bcb-41de-4a08-83b8-48b6eec2b236`, the proof
of `Langlands.AbelianScheme.AlgClosedFieldAmpleEulerInverseScalingStatement`
(`χ(H^k) χ(H^{-k}) = k^{2g} χ(H) χ(H^{-1})` for ample `H`). That proof works on
`Z = A ×_K A` with the line bundle `Q = m^* H ⊗ p₁^* H^{-1}` and the second projection
`q = p₂ : Z ⟶ A`. The higher direct images of `Q` along `q` have finite support. Two steps
change `Q` without changing its Euler characteristic, or by multiplying it with a known
factor:

1. Twisting by `q^* E` for a line bundle `E` on `A`. This is formula (10) in the proof of
   (9.11) of Edixhoven, van der Geer and Moonen, *Abelian Varieties* (registered source
   `edixhoven-vandergeer-moonen-abelian-varieties-draft`, printed p.132, PDF p.136).
2. Pulling back along `1 × [k]`, the base change along `q` of the finite flat
   multiplication `[k]` of degree `k^{2g}`. With finite support this multiplies `χ` by the
   degree. This is an analogue, for line bundles whose direct images have finite support, of
   EvdGM (9.12) (`χ(f^* L) = deg(f) · χ(L)` for an isogeny `f`), printed p.131.

This module proves both steps for an arbitrary morphism `q : Z ⟶ Y` over a field, as the
anchor proposition `FiniteSupportEulerScalingStatement`. The anchor is internal: it is
exactly the conjunction of the two theorems below and is proved in the same module
(`finiteSupportEulerScaling`). Its proof does not follow the source, which uses
intersection theory for (9.12). It uses the finite support and the local freeness of
`f_* 𝒪`.

## Declarations

- `pushforwardPullbackLineBundleIso φ F`: for a morphism `φ : Z₁ ⟶ Z` and a line bundle `F` on
  `Z`, `φ_* φ^* F ≅ F ⊗ φ_* 𝒪_{Z₁}`. It combines the right unitor with the Library projection
  formula `lineBundleProjectionIso φ F 𝒪`.
- `eulerCharacteristic_finiteFlatBaseChange`. Let `K` be a field, `s : Y ⟶ Spec K`, and
  `q : Z ⟶ Y`. Let `f : Y₁ ⟶ Y` be finite, flat and locally of finite presentation with
  `f.finrank y = d` at every point. Let `φ : Z₁ ⟶ Z` and `q₁ : Z₁ ⟶ Y₁` make a cartesian
  square with `q` and `f` (`IsPullback φ q₁ q f`). Let `F` be a line bundle on `Z` with finite
  cohomology along `q ≫ s`, all of whose higher direct images along `q` have finite closed
  support. Then `φ^* F` has finite cohomology along `φ ≫ q ≫ s`, and
  `χ(Z₁, φ^* F) = d · χ(Z, F)`.
- `FiniteSupportEulerScalingStatement`: the anchor proposition. Its first conjunct is the
  statement of `eulerCharacteristic_twist` (module `FiniteSupportTwistEuler`), for every field
  `K`, all `Y`, `Z`, `s`, `q`, every line bundle `F` on `Z`, every module `W` on `Y` with free
  charts of rank `d`, under finite closed support of every `R^n q_* F` and finite cohomology
  of `F`. Its second conjunct is the statement of `eulerCharacteristic_finiteFlatBaseChange`
  with all data universally quantified.
- `finiteSupportEulerScaling`: the anchor proposition holds. The proof applies the two
  theorems.

## Proof of `eulerCharacteristic_finiteFlatBaseChange`

`φ` is finite, as a base change of `f` (`MorphismProperty.of_isPullback`), hence affine. Let
`W = f_* 𝒪_{Y₁}`. There is an isomorphism `φ_* φ^* F ≅ F ⊗ q^* W`. It is
`pushforwardPullbackLineBundleIso`, followed by
`pushforwardStructureSheafBaseChangeIso : φ_* 𝒪_{Z₁} ≅ q^* W` (module
`FiniteFlatPushforwardFreeCharts`). `W` has free charts of rank `d`
(`exists_freeChart_pushforward_structureSheaf`). So `eulerCharacteristic_twist` gives finite
cohomology of `F ⊗ q^* W` and `χ(F ⊗ q^* W) = d · χ(F)`. By the Library's
`affinePushforwardEulerCharacteristic` for the affine morphism `φ` and the quasi-coherent
module `φ^* F`, `φ^* F` has finite cohomology along `φ ≫ (q ≫ s)` exactly when `φ_* φ^* F`
has it along `q ≫ s`, and the two Euler characteristics agree. The isomorphism above and the
Library's `eulerCharacteristic_eq_of_iso` finish the proof.

No flat base change for higher direct images is used. The only base change needed is that of
`f_* 𝒪`, which `FiniteFlatPushforwardFreeCharts` proves. The axioms are `propext`,
`Classical.choice` and `Quot.sound`.
