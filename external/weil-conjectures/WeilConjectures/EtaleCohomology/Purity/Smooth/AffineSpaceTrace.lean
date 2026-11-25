/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# The affine-space trace

For the projection `p : 𝔸^d_S ⟶ S` of relative affine space, the *affine-space trace*
`t_p : Rp_! Λ(d)[2d] ⟶ Λ_S` is an isomorphism (blueprint `lemma-integral-linear-character--1`, a
step of the model purity `proposition-purity-vector-bundles`): the compactly supported cohomology of
affine `d`-space is `Λ(-d)` in degree `2d` and vanishes otherwise.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`:
  `Rp_! Λ(d)[2d] ≅ Λ_S`.

## Implementation notes

As for the other model purity statements
(`WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace`), the trace map itself, the counit
of the affine-space adjunction, is not constructed: the projective-line trace it is built from
is not available. Only the existence of the isomorphism is recorded.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]

/-- Blueprint `lemma-integral-linear-character--1`: the affine-space trace is an isomorphism.

For the projection `p : 𝔸(n; S) ⟶ S` of relative affine space of dimension `d = #n`, over a
scheme `S` on which the exponent of `Λ` is invertible, the compactly supported direct image of
the twisted constant complex is the constant complex: `Rp_! Λ(d)[2d] ≅ Λ_S`. Equivalently
`Rp_! Λ ≅ Λ_S(-d)[-2d]`: compactly supported cohomology of affine `d`-space is `Λ(-d)`,
concentrated in degree `2d`. -/
theorem nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace
    [HasTateTwist.IsNormalized Λ] (n : Type u) [Fintype n] (S : Scheme.{u})
    [HasInvertibleExponent Λ S] [HasCompactification (𝔸(n; S) ↘ S)] :
    Nonempty ((R(𝔸(n; S) ↘ S)_![ModuleCat.{u + 1} Λ]).obj
        ((twistShift Λ 𝔸(n; S) (Fintype.card n)).obj (constantComplex Λ 𝔸(n; S))) ≅
      constantComplex Λ S) :=
  sorry

end AlgebraicGeometry.Etale
