# Full Haar-to-block modulus compatibility for p-adic GL parabolics

Author: Worker 106.

`Langlands.Parabolic.generalLinearModulusCompatibility` proves the published
proposition `Langlands.Parabolic.GeneralLinearModulusCompatibility.{uF}`.
Its parameters are exactly a prime `p`, `F : PadicField.{uF} p`, supplied
`T : F.TopologicalData`, a natural rank `n`, and `B : GeneralLinear.BlockShape n`.
The field universe is unrestricted. There are no additional theorem premises.
The target pair and every pair it imports remain unchanged.

The result identifies the actual Haar conjugation character on **the entire
upper block parabolic** with `(T.leviModulus B).comp (B.leviProjection F.Carrier)`.
The topology is precisely `T.topology`, with the target's supplied Hausdorff,
local compactness and nonarchimedean instances. The radical is the existing
closed ambient subgroup `B.unipotentSubgroup F.Carrier`.

## Implemented argument

Write `χ` for the restriction of `HaarModulus.normalizerCharacter` to the actual
parabolic. The closed-subgroup wrapper in the target reduces to this character
once local compactness of the closed radical is installed. The existing
continuous group equivalence
`GeneralLinear.BlockShape.unipotentRadicalAmbientEquiv` identifies the intrinsic
kernel radical with that ambient subgroup. It forgets the intermediate
parabolic membership and preserves the underlying matrix.

For an intrinsic radical element `u`, apply
`Parabolic.unipotentFiniteContainment` to the singleton `{u}`. Pull the resulting
compact open subgroup along the inverse equivalence to obtain a compact open
subgroup `L` of the ambient radical containing the image of `u`. Conjugation by
that image preserves `L`: cancellation of multiplication by members of a
subgroup proves the preimage equality. Consequently
`HaarModulus.normalizerCharacter_eq_one_of_preimage` gives `χ(u) = 1`.

For a product-Levi element `m`, let `φ` be ambient conjugation by its actual
section `B.leviInParabolic F.Carrier m`. Pull a Borel Haar measure `μ` on the
ambient radical back by the inverse continuous group equivalence, obtaining
`ν`. Mathlib's `ContinuousMulEquiv.isHaarMeasure_map` makes `ν` Haar. The existing
`Langlands.glBlockModulusHaar` gives

`ν.map (B.leviAction F.Carrier m) = ((T.leviModulus B m : ℝ≥0)⁻¹) • ν`.

The continuous equivalence intertwines these two conjugation actions by their
underlying matrix formulas. Push the displayed identity forward along the
equivalence. `MeasurableEquiv.map_map_symm`, `Measure.map_map`, and
`Measure.map_smul` give the identical inverse-scaling formula for `μ.map φ`.
`B.continuous_leviAction` supplies measurability of the intrinsic action.

Mathlib's `mulEquivHaarChar_eq` expresses the ambient automorphism character as
`haarScalarFactor μ (μ.map φ)`. Set `d = (T.leviModulus B m : ℝ≥0)`; it is
nonzero because the modulus is unit-valued. The existing
`mul_haarScalarFactor_smul` and `haarScalarFactor_self` give
`d⁻¹ * haarScalarFactor μ (d⁻¹ • μ) = 1`. Multiplication by `d` proves
`χ(B.leviInParabolic F.Carrier m) = T.leviModulus B m`. The explicit
`IsHaarMeasure.nnreal_smul` instance justifies the scalar-factor expression
for the rescaled measure.

Finally `B.decomposition F.Carrier` supplies the actual factorization

`g = (B.unipotentPart F.Carrier g).val *
  B.leviInParabolic F.Carrier (B.leviProjection F.Carrier g)`.

The homomorphism law and the two computed values prove equality on every `g`.
Thus the conclusion is an equality of the full parabolic characters. Haar
pushforward scales by the inverse explicit modulus, so the resulting character
has exactly the positive orientation used for induction and the inverse
orientation used for Jacquet restriction.

## Scope and provenance

This is an internal proof assembling published actual-group results; it adds no
external structural assertion or new Haar normalization. The original modulus
convention and source provenance are those of the unchanged target and
`GLBlockModulusHaarStatement`, as explained in their paired documentation. The
finite-containment theorem and the continuous radical equivalence are imported
from `Langlands.Representation.Parabolic.UnipotentFiniteContainment`; the Haar
scaling theorem is imported from `Langlands.Group.GL.BlockModulusHaarProof`.
The homomorphism and normalization definitions come from the unchanged
`Langlands.Representation.Aubert.GeneralLinearSpecialization`,
`Langlands.Group.HaarModulus`, and `Langlands.Group.GL.Blocks`.

Every step allows rank zero and empty upper-block coordinates. The proof of
finite containment already includes rank zero, and neither the Haar argument
nor the factorization requires a nontrivial radical. One-block shapes and the
trivial radical cases therefore require no additional hypotheses or exceptions.
