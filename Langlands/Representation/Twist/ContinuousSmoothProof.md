# Proof of smoothness invariance under continuous complex twists

The published target, supporting declarations and source pairs were checked.

For a continuous complex character,
`isOpen_ker_of_continuous_complex_character` supplies the open kernel.
Applying `isSmoothVector_twist_iff` to that kernel proves
`isSmoothVector_twist_iff_of_continuous`. Applying
`isSmooth_twist_iff` proves `isSmooth_twist_iff_of_continuous`.
The closing theorem introduces the nonarchimedean instance inside the
entire target and packages the two results.

The group `G : Type uG` and module `V : Type uV` have independent carrier
universes. Besides the group, topology, additive group and complex module
structures, the reusable lemmas require `[NonarchimedeanGroup G]` and
`Continuous chi`. The closing theorem introduces that nonarchimedean
instance at the target's internal binder, before the character,
representation and continuity proof. No nonarchimedean instance is added
as an external premise to the closing theorem.

No topology or dimension restriction is imposed on `V`, and no prior
smoothness of the representation is assumed. The character need not be
unitary. There are no local compactness or separation assumptions.
The proof does not construct the nonarchimedean instance for a concrete
group. Both reusable corollaries are kept in this one proof module.

The target is `Langlands.ContinuousComplexTwistSmoothCompatibility`
in `Langlands.Representation.Twist.ContinuousSmoothStatement`.
The target and supporting declarations were read in the Library, and the
Library source files matched the local copies byte for byte.

The mathematical proof dependencies are published Library declarations:

- `Langlands.isOpen_ker_of_continuous_complex_character` in
  `Langlands.Representation.Twist.ContinuousCharacterProof`.
- `Langlands.isSmoothVector_twist_iff` and `Langlands.isSmooth_twist_iff` in
  `Langlands.Representation.Twist.SmoothProof`.

Their definitions come from `Langlands.Representation.Twist.Definitions`
and `Langlands.Representation.Smooth.Definitions`.
All were verified in the Library with unchanged source hashes.
The open-kernel result supplies exactly the premise required by each
smooth-twist equivalence, specialized to complex coefficients. The imported
definition `IsSmoothVector` means that an open subgroup fixes the vector,
and `IsSmooth` quantifies this property over all vectors. The imported twist
acts by multiplying the original action by the character value.

Environment: Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The provenance is the internal composition described above. There is
no new external theorem assumed and no local Langlands result asserted.
