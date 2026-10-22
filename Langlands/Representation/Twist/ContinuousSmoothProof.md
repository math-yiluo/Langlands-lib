# Proof of smoothness invariance under continuous complex twists

Worker 4 authored this derived proof. Worker 32 checked the published target,
supporting declarations and source pairs, retained the Lean proof unchanged,
and prepared this contribution for independent validation and review.

For a continuous complex character,
`isOpen_ker_of_continuous_complex_character` supplies the open kernel.
Applying the accepted `isSmoothVector_twist_iff` to that kernel proves
`isSmoothVector_twist_iff_of_continuous`. Applying the accepted
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
The target and supporting declarations were read in the current Library at
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`.
The workspace's recorded Library base is that commit, with no refresh
conflicts. Its Library source pairs match the workspace copies byte for
byte. The target pair and its imported pairs are preserved.

The mathematical proof dependencies are published Library declarations:

- `Langlands.isOpen_ker_of_continuous_complex_character` in
  `Langlands.Representation.Twist.ContinuousCharacterProof`.
- `Langlands.isSmoothVector_twist_iff` and `Langlands.isSmooth_twist_iff` in
  `Langlands.Representation.Twist.SmoothProof`.

Their definitions come from `Langlands.Representation.Twist.Definitions`
and `Langlands.Representation.Smooth.Definitions`.
All were verified in the current Library with unchanged source hashes.
The open-kernel result supplies exactly the premise required by each
smooth-twist equivalence, specialized to complex coefficients. The imported
definition `IsSmoothVector` means that an open subgroup fixes the vector,
and `IsSmooth` quantifies this property over all vectors. The imported twist
acts by multiplying the original action by the character value.

Environment: `2ecc41bc-2901-4e34-96c5-6d98fbb3c74d` v1, Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The provenance is the internal composition described above. There is
no new external theorem assumed and no local Langlands result asserted.
Development compilation is distinct from the required exact-target and
allowed-assumption inspection, independent semantic review and publication.
