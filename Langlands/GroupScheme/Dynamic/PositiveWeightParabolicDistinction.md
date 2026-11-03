# Positive Lie weights distinguish opposite dynamic parabolics

This is an internal supporting construction derived from the published actual
Lie-weight and dynamic-subgroup interfaces. It records a condition on the actual
Lie algebra and proves a consequence needed when distinguishing opposite
parabolics in reflection geometry. No external source passage is claimed.

For a field `k : Type u`, an affine group scheme `G` over `Spec k`, and a
cocharacter `χ : Gm → G`, `Dynamic.HasPositiveLieWeight χ` means that there exist
`n : ℕ` and `X : lieKernel G k` such that `X ≠ 1` and `Additive.ofMul X` belongs
to `weightSpace χ (Gm.powerHom _ (n + 1))`. The identity `1` in the actual
reduction kernel is the zero vector after passage to the additive Lie algebra.
The weight space uses the published adjoint action and its condition over every
commutative test algebra.

If `G` is also locally of finite type, then
`Dynamic.HasPositiveLieWeight.parabolic_ne_opposite` proves
`Dynamic.parabolic χ ≠ Dynamic.parabolic (Dynamic.oppositeCocharacter χ)`.
`Dynamic.parabolic_ne_opposite_of_positive_weight` gives the same conclusion
with explicit `n`, `X`, nonzero and weight-membership arguments. These assertions
hold over an arbitrary field and in every universe `u`; no smoothness,
reductivity, splitness, characteristic or perfectness hypothesis is used.

The proof proceeds through the actual dual-number point `X.val`. The unipotent
clause of the published `Langlands.GroupScheme.dynamicLie` identifies the sum
of strictly positive weight spaces with membership of `X.val` in the actual
functor `Dynamic.unipotent χ`. Inclusion of the given weight space in that sum
therefore supplies this membership. Injectivity of the subgroup carrier
inclusion turns `X ≠ 1` into `X.val ≠ 1`.

The supporting theorem `Dynamic.parabolic_ne_opposite_of_mem_unipotent` is more
general: over an arbitrary commutative ring `R`, for affine `G` and any test
scheme `U` over `Spec R`, a nonidentity `g ∈ Dynamic.unipotent χ` implies the
same parabolic inequality. If the parabolics were equal, the inclusion
`Dynamic.unipotent_le_parabolic` would put `g` in the opposite parabolic. The
published theorem
`Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`, applied to the
opposite cocharacter, then forces `g = 1`.

For this application,
`Dynamic.oppositeCocharacter_oppositeCocharacter` proves that reversing the
parameter twice returns `χ`, over every base scheme and for every group
scheme. Its proof writes `Gm.powerHom _ (-1)` as the negative identity in the
preadditive category of commutative group schemes, computes its square as the
identity, and uses preservation of composition by `CommGroupScheme.groupHom`.

The condition and its consequences concern the existing all-test-scheme
subgroup functors, including the dual-number test scheme in the Lie argument.
They do not assert existence of a positive weight or of a nontrivial rational
unipotent point. They do not prove either `GenericCentralizerStatement` or
`StandardParabolicEndpointsStatement`; both exact host-task proof obligations
remain separate.
