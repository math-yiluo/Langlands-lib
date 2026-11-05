# Solvability through a represented quotient

This is an internal, derived contribution to the proof of
`FiniteFieldCentralCocharacterSolvableStatement`. It isolates the passage from a
solvable quotient by the unipotent radical to solvability of the original group.
It uses the existing definitions and proved point-group results, and introduces
no assertion from external literature.

For group schemes `N`, `G`, and `Q` over any scheme `S`, and morphisms
`i : N ⟶ G` and `q : G ⟶ Q`, the hypothesis
`range (kernelι q) = range i` is equality of subgroup functors on every test
scheme. If `N(T)` and `Q(T)` are solvable, then `G(T)` is solvable.
`SolvableQuotientExtension.kernelPointsToRange` constructs the canonical
injective group homomorphism from the kernel of `q(T)` to the range of `i(T)`.
Its underlying function is the identity on the ambient points; the stated
kernel equality supplies membership in the range. Its injectivity follows
from equality of underlying points.

The solvability proof applies Mathlib's `Group.isSolvable_of_ker_le_range`
to the point maps, using this constructed homomorphism's membership
certificate. The result requires neither injectivity of `i(T)` nor
surjectivity of `q(T)`.

`SolvableQuotientExtension.points_of_isFppfQuotient` specializes this argument to
the existing `RelativeRoot.IsFppfQuotient` interface by extracting its kernel
equality. Its geometric cover conditions are unnecessary for this point-group
argument.

Over an arbitrary field, `isSolvableGroupScheme_of_kernel_range` applies the
point result to `Spec k̄ → Spec k`. The published `baseChangePointsEquiv`
transports the defining geometric solvability of `N` and `Q` to this test
scheme; `isSolvableGroupScheme_of_isSolvable_points` transports the result back.
No smoothness, affineness, connectedness, or finite-type assumption is needed
for this general extension result.

`isSolvableGroupScheme_of_solvable_fppfQuotient` is its fppf specialization.
Finally, `isSolvableGroupScheme_of_unipotent_fppfQuotient` assumes that `N` is
affine, locally of finite type, and unipotent. It uses the published
`isSolvable_points_of_isUnipotent` to supply the kernel's geometric solvability.
This last result proves solvability of `G` from solvability of `Q`.

These declarations do not establish finite-field quasi-splitness, lift
cocharacters, or prove the host statement. Those are separate remaining steps.
