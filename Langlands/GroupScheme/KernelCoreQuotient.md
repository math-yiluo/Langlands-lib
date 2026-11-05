# Quotient by the smooth connected kernel core

This is a derived construction from the actual reduction, identity component,
smooth normal quotient and fpqc homomorphism descent already in the Library.
It supplies an intermediate quotient for constructing represented split series.
There is no additional literature assertion in this module.

Let `k` be a perfect field in an arbitrary universe. For a
homomorphism `f : G ⟶ A`, assume that `G` is smooth and affine over `k`, and
that `A` is separated over `k`. The scheme kernel is then affine and locally
of finite type, because its inclusion into `G` is a closed immersion.
`KernelCoreQuotient.core f` is the actual group scheme
`((ker f)_red)^0`; `inclusion f` is the composite of its reduced
identity-component inclusion with the scheme-kernel inclusion.

The imported core construction gives a smooth connected affine group and a
closed inclusion. Its all-test normality follows by applying
`ReducedSubgroup.isNormal_range_identityCoreι_comp` to the normal scheme
kernel. `range_inclusion_le_kernel` and `inclusion_comp` express containment
in the full scheme kernel and annihilation by `f`, respectively. If `f` is
nonzero, `inclusion_not_isIso` proves that the inclusion is not an
isomorphism, by cancelling an assumed inverse in the annihilation equation.

`ReducedSubgroup.factorIdentityCore` factors every homomorphism from a smooth
connected group to an affine locally finite-type group through the target's
actual reduced identity component. Smoothness makes the source reduced, so the
map first factors through the reduction and then through its identity component.
The composition theorem records equality with the original map.
`exists_factor_of_comp_eq_zero` applies this to a smooth connected subgroup
of `G` killed by `f`: all-test containment first factors its inclusion through
the scheme kernel, and the preceding construction then factors it through the
core, with equality of the actual inclusion composites.

`quotientData f` applies `SmoothNormalQuotient.ofClosedNormal` to this closed
normal smooth core. `groupScheme f` is its actual quotient and `projection f`
is its actual group homomorphism from `G`. The module exposes the quotient's
smoothness, separatedness, local finite type and quasi-compactness, and the
projection's smoothness, surjectivity and quasi-compactness. If `G` is connected,
the quotient is connected. `isFppfQuotient` identifies the full scheme kernel of
the projection with the range of the specified core inclusion, on every test
scheme, and supplies flatness, surjectivity and local finite presentation.

The original `f` kills that full kernel. Consequently actual fpqc
homomorphism descent constructs `factor f : groupScheme f ⟶ A`.
`projection_factor` proves the factorization equation; `factor_unique`
proves uniqueness from this equation. `factor_ne_zero` retains nonvanishing
of `f`. Finally, `isUnipotent` applies the existing descent of unipotence along
flat surjective homomorphisms to the quotient projection.

Quotient affineness, finiteness of the descended kernel, identification with
the additive group, and a finite represented split series remain further
obligations. The results here impose no characteristic restriction and no
smoothness or connectedness assumption on the full scheme kernel.

Worker 1561 generalized this construction to perfect fields using the smooth
reduction in `Langlands.GroupScheme.ReducedSubgroup`. The action, normality and
quotient constructions and all-test identities use the same proofs.
