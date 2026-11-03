# Root movement by opposing dynamic parabolics

This derived helper retains the normalizing point and its all-test opposing
parabolic inclusion as explicit inputs. It does not establish intrinsic
existence of that point.

For an affine group scheme locally of finite type over an arbitrary field, a
nonzero adjoint weight space whose character pairs positively with a supplied
cocharacter contains a nonzero actual Lie vector. The dynamic Lie theorem puts
its dual-number point in the positive unipotent subgroup. If a normalizing
point fixed that character, its adjoint image would also have positive weight.
The opposing parabolic inclusion places this image in the opposite parabolic.
The actual opposite unipotent/parabolic intersection is trivial. Invertibility
of the adjoint action then contradicts the original vector's nonvanishing.

If the torus is split and the normalizer centralizes the full scheme-theoretic
kernel of a nonzero root character, integral divisibility of all character
differences and the integral rank-one unit argument imply that this moved
character is sent to its negative. No primitivity or reducedness assumption on
the character kernel is introduced.

`corootOfKernelCentralizingOppositeParabolic` then returns an actual integral
cocharacter together with self-pairing two and the reflection formula on every
character, using the published unique-coroot extraction theorem. The supplied
normalizer and its full-kernel centralization are retained throughout.

The proof derives these conclusions from `dynamicLie`,
`weightSpace_le_comp`, the normalizer's actual adjoint weight transport,
`Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic`,
`exists_integral_difference_of_mem_kernelCentralizer`, and
`IntegralRootLine.apply_eq_neg_of_ne`, followed by
`IsSplitTorus.existsUnique_coroot_of_mem_kernelCentralizer`. It supplies the root-movement calculation
needed after a geometric opposing conjugator has been constructed; it does not
prove opposing parabolic existence, minimality, conjugacy, or the host
reflection-existence proposition.
