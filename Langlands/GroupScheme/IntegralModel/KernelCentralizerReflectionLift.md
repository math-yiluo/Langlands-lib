# Ambient reflections from an integral kernel-centralizer component

This internal construction supplies cell-coordinate transport and an actual
ambient generic normalizer for the relative identity component of the full
scheme-theoretic character-kernel centralizer. It works at arbitrary universe
`u`, retaining the original integral torus, character and ambient integral model.

For any group-scheme homomorphism `f : H → G` over any base, and any cocharacter
`χ` of `H`, `Dynamic.exists_oppositeCellPoint_image` maps a point of a represented
`U(-χ) × P(χ)` cell to an actual point of any represented target cell for `χ ≫ f`.
The two product images agree exactly after composition with `f`. The proof
projects the source coordinates, uses functoriality of the dynamic unipotent and
parabolic functors, then uses target representability to choose coordinates.
It applies to every relative test scheme and makes no field or smoothness
assumption.

Let `R` be a domain with a specified fraction field `K`, let `M` be an integral
model, let `i : T → M.group` have split torus `T`, and let `a` be a character of
`T`. For `D : KernelCentralizerData M i a`,
`D.ambientGenericNormalizer hT m σ hm` sends an actual integral component point
`m` normalizing `D.torus hT` through the specified automorphism `σ` to a point of
`normalizerPoints (M.genericHom i)`. Its underlying point is exactly
`M.integralPointMap (rationalPoints.map (D.componentHom ≫ D.fullHom) m)`.
The construction composes the normalizing equation through the original
ambient map, changes base to `K`, and composes with the specified `M.genericIso`.

If the ambient generic group is affine, the generic torus inclusion is monic,
`a_K` is an actual ambient relative root, and `characterAut σ a = -a`,
`ambientGenericNormalizer_isRelativeReflection` proves that the Weyl class of
this same normalizer is the ambient relative reflection for `a_K`.
Base change preserves character negation, and uniqueness of the normalizing
automorphism identifies its Weyl action. The component point factors through
the actual full generic centralizer. Its all-test representing property and
the commuting generic torus square transport that membership to the original
generic group. The existing full-kernel reflection theorem then proves the
assertion on the rational root span.

The provenance is internal composition of dynamic functoriality,
`KernelCentralizerData.torus_comp_ambient`, normalizer base change,
`fullGenericRepresents`, full character-kernel centralizer transport, and
`IsSplitTorus.isRelativeReflection_of_mem_kernelCentralizer`.
The full character kernel is retained, including a nonreduced kernel.
No closedness of the relative component inclusion is assumed. This unit
supplies helpers for integral opposite-factor arguments; it contains no
residue quotient construction and does not prove the host Galois-fixed
opposite-factor statement.
