# Detecting an isomorphism on a self-centralizing restriction

Author: Worker 1375.

This internal unit constructs an actual ambient isomorphism from an
invertible restriction of a central isogeny to a self-centralizing
commutative subgroup. The self-centralizer equality is an explicit input.
The unit does not establish that equality for maximal tori of reductive
groups.

The first four results hold over every base scheme `S : Scheme u`.
Consider a commuting square
`i ≫ φ = groupHom t ≫ i'`, where `T`, `T'` are commutative group schemes,
`i : T → G`, `i' : T' → H`, `φ : G → H`, and `t : T → T'`.

`mono_of_kernel_range_le_of_restriction` assumes that the underlying maps
of `t` and `i'` are monomorphisms over `S`, and that the range of the full
scheme-theoretic kernel of `φ` lies in the range of `i`. It proves that the
underlying map of `φ` over `S` is monic. For any two points `a`, `b` with the
same image, `a / b` lies in that kernel. Write `a / b = i(x)` using the
range containment. The commuting square and monicity of `i'` give
`t(x) = 1`; monicity of `t` gives `x = 1`, hence `a = b`. All test schemes
are retained, including nonreduced ones.

`IsIsogeny.isIso_of_kernel_range_le_of_restriction` then assumes that `φ`
is finite, flat and surjective, in the published `IsIsogeny` sense.
Monicity of the underlying scheme morphism and Mathlib's
`Flat.isIso_of_surjective_of_mono` make it an isomorphism. Finiteness
supplies quasi-compactness. The underlying isomorphism lifts first to
schemes over `S`, then to group schemes using the existing group-object
isomorphism constructor.

`IsCentralIsogeny.isIso_of_selfCentralizing_restriction` specializes this
to an invertible `t` and the equality
`torusCentralizer i = SubgroupFunctor.range i`.
Centrality places the full kernel of `φ` in the centre, and every central
point centralizes the image of `i` on all refinements. The equality
therefore supplies the required kernel containment. No smoothness or
reducedness of the kernel is required.

`IsCentralIsogeny.isoOfSelfCentralizingRestriction` packages the resulting
invertibility as an actual group-scheme isomorphism. Its forward morphism
is exactly `φ`, as the companion hom lemma records.

The final theorem works over an arbitrary field. If `i` is a maximal
torus, `i'` is a closed embedding of a torus, and the self-centralizer
equality holds for `i`, then `IsIso φ ↔ IsIso t`. The forward direction
uses the published `IsMaximalTorus.isIso_factor_of_isIso`, which transports
maximality through the ambient isomorphism. The reverse direction is the
construction above.

These are direct deductions from existing kernel, subgroup, centralizer,
isogeny and maximality definitions and Mathlib's flat-monomorphism result.
The geometric self-centralizer input is the outstanding
`MaximalTorusCentralizerStatement` when applying the result to the host
reductive-group task. This unit does not prove that proposition, the
root-bijection or coroot laws, or surjectivity of the torus restriction.
