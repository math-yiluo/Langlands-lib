# Algebraicity and geometry of tensor base changes of Weil restrictions

This is an internal supporting construction for the adelic Weil restriction
comparison. It is derived from the published full-test comparison
`weilRestrictionBaseChangePresheafIso`, the base change of algebraic spaces,
and transport of atlases and diagonal properties along presheaf isomorphisms.
It asserts neither the existence of the original Weil restriction nor a
topological comparison.

For a cartesian square with maps `g : S' → S`, `f : T → S`,
`f' : T' → S'`, and `g' : T' → T`, let `X'` be an algebraic space over
`S'`. Suppose the Weil restriction along `g` is an algebraic space.
`isAlgebraicSpace_weilRestriction_baseChange` proves that the restriction
along `g'` of the base change along `f'` is an algebraic space as well:
it is isomorphic, on all test schemes over `T`, to the base change along
`f` of the original algebraic Weil restriction. The corresponding
`weilRestrictionBaseChangeIso` therefore needs just the original
algebraicity witness.

The separatedness and quasi-separatedness lemmas base change the original
diagonal and transport its closed-immersion or quasi-compact property through
the same full presheaf isomorphism. The atlas lemma does the same for any
property of scheme structure maps stable under base change. Its atlas is
the base change of the original atlas, followed by the presheaf comparison.

The tensor specialization starts with commutative rings `R`, `B`, `C`,
and `D`, their displayed algebra structures, and a specified equivalence
`e : C ⊗[R] B ≃ₐ[C] D`. It also requires
`e (1 ⊗ b) = algebraMap B D b`. There is no finiteness, separability,
field, or topology assumption. The spectrum of `e`, followed by the
published tensor-spectrum isomorphism, identifies `Spec D` with
`Spec C ×_(Spec R) Spec B`. Its two proved projection formulas are the
original maps to `Spec C` and `Spec B`. These formulas, and the pullback
condition, prove the cartesian square with exactly those maps.

Consequently `isAlgebraicSpace_ringWeilRestriction_tensor` derives the
algebraicity of `Res_(D/C)(X'_D)` from that of `Res_(B/R)(X')`.
`ringWeilRestrictionTensorBaseChangeIso` identifies the scalar extension
of the latter with the former, using the ordinary base change of `X'`
along the original map `B → D`. The construction is valid on the full
category of test schemes, including when `D` is a specified product of
completed local rings. The equivalence and its coefficient law must
still be supplied by the arithmetic tensor results.
