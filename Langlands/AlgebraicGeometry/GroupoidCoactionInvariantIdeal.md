# Invariant ideals and coaction filtrations

Worker 148. This is internal algebra derived from the existing coaction, regular
coaction, Hom coaction, and stable-submodule constructions. It makes no use of a
geometric descent or acyclicity theorem. The coefficient rings have arbitrary
universe `u`; the module has independent universe `v`.

For an ideal `I` of `B`, `IsInvariantIdeal t I` means the literal equality
`I.map t = I.map (algebraMap B C)`. Its two sides are the target and source
extensions of `I`. Ideal-map identities show that this property is closed under
sums, products, and natural-number powers, without an étale hypothesis.

The map `idealTensorMap I : C ⊗[B] I →ₗ[C] C` tensors the inclusion of `I`
and applies tensor cancellation. On a pure tensor `c ⊗ b` it gives
`algebraMap B C b * c`. Its range is exactly the source extension of `I`.
One containment follows by tensor induction and ideal closure under
multiplication and addition. For the other, the tensor `1 ⊗ b` lifts each
image of an element of `I`, which suffices by the universal property of the
extended ideal.

For the regular coaction on `B`, whose value on `b` is `t b ⊗ 1`, this range
identity proves that stability of `I` is equivalent to
`I.map t ≤ I.map (algebraMap B C)`. For a `RingEtaleEquivalenceRelation t`,
applying its reversal map to this containment gives the reverse containment:
reversal interchanges the source and target maps. Thus regular-coaction
stability is equivalent to `IsInvariantIdeal t I`.

For a finitely presented `B`-module `M` with coaction `θ`,
`hom_coaction_lsmul` proves that the scalar-endomorphism map
`LinearMap.lsmul B M : B →ₗ[B] (M →ₗ[B] M)` commutes with the regular and Hom
coactions. The identity endomorphism is invariant because it is equivariant.
Since the scalar endomorphism of `b` is `b • id`, the Hom coaction's
semilinearity gives the required tensor equality. This is stated as a direct
equality, permitting `M` to lie in an independent universe.

`annihilator_isInvariantIdeal` identifies the annihilator of `M` with the kernel
of this scalar-endomorphism map. Source étaleness supplies flatness of `C` over
`B`. Mathlib's `Module.Flat.ker_lTensor_eq` identifies the kernel after tensoring
with the image of the tensor of the original kernel. For `b` in the annihilator,
the commuting-coaction identity puts the regular coaction of `b` in this tensor
kernel. Hence the annihilator is stable for the regular coaction, and the
preceding equivalence makes it invariant. Finite presentation is used for the
Hom coaction; Noetherianity is not an assumption of this result.

Finally, `isStableSubmodule_iff_lTensor_mkQ_eq_zero` uses the same flat
tensor-kernel identity for a submodule's quotient map. It identifies stability
with vanishing of the coaction after tensoring the quotient. The existing
`ideal_smul_top_stable` theorem supplies this vanishing for `I • M` whenever
the target extension is contained in the source extension. Consequently an
invariant ideal gives a stable submodule `I • M`, and the closure under powers
gives stability of every `I^n • M`.

These results provide invariant ideals and stable filtration terms. They do
not assert vanishing for the associated quotients, exactness of invariants for
the geometric relation, or the host task's acyclicity conclusion.
