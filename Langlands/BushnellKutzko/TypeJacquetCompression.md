# Jacquet nonvanishing from injective compression

The module `Langlands.BushnellKutzko.TypeJacquetCompression` gives a criterion
in the namespace `Langlands.Jacquet`. It expresses the contraction argument of
BK93 (7.3.2) in terms of the span of the Jacquet relations and powers of a
compressed operator. The smooth scope comes from (7.3.6)(i).
[Source details](LevelZeroNonmaximalTypeJacquetProof.md#source)

For a smooth complex representation `ρ` and a compact open subgroup `K`,
`compressionMap ρ hρ K hK g` is the endomorphism `v ↦ e_K (ρ(g) v)`, where
`e_K` is the normalized average `Compact.averageMap`. On `K`-fixed vectors,
`compressionMap_mul_of_factor` composes compression by `x` with compression by
`y` to give compression by `x * y` if every `k ∈ K` factors as `u * l` with
`x u x⁻¹ ∈ K` and `y⁻¹ l y ∈ K`. If `x⁻¹ K x ⊆ K`, then
`compressionMap_of_normalizes` identifies compression by `x` on `K`-fixed
vectors with the action of `x`.

## Nonvanishing criterion

Let `K = (K ∩ Nbar)(K ∩ M)(K ∩ N)`, let `M` normalize `N`, and suppose `g`
is a weak Iwahori contraction for these subgroups in the sense of
`IsWeakIwahoriContraction`. Assume also that some power of `g` carries each
element of `N` into `K` by conjugation. The factorization and this last
condition are separate hypotheses. The proof of the power identity for
`compressionMap` uses `IsWeakIwahoriContraction.compressedAction_pow` on the
fixed-vector submodule.
[Weak Iwahori contraction](../Representation/Jacquet/WeakIwahoriBasis.md)
[Compression powers](../Representation/Jacquet/JointIwahoriEigenCoefficient.md)

Every Jacquet relation `ρ(n) w - w` is killed by `e_K ∘ ρ(g^s)` for all large
`s`. Indeed, conjugation by `g^s` carries `n` into `K` for all large `s`, and
the average absorbs translation by an element of `K`. Span induction extends
this to the entire relation submodule. Consequently,
`exists_pow_compressionMap_eq_zero` gives local nilpotence on the fixed-vector
submodule when the coinvariants vanish.

In `not_subsingleton_coinvariants_of_compression`, a nonzero linear map from
a finite-dimensional space `W` into the `K`-fixed vectors belongs to a family
stable under compression. If the coinvariants vanished, taking the maximum
of the powers that kill the images of a basis of `W` would give one power
that kills the whole map. The hypothesis that compression kills only the
zero map in the family then gives a contradiction by induction on that power.
