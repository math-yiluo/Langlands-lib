# Character-valuation kernels under finite Galois extension

Author: Worker 706.

This is a derived helper for KP Lemma 2.5.18. It concerns an affine group scheme
`G` over an arbitrary field `k`, a finite Galois extension `L/k`, valuations
`vk : Valuation k Γk` and `vL : Valuation L ΓL`, and `vk.HasExtension vL`.
The value groups are arbitrary linearly ordered commutative groups with zero.
Assume every `k`-automorphism of `L` preserves `vL`. The module proves

```text
characterValuationKernel vk G =
  (characterValuationKernel vL (baseChanged k L G)).comap
    (rationalExtend k L G).
```

No torus or splitting hypothesis is required. All fields retain the arbitrary
universe `u`.

The construction `characterValuationKernelExtend vk vL hinv G` restricts
the actual scalar-extension homomorphism `rationalExtend k L G` to these
two character-valuation kernels. The ascent inclusion supplies its
codomain-membership proof; `characterValuationKernelExtend_coe` identifies
its underlying rational point with the original scalar extension.

`valuation_eq_one_of_norm_eq_one` first proves that `vk (norm k z) = 1`
implies `vL z = 1`. After extending the norm to `L`, the finite Galois norm
formula expresses it as the product of all conjugates. Invariance makes its
valuation the positive-cardinality power of `vL z`; orderedness implies that
this power is one only when `vL z` is one.

For `characterValuationKernel_le_comap`, take an `L`-character `χ` of `G_L`.
The published construction `normCharacter χ` is a `k`-character of `G`, and
`normCharacter_eval` identifies its value with the field norm of the value of
`χ` at the extended point. The preceding valuation lemma gives the required
unit value. The reverse inclusion is the published
`comap_characterValuationKernel_le`, by extending a base-field character.

Provenance: an internal deduction from the actual norm-character construction
in `Langlands.Representation.Plancherel.TorusNormKernel.NormCharacter`, the
finite Galois field-norm formula in Mathlib, and the existing character-kernel
descent inclusion. This helper supplies a scalar-extension comparison used in
the planned proof of the public induced-torus Iwahori statement.
