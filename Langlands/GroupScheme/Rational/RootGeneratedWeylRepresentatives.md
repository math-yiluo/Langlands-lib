# Actual Weyl representatives in root-generated rational subgroups

This internal construction uses the actual root subgroup functors, the actual
normalizer point group and its quotient by the whole-torus centralizer. The
field and universe are arbitrary. The torus is split, its map is monomorphic,
and the ambient group is smooth and affine. Opposite-pair existence remains
an explicit structural premise.

For every actual root `a`, unconditional rational nontriviality supplies a
nonidentity point `x` of its root subgroup. `HasOppositeFactorPairs i` supplies
two points `p₁,p₂` in the opposite root subgroup for which `n = p₁*x*p₂`
normalizes the torus. Thus `n` belongs to the join of the two actual root point
subgroups. The existing opposite-pair results prove that `n` negates `a` and
centralizes its full scheme-theoretic character kernel, including nonsmooth
kernels. `rootGeneratedRepresentative` chooses such an actual normalizer
point for every root.

`RelativeRootReflectionData.ofOppositeFactorPairs` applies the existing
full-kernel-centralization construction to these choices. Its actual integral
coroots pair to two and give the reflection formula on the whole character
lattice. Its representatives retain their membership in the two-root
subgroup join. In particular, every rational-point subgroup containing all
actual root point subgroups contains these representatives. Their reflection
formula also proves that the opposite of each root is an actual root; no
separate root-negation hypothesis is needed for that membership argument.

For any integral reflection data `D`, a supplied `HasRelativeRootSystem i`
identifies the image of the Weyl group of the constructed root pairing with
the whole actual quotient's action range. That same image is the closure of
the actions of `D`'s representatives. Faithfulness of the actual action, also
part of the supplied root-system hypothesis, pulls this equality back to
generation of the whole actual quotient by the representative classes.

If a subgroup `H` contains all representatives of any such generating family,
the range of `subgroupRelativeWeylMap i H` contains every generator and hence
the entire quotient. Specializing to the chosen opposite-root triples proves
surjectivity whenever `H` contains every actual root subgroup. Equivalently,
the previously established surjectivity characterization yields actual
normalizer factorization by `H` and the torus centralizer. No normality
hypothesis on `H` is used.

A second specialization uses the existing chamber-generation theorem:
finitely many actual roots, a generic cocharacter and triviality of the
actual quotient's positive-root stabilizer suffice in place of the full
root-system realization. This is a conditional alternative, not a proof that
the stabilizer is trivial.

The provenance is internal: the implemented argument combines published
rational root-point existence, actual opposite-pair consequences, integral
coroot construction, root-pairing image comparison and elementary subgroup
generation. It invokes no Coxeter-system premise. It does not prove
opposite-pair existence, the full root-system realization, or rational Bruhat
covering, and it does not prove the unconditional
`SimplyConnectedCentralizerProductStatement`.
