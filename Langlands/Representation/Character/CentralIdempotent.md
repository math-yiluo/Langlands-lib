# Characters from central idempotents

For a finite group `G` and a central idempotent `e` in `ℂ[G]`, `CentralIdempotentCharacterStatement` asserts that the function `g ↦ |G| e[g⁻¹]` is the character of a finite-dimensional complex representation of `G`. Here `e[h]` denotes the coefficient of `h` in the group algebra.

The theorem `centralIdempotentCharacter` takes the image of left multiplication by `e` in the left regular representation. Centrality ensures this image is stable under `G`, and idempotence makes multiplication by `e` act there as the identity. Cyclicity of trace identifies the trace of `g` on the image with the trace of left multiplication by `g e` on the whole group algebra. Each diagonal entry of left multiplication by `a` in the group basis equals `a[1]`. Taking `a = g e` yields the formula.

This is the character computation for a regular summand behind the identification of convolution idempotents with scaled characters. The proof applies to idempotents that are sums of primitive ones as well, so the formula supplies a character for each central idempotent obtained from an entire orbit of additive characters. [Boyarchenko and Sabitova, *The orbit method for profinite groups and a p-adic analogue of Brown's theorem*, §1.2, Lemma 1.3](https://arxiv.org/abs/math/0608126v1)
