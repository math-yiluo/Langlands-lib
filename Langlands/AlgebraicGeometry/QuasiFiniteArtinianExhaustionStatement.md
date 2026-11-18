# Artinian detection of a filtered quasi-finite exhaustion

`Langlands.AlgebraicGeometry.QuasiFiniteArtinianExhaustionStatement` is a
derived form of SGA 3, Exposé IX, Lemma 6.2. It concerns an actual quasi-finite
scheme `X` over a noetherian scheme `S`, where quasi-finiteness is encoded by
local finite type, local quasi-finiteness and quasi-compactness. Mathlib's
`LocallyQuasiFinite` does not include local finite type; the latter is explicit
here, as required by the source's convention in footnote 41. The family consists of actual
immersions `Y i → X`. Its nonempty directed preorder has an inclusion morphism
from `Y i` to `Y k` whenever `i ≤ k`, with the required triangle over `X`.
No choice of transition morphisms or additional coherence is part of the
conclusion: immersions are monomorphisms, so those morphisms are unique.

The hypothesis says that, after each map from the spectrum of a commutative
local Artinian ring to `S`, some member pulls back to all of the actual base
change of `X`. The displayed morphism
`pullback.snd (j i) (pullback.fst f b)` is the pullback of the subscheme
immersion along `X ×[S] Spec R → X`. Its being an isomorphism expresses
scheme-theoretic equality, including nilpotent structure. The assertion is
that already one `j i` is an isomorphism over `X`.

The original Lemma 6.2 assumes this equality for the infinitesimal base
neighborhoods `Spec (O_{S,s}/m_s^(n+1))`, for every `s` and `n ≥ 0`. The case
`n = 0` tests the residue fibre. These rings are local Artinian for a
noetherian base, so the all-local-Artinian hypothesis here supplies every
test in the source. This form lets the exhaustion theorem use a
uniform-exponent result over arbitrary local Artinian bases.

The source is registered as `sga3-expose-ix-gille-polo-2009`, SHA256
`7c1e3d5b9d01ad01d0dd7b8b62045d012052e7890fb37adc3e7934ebb5fd6fc3`,
Exposé IX, Lemma 6.2 and its proof, printed pp.53–54 (retained PDF pp.23–24).
Its proof uses noetherian induction on the base, localization at a maximal
point of the remaining closed set, and finite-length control of an ideal
supported on a finite special fibre.

This module states the geometric prerequisite; it supplies no proof.
There is no group structure, flatness or separatedness assumption. In
particular, the subschemes may be immersions that are not closed immersions.
Both the scheme universe and the index universe are arbitrary.
