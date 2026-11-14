# Separation of actual root-partner character values over infinite fields

Worker 244. This internal unit proves an actual-root character separation
prerequisite for the unitary Heisenberg construction. It concerns values of
the actual descended characters on all original rational torus points.
The main theorem requires an infinite base field.

Work over fields `k,L : Type u` with an algebra `k → L`, a commutative
group scheme `T`, an affine group scheme `G`, and a homomorphism
`j : T.toGrp → G`. All roots are roots of this same homomorphism after
base change to `L`. `IsRootPartner.smul` says that applying the same
Galois automorphism to two actual partners preserves the partner
relation: conjugate the automorphism moving one partner to the other,
and use additivity of the Galois action on the character lattice.

For `IsRootPartner.eq_or_eq_of_add_eq`, assume also that `G` is locally
of finite type, `T_L` is split, `j_L` is a closed immersion, a finite-indexed
root datum of `j_L` is supplied, the Galois automorphism group has a
`Fintype` instance, and every actual root has a nonzero Galois orbit
sum. If `β,β'` are partners and `γ,δ` belong to the orbit of `β`,
then `β + β' = γ + δ` forces equality of the unordered pairs.
The proof transfers the actual roots to root-datum indices. The sum
of the partners pairs to one with the coroot of `β`. If neither `γ`
nor `δ` equals `β`, the published orbit-pairing bound makes both
pairings nonpositive, which contradicts their sum being one.
The two cases in which one root equals `β` follow by cancellation.
No separate reducedness hypothesis is used.

Now assume `k` is infinite and `L/k` is finite Galois.
`character_ext_of_rational_values` says that two characters of the
split base change `T_L` are equal if their values agree at the base
changes of every original rational point of `T`. It converts to
`rationalCharacters`, applies the published
`RationalCharacterSeparation.rationalCharacters_ext_of_isSplitTorus`,
and uses `rationalCharacterEval_baseChangedCharacter`.

For the separation statement, let `β,μ` be actual roots and put
`E = rootOrbitField k L j β` and `E₀ = rootOrbitField k L j μ`.
Retain the supplied algebra `E₀ → E`, its compatible scalar tower into
`L`, and the separable quadratic extension instances on `E/E₀`.
These are the same inclusion-compatible field hypotheses used in
`RootPartnerFields.conjugation_apply`. Assume `T` is affine so that
the actual descended character `rootOrbitCharacter k L j β` is
available.

`HasSeparatingCharacterValues` is the Prop-valued condition that,
for any three `k`-embeddings `π,τ,ρ : E → L`, equality
`τ(c)ρ(c) = π(c)π(bar(c))` for every value `c` of that descended
character at an extended original rational point forces either
`(τ,ρ) = (π,π ∘ bar)` or `(τ,ρ) = (π ∘ bar,π)`. Here `bar` is
the quadratic conjugation of `E/E₀`, restricted to a `k`-algebra
homomorphism, and the values range over all rational points, without
selecting a generating subset.

`hasSeparatingCharacterValues` proves this condition under the
root-datum, splitness, closed-immersion, local-finite-type and nonzero
orbit-sum hypotheses above, together with an actual partner `β'` of
`β` and `μ = β + β'`. Extend `π` to an automorphism `σ` of `L/k`
and choose `s` moving `β` to `β'`. The published conjugation formula
identifies `π ∘ bar` with the restriction of `σs`. The
orbit-embedding correspondence therefore associates these two
embeddings with `σβ` and `σβ'`, which are partners. The product
equality on character values becomes equality of values of two
sums of split characters, using
`rationalCharacterEval_rootOrbitCharacter`,
`rootOrbitEmbeddingEquiv_characterValue`, and multiplicativity of
character evaluation under addition. Character extensionality gives
equality of the sums themselves. The unordered-decomposition lemma
then identifies the two pairs of roots, and injectivity of the
orbit-embedding correspondence identifies the embeddings.

The provenance is internal composition of the named published
root-datum pairing, Galois-orbit, fixed-field, character-descent and
rational-character separation results. There is no restriction on
characteristic. The infinite-field hypothesis is retained; no
finite-field separation theorem is asserted. This unit does not
construct quotient or doubled-root coordinates, a unitary
homomorphism, a coroot map, or an affine lift.
