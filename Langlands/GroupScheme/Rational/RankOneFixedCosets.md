# Rational normalizer representatives for descended rank-one fixed cosets

This internal unit constructs rational normalizer representatives for fixed
cosets in the descended-conjugation setting. It works over every field
`k : Type u`, with all scheme tests. Let `i : T.toGrp → G` be an actual maximal
split torus of a smooth affine group scheme. Let `a` be a nonzero character of
`T`, and let `e` be an actual automorphic action of `Gm` on `G` whose restriction
along `a` is conjugation by `i`. Choose a cocharacter `ν` with
`0 < latticePairing T a ν`, and put `χ = ν ≫ i`,
`P = Dynamic.parabolic χ` and `U = Dynamic.unipotent χ`.

Supply a scheme over `k` called `Q` and a morphism `q : G.X → Q` satisfying
the exact fiber condition
`x ≫ q = y ≫ q ↔ x⁻¹ * y ∈ P(V)` for every test scheme `V` and its points
`x,y` in `G(V)`. For a rational point `g`, assume that its coset is fixed by
`χ` on every test:
`q(χ(z) * g_V) = q(g_V)` for every `V` and `z ∈ Gm(V)`.
Here `g_V` is the constant point obtained from `g`.

`RelativeRoot.normalizerRepresentativeOfFixedCoset` constructs an actual
rational point `n` in `normalizerPoints i`, together with proofs of
`n ≫ q = g ≫ q` and `g⁻¹ * n ∈ U(k)`. Its type is the subtype carrying this
point and these two properties. It makes a classical choice of a unipotent
adjustment. There is no connectedness, reductivity, perfectness or
characteristic hypothesis.

## Implemented proof

`RelativeRoot.exists_unipotent_normalizer_adjustment_of_range_le` first
handles a rational point `g` whose conjugated torus
`i ≫ (G.innerIso g⁻¹).hom` has all-test range contained in `P`.
The local conjugacy theorem in `RankOneParabolicTorusConjugacy` provides
`u ∈ U(k)` and an invertible homomorphism `f` with
`(f ≫ i) ≫ (G.innerIso u).hom = i ≫ (G.innerIso g⁻¹).hom`.
The actual inner-automorphism composition identities give
`i ≫ (G.innerIso (g*u)).hom = inv f ≫ i`.
The inverse of `f` determines the source automorphism required by the
definition of `normalizerPoints i`. Thus `g*u` normalizes `i`.

`RelativeRoot.torus_fixed_coset_of_cocharacter_fixed` proves that the supplied
fixed-coset condition implies `q(i(t)*g_V) = q(g_V)` for every test and
`t ∈ T(V)`. This intermediate theorem requires neither affineness nor
smoothness of `G`, and requires neither maximality of `i` nor a separate
nonvanishing hypothesis on `a`. It retains the descended action, positive
pairing and exact all-test fiber condition. The image of `T` centralizes `χ`,
so it lies in `P`; hence right multiplication by its points preserves `q`.
The descended-conjugation equation then gives
`q(e(a(t),x)) = q(i(t)*x)` for arbitrary `x`.

Set `N = latticePairing T a ν`. The composite `ν ≫ a` is the power
homomorphism of `Gm` with exponent `N`. Since `N > 0`, this is a nonzero
character and is faithfully flat, quasi-compact and surjective by
`characterFpqc`. Fixedness under `χ` therefore implies
`q(e(z^N,g_V)) = q(g_V)`. Locally lift `a(t)` along that power homomorphism,
use naturality of the actual action and of the constant point, and descend
equality by `AutomorphicAction.hom_ext_of_local_quotient_lift`. This proves
whole-torus fixedness without assuming that power maps are surjective on
rational points. The argument also applies when the characteristic divides
`N`.

For the final construction, the canonical affine representative of `P`
and `range_conjugate_le_of_fixed_coset` convert whole-torus fixedness into
the conjugated-range hypothesis of the first theorem. Choose its point `u`
and set `n = g*u`. Membership `u ∈ U ⊆ P` and the exact fiber condition give
`n ≫ q = g ≫ q`; cancellation gives `g⁻¹*n = u ∈ U(k)`.

## Provenance and scope

The argument is derived internally from the actual local parabolic conjugacy
theorem, the published all-test fixed-coset range inclusion, character power
maps and fpqc equality descent. It does not translate a further literature
assertion or call general rational Bruhat, a Tits-system result or the host
rank-one factorization theorem.

The quotient morphism and the rational lift `g` of the fixed coset are supplied.
The unit constructs neither a proper flag quotient, an orbit limit or its
rational lift, a nontrivial Weyl element, nor a two-cell covering. The host
`RootRankOneFactorizationStatement` remains a separate proof obligation.
