# Maximal compact subgroups in good position with Iwasawa coverage

Module `Langlands.Global.AdelicGoodPositionIwasawaCompactStatement` states the
proposition `Langlands.Global.GoodPositionIwasawaCompactStatement` and proves
nothing.

## Statement

Let `F` be a number field and `G` a group scheme over `Spec F` with
`IsAffineHom G.X.hom`, `IsAffine G.X.left`, `LocallyOfFiniteType G.X.hom` and
`IsConnectedReductive G`. Let `p : P → G` be a closed immersion of an affine
group scheme `P` with `IsParabolicSubgroup p`. Then there are a standard
parabolic family `𝓕 : StandardParabolicFamily F G` (a maximal split torus, a
generic cocharacter and the standard parabolics `P_J = M_J U_J`, `J ⊆ Δ₀`;
module `Langlands.Global.AdelicLeadingCuspidalComponents`) and a subgroup `K`
of `G(𝔸)` such that

1. `K` is a maximal compact subgroup of `G(𝔸)` (`IsMaximalCompactSubgroup F G K`);
2. `P(𝔸) K = G(𝔸)` (`IsIwasawaCompact p K`);
3. `P₀(𝔸) K = G(𝔸)` for the minimal standard parabolic `P₀ = P_∅` of `𝓕`
   (`IsIwasawaCompact (𝓕.p ⟨∅, _⟩) K`);
4. for every standard index `J`, the inverse image of `K` under the Levi map
   `M_J(𝔸) → G(𝔸)` is a maximal compact subgroup of `M_J(𝔸)`.

## Source and correspondence

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein
series* (1995), registered as `moeglin-waldspurger-1995-spectral-decomposition`,
I.1.4, pp.4–5 (chapter file
`05.1_pp_1_18_Hypotheses_and_general_notation.pdf`): after fixing a minimal
parabolic `P₀` and a Levi subgroup `M₀`, the maximal compact subgroup `K` may be
chosen in good position with respect to `M₀`. Then `G(𝔸) = P(𝔸) K` for every
standard parabolic `P`, and `M(𝔸) ∩ K` is a maximal compact subgroup of `M(𝔸)`.
J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein
series*, J. Amer. Math. Soc. 37 (2024), §2.1, p.190, registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, fixes such a `K`.

The proposition is this existence assertion for a given parabolic `P`. Choose
the minimal parabolic inside `P`, so that `P` is standard; then `P₀ ⊆ P` and
clause 3 gives clause 2. The statement asks for clause 2 directly, so that `P`
need not be one of the standard parabolics of `𝓕` as presented by the family.
Clauses 1, 3 and 4 supply the compact-subgroup hypotheses of
`LeadingCuspidalInjectivityStatement`.

## Scope

Only the number field case is stated. Nothing is asserted about the
relation between `K` and any other given compact subgroup. In particular `K` is
not asserted to be conjugate to a prescribed maximal compact subgroup.
