# Twisted split factorization with Galois inverse-orbit matching

Author: Worker 5268.

This module states, without proof, the core step of Springer's proof of
compactness (Springer 1994, §3.5). The statement is conditional: it assumes
the split fundamental-set theorem `SplitAdelicFundamentalSetStatement` and
the split overlap estimate `SplitSiegelOverlapStatement` as hypotheses. From
these, together with a Galois twisting of a split Borel pair over a splitting
field, it derives a dichotomy for the points of `G(𝔸_F)¹`. Each such point,
after scalar extension, has a Siegel factorization over the splitting field.
Either all simple-root norms of its torus factor are larger than a fixed
threshold, or the inverse-orbit matching condition used for Galois descent of
parabolic subgroups holds. No anisotropy or centrality hypothesis is made.

## Notation

`F` is a number field and `L` a finite Galois extension of `F`. `G` is an
affine, locally finite-type group scheme over `F`, and
`G_L = AffineWeil.unitBaseChange F L G`. Inside `G_L` we fix a commutative
group scheme `T` over `L` with a homomorphism `i : T → G_L` and a cocharacter
`ν`. Write:

- `Δ = simpleRelativeRoots i ν`;
- `P_H = Standard.parabolicScheme i ν H` with inclusion
  `j_H = Standard.parabolicHom i ν H`, for `H ⊆ Δ`;
- `|β(t)| = PositiveRealTorus.normCharacter L T β t` for a character `β` and
  `t ∈ T(𝔸_L)`;
- `G(𝔸_F)¹ = normOneSubgroup F G`, `G_L(𝔸_L)¹ = normOneSubgroup L G_L`, and
  `P_∅(𝔸_L)¹` for the norm-one subgroup of `P_∅`, defined by all characters
  of `P_∅`.

`rationalSection F L G q` is the image in `G_L(𝔸_L)` of a rational point `q`
of `G_L`, given as a section over `Spec L`. It comes from the module
`AdelicGaloisBorelTwisting`, as do `HasGaloisBorelTwisting` and
`radicalGaloisHom`-based Galois transport. `innerIso q⁻¹` is conjugation
`x ↦ q⁻¹ x q`.

## Definitions

**`HasTwistedOverlapMatching F L G T i ν`.** There are a compact set
`C ⊆ G_L(𝔸_L)` and units `c, d` of `ℝ≥0` with the following property. For every
`g ∈ G(𝔸_F)¹` there are `x ∈ C`, `t ∈ T(𝔸_L)`, `p ∈ P_∅(𝔸_L)¹` and a rational
point `q` of `G_L` such that:

1. `scalarExtensionNormOneMap F L G g = x · i(t) · j_∅(p) · rationalSection q`
   in `G_L(𝔸_L)`;
2. `i(t) ∈ G_L(𝔸_L)¹`;
3. `|β(t)| ≤ c` for every `β ∈ Δ`;
4. for every `α ∈ Δ` with `|α(t)| ≤ d` there is a family
   `J : Gal(L/F) → Set (characterLattice T)` with `J σ ⊆ Δ` for all `σ` and
   `J 1 = Δ \ {α}`, satisfying the inverse-orbit matching condition: for
   every `σ`,
   `SubgroupFunctor.range (radicalGaloisHom (j_(J σ⁻¹) ≫ (innerIso q⁻¹).hom) σ)`
   equals
   `SubgroupFunctor.range (j_(J 1) ≫ (innerIso q⁻¹).hom)`.

The thresholds `c` and `d` are chosen before `g`, so they are uniform. In
words, condition 4 says that the `σ`-translate of `Int(q⁻¹) P_(J σ⁻¹)` is
`Int(q⁻¹) P_(J 1)`. This is precisely the premise `hmatch` of
`IsMaximalSplitTorus.eq_simpleRelativeRoots_of_inverse_orbit_matching`
(module `Langlands.GroupScheme.Descent.GaloisParabolicOrbitMatching`), with
`e = innerIso q⁻¹`. As a consequence that this module does not state, the
intersection of the family is Galois-invariant by
`galoisTransport_intersection_eq_of_inverse_orbit_matching`. It contains
`Int(q⁻¹) P_∅` and lies in the proper parabolic `Int(q⁻¹) P_(Δ \ {α})`.

## The statement

`SplitGaloisOverlapMatchingStatement` asserts, in universe `u`: assume
`SplitAdelicFundamentalSetStatement` and `SplitSiegelOverlapStatement`. Let
`F` be a number field and `G` an affine, locally finite-type, connected
reductive group scheme over `F`. Let `D : FiniteGaloisSplitMaximalModel G`
have splitting field `L = D.carrier`, split maximal torus `D.torus` and
inclusion `D.inclusion`. Let `ν` be a generic cocharacter of `D.torus` such
that `HasGaloisBorelTwisting F L G D.torus D.inclusion ν` holds. Then
`HasTwistedOverlapMatching F L G D.torus D.inclusion ν` holds.

## Provenance

This is an internal interface. It isolates the first half of the proof of
(C) in T. A. Springer, *Reduction theory over global fields* (1994), §3.5,
printed p.215. There Springer writes `g = xtuγ` over the splitting field `l`
using (F) over `l`. He rewrites `s(xtuγ) = xtuγ` with the representative
`ŵ_s ∈ G(l)` of §3.4, which satisfies `s.B = Int(ŵ_s) B`, as
`((s.x) ŵ_s)(w_s⁻¹(s.t)) u' = xtu (γ (s.γ)⁻¹ ŵ_s)`. Proposition 2.6 then
gives a constant `d` such that `|α(t)| ≤ d` implies
`γ (s.γ)⁻¹ ŵ_s ∈ P̃(α)` for all `s`. The twisting representative `ŵ_s` on
the right is essential: it gives
`s.Int(γ⁻¹) P̃_(ι(s)⁻¹.α) = Int((s.γ)⁻¹ ŵ_s) P̃(α) = Int(γ⁻¹) P̃(α)`, so the
family `Int(γ⁻¹) P̃_(ι(s)⁻¹.α)` is Galois-stable. In the notation of this
module, `q` plays the role of `γ` and the twisting point `m_σ` of
`HasGaloisBorelTwisting` plays the role of `ŵ_s`. The membership used in the
intended proof below, `m_σ⁻¹ σ(q) q⁻¹ ∈ P_(Δ \ {α})(L)`, is the inverse of
Springer's `γ (s.γ)⁻¹ ŵ_s ∈ P̃(α)`. Springer then descends the intersection
to `k` and uses anisotropy for a contradiction. This statement stops before
the descent and the contradiction. It differs from the printed text as
follows.

1. **Hypotheses as premises.** (F) for split groups and Proposition 2.6 for
   split groups are the published statements `SplitAdelicFundamentalSetStatement`
   and `SplitSiegelOverlapStatement`. They appear as premises, so this
   proposition is the implication that Springer's argument proves. The
   Galois data enter through `HasGaloisBorelTwisting`, the published form of
   Springer's §3.4 twisting `s.P_H = Int(ŵ_s) P_(ι(s).H)`.
2. **Right action.** Rational points act on the right, as in
   `HasRightAdelicFundamentalSet`. The Galois-stable family appears through
   its inverse-orbit matching condition. The Library's descent module
   consumes exactly this condition.
3. **Uniform threshold.** One threshold `d` serves all simple roots. Since
   `Δ` is finite, the minimum of the per-root thresholds of Proposition 2.6
   works.
4. **Indexing.** With the based action `a` of `HasGaloisBorelTwisting`, the
   intended family is `J τ = Δ \ {a_τ α}`. The statement only asserts that
   some family with `J 1 = Δ \ {α}` exists.

## Intended proof

Apply (F) over `L` to the inverse of the scalar extension, or directly, to
get `x · i(t) · j_∅(p) · q`. Each Galois twist `φ_σ` fixes the scalar
extension of `g`. Its conditions rewrite `φ_σ` of the factorization as a
second factorization `(φ_σ(x) M_σ) · i(t') · j_∅(p') · (m_σ⁻¹ σ(q))`. Here
`M_σ` is the image of `m_σ`, and `t'` satisfies the same simple-root bounds.
The compact set `C ∪ ⋃_σ φ_σ(C) M_σ` covers both. Proposition 2.6 then gives
`m_σ⁻¹ σ(q) q⁻¹ ∈ P_(Δ \ {α})(L)`. Galois transport of an inner conjugate is
the inner conjugate by the Galois conjugate point, and conjugating a subgroup
by one of its own points does not change it. Together with the twisting
identity for maximal parabolics, these give the matching condition for
`J τ = Δ \ {a_τ α}`.

## Scope

This module contains only definitions and the proposition. It proves
nothing. In particular it does not prove `SplitAdelicFundamentalSetStatement`,
`SplitSiegelOverlapStatement` or `GaloisBorelTwistingStatement`, nor the
compactness theorem itself.
