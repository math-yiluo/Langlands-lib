# Springer's Siegel-set overlap estimate for split groups

Author: Worker 5268.

This module states, without proof, the split-group case of Springer's
Proposition 2.6. It gives the overlap estimate in the right-action form
produced by `HasRightAdelicFundamentalSet`. The statement is the input
needed to bound simple roots from both sides after a finite Galois
scalar extension (Springer, §3.5).

## The statement

`SplitSiegelOverlapStatement` quantifies in universe `u` over:

- every number field `F`;
- every affine, locally finite-type connected reductive group scheme `G`
  over `F`;
- every torus embedding `i : T → G` and cocharacter `ν : cocharacterLattice T`
  such that `i` is a maximal split torus (`IsMaximalSplitTorus i`), is a
  maximal torus (`IsMaximalTorus i`; this is the split-group hypothesis),
  and `ν` is generic (`IsGenericCocharacter i ν`).

Write `Δ = simpleRelativeRoots i ν` for the simple roots and
`P = Standard.parabolicScheme i ν ∅` for the canonical minimal parabolic,
a Borel subgroup here. Let `P_(Δ \ {α}) = Standard.parabolicScheme i ν (Δ \ {α})`
be the standard maximal parabolic attached to `α`. For `β` a character and
`s ∈ T(𝔸_F)`, `|β(s)|` means `PositiveRealTorus.normCharacter F T β s`, the
normalized full idele norm of `β(s)`.

The statement asserts the following. Let `C ⊆ G(𝔸_F)` be compact and
`c : ℝ≥0ˣ`. Then for every `α ∈ Δ` there is `d : ℝ≥0ˣ` with this property.
Suppose that

`x · i(s) · ι_P(p) · rational(q) = x' · i(s') · ι_P(p') · rational(q')`,

where:

- `x, x' ∈ C`;
- `s, s' ∈ T(𝔸_F)` with `i(s), i(s') ∈ G(𝔸_F)¹`;
- `|β(s)| ≤ c` and `|β(s')| ≤ c` for every `β ∈ Δ`;
- `p, p'` lie in the norm-one subgroup of `P(𝔸_F)`, defined by all
  characters of `P`;
- `q, q' ∈ G(F)`;
- `|α(s)| ≤ d`.

Then `q' q⁻¹` is the image of an `F`-rational point of `P_(Δ \ {α})` under the
inclusion `Standard.parabolicHom i ν (Δ \ {α})`.

The compact set `C` is arbitrary. It need not lie in `G(𝔸_F)¹`. The
Galois step of Springer §3.5 compares a factorization with its Galois
conjugates and needs compact sets of the form `σ(C) · n_σ`.
The threshold `d` depends on `α`, `C` and `c`, but not on the
two factorizations or on `q, q'`.

## Provenance

This is a derived formulation of T. A. Springer, *Reduction theory over
global fields* (1994), §2.5–2.6, Proposition 2.6, printed p.213.
Springer considers `g = x s y = x' s' y' γ` with:

- `x ∈ K` and `x' ∈ K'` compact;
- `s, s' ∈ S(𝔸) ∩ G(𝔸)¹` in the sets `S(c)` and `S(c')`, given by upper
  bounds on the simple roots;
- `y, y' ∈ P(𝔸)¹` and `γ ∈ G(k)`.

He assumes that `C(L)` is compact, and concludes `γ ∈ P(α)(k)` if the
values `|α(s)|` are not bounded away from zero.

The formulation here differs from the printed one in four ways.

1. **Split case.** The minimal Levi is the maximal torus `T`. Springer's
   hypothesis that `C(L)` is compact then becomes the published torus case,
   and the statement is unconditional.
2. **One compact set and one bound.** A single compact set `C` and a single
   bound `c` replace `K, K'` and `c, c'`. Taking unions and maxima shows that
   this loses nothing.
3. **Uniform threshold.** The threshold is uniform in `γ = q' q⁻¹`, and the
   statement is the contrapositive "small `|α(s)|` forces `γ ∈ P(α)(F)`".
   Springer's proof gives such a threshold. For each Weyl element `w` with
   `w ∉ W(α)`, it bounds `|α(s)|` below by a constant that depends only on
   `w`. There are finitely many such `w`.
4. **Rational factors on the right.** The rational factor is written as
   `rational(q)` on both sides. Dividing through gives Springer's form with
   `γ = q' q⁻¹`.

The norm-one condition on the parabolic factors uses `P`'s own characters,
exactly as in `HasRightAdelicFundamentalSet`. In the split case this is
Springer's `P(𝔸)¹`.

## Correction to the printed proof

The printed proof (p.213) uses the claim in §2.5 that the weight `χ_β` of a
representation adapted to `P(β)` is a positive multiple of `β`. This claim is
false in higher rank; see the Library errata note
`notes/errata/springer-1994-reduction-global-fields.md`.
The statement itself is not affected. Here is a corrected route, given as
guidance for a proof; it is not a verified argument.

- **Weights.** In `X*(T) ⊗ ℚ` one has `χ_β = m_β ϖ_β + η_β`. Here `m_β` is a
  positive rational number and `ϖ_β` is the fundamental weight in the `ℚ`-span
  of the roots. The term `η_β` lies in the image of `X*(G) ⊗ ℚ` under
  restriction to `T`. So `η_β` is a rational linear combination of algebraic
  characters of `G`; in general it is not itself an algebraic character. For
  `GL₂` with the upper triangular Borel, `χ = e₁`, `ϖ = (e₁ − e₂)/2` and
  `η = det/2`. Clearing denominators gives an identity of actual characters, as
  in Godement §6B (printed p.209): there are a positive integer `n` and an
  algebraic character `η'_β` of `G` such that `n m_β ϖ_β` is an integral
  combination of simple roots and `n χ_β = n m_β ϖ_β + η'_β` in `X*(T)`. For
  `GL₂` this is `2χ = α + det`. Since `i(s), i(s') ∈ G(𝔸)¹`, the norm of
  `η'_β` is `1` at `s` and at `s'`. Hence `|χ_β(s)|ⁿ = |(n m_β ϖ_β)(s)|`, and
  similarly for `s'`. Thus the adapted weights are controlled by positive
  multiples of the fundamental weights, which are products of simple roots.
- **Height inequalities.** Write `γ` in a Bruhat cell `U(F) ẇ P(F)`. The height
  argument applied to `γ` gives a one-sided inequality between the
  fundamental-weight coordinates of `s` and of `w`-twisted `s'`. The same
  argument applied to `γ⁻¹`, whose cell is that of `w⁻¹`, with the roles of
  the two factorizations exchanged, gives the symmetric inequality.
- **Conclusion.** Pass to logarithmic coordinates and use the upper root bounds
  on both `s` and `s'`. The two inequalities show that `|ϖ_β(s)/ϖ_β(s')|` is
  bounded above and below, and that `|(ϖ_α − w ϖ_α)(s)|` is bounded below up
  to the twist convention. If `w ∉ W(α)`, the `α`-coefficient of
  `ϖ_α − w ϖ_α` is strictly positive. This gives a lower bound for `|α(s)|`.
  Hence small `|α(s)|` forces `w ∈ W(α)`, and so `γ ∈ P(α)(F)`.

A proof of this statement may follow another route. It must supply the
actual scheme-level Bruhat decomposition, the adapted representations and
the height comparisons.

## Scope

This module contains only the proposition. It proves nothing, and it adds
no hypotheses beyond the split and genericity conditions listed above.
