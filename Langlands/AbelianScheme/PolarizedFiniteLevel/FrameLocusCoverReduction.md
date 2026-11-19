# Covering by projective frame loci from Lefschetz's theorem

This unit derives the published statement `FrameLocusCoverStatement` from two
other published statements:

- `CubicFieldEmbeddingStatement`: Lefschetz's embedding theorem for the cubic
  bundle over a field;
- `FrameLocusBaseChangeStatement`: over a locally noetherian base, the frame
  locus of a pulled-back datum is the preimage of the original frame locus.

The bound produced is

`N = (cubicProjectiveDimension g d + 1) * (6^g * d * g!) + 1`,

which equals `(6^g d) * (6^g d g!) + 1` because
`cubicProjectiveDimension g d + 1 = 6^g d` for positive `d`. The Lean proof does
not need this identity.

## Declarations

- `frameSize_lt`: for natural numbers `g, d, n, m` with `0 < g`, if
  `(m + 1) * (6^g * d * g!) < n`, then

  `(m + 1) * (6^g * d * g! * n^(2g-2)) < n^(2g)`.

- `frameLocusCover_of_cubicFieldEmbedding` (proved definition): from proofs
  `hL : CubicFieldEmbeddingStatement` and `hB : FrameLocusBaseChangeStatement`
  it produces a proof of `FrameLocusCoverStatement`, with the bound `N` above.
  It is a `def` whose type is the proposition `FrameLocusCoverStatement`, so it
  records an implication between the three statements and proves none of them
  by itself.

## Proofs

`frameSize_lt`: write `C = (m + 1) * (6^g d g!)`. Since `C < n`, also
`0 < n` and `C < n ≤ n^2`. Since `g` is positive, `n^(2g) = n^2 * n^(2g-2)`.
The left side equals `C * n^(2g-2)`, which is less than `n^2 * n^(2g-2)`
because `n^(2g-2)` is positive.

`frameLocusCover_of_cubicFieldEmbedding`: fix `P`, `g > 0`, `d > 0` and take
`N` as above. Let `n ≥ N`, let `S` be locally noetherian with `n` a unit in
`Γ(S, ⊤)`, let `a` be a datum over `S` and let `x` be a point of `S`.

1. Let `κ` be the residue field of `x` and `K` its algebraic closure (Mathlib's
   `AlgebraicClosure`). Let `f : Spec K → S` be `Spec` of the inclusion
   `κ → K` followed by `S.fromSpecResidueField x`.
2. `n` is a unit in `K`: apply the ring map `f.appTop` and then
   `Scheme.ΓSpecIso`. Hence `(n : K) ≠ 0`. Also `n > C`, so `n > 0`, and
   `frameSize_lt` (with `m = cubicProjectiveDimension g d`) gives the size
   hypothesis of the field theorem.
3. The field theorem `Datum.exists_frameLocus_eq_top` (from the unit
   `FrameLocusField`), applied to the pulled-back datum `a.pullback f` and to
   `hL`, gives `ρ` with `(a.pullback f).frameLocus ρ = ⊤`.
4. The closed point of `Spec K` therefore lies in the frame locus of
   `a.pullback f`. By `hB` this frame locus is `f⁻¹ (a.frameLocus ρ)`. Every
   point of `Spec κ(x)` maps to `x` under `S.fromSpecResidueField x`
   (Mathlib's `Scheme.fromSpecResidueField_apply`). So `f` maps the closed
   point to `x`, and `x ∈ a.frameLocus ρ`.

## Provenance

The reduction follows the large-level argument in Mumford, Fogarty and Kirwan,
*Geometric Invariant Theory*, third edition (1994). Proposition 7.7 (printed
p.138 / one-based PDF p.151) bounds the number of `n`-torsion points on a
hyperplane section of a projective embedding by a multiple of `n^(2g-2)`.
Its proof shows that fewer than `n^(2g)/(m+1)` of the `n^(2g)` torsion points
lie on any hyperplane, over an algebraically closed field. Corollary 7.8
(printed p.139 / one-based PDF p.152) applies this to the universal family
over the Hilbert scheme. Here the same counting is used in
`FrameLocusField` to choose a frame of torsion points over an algebraically
closed field. Two steps here are internal: reducing from a point of `S` to its
geometric point `Spec K → S` through `FrameLocusBaseChangeStatement`, and the
explicit bound `N`.
