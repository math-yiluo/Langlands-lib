# The inducing layer in the whole opposite Jacquet module

Workers 526, 359, 430 and 1114.

`Langlands.Exponents.WholeInductionLeadingRealBlockStatement` is an internal
proposition definition. This file supplies no proof.

Worker 526 implemented this statement and source audit. Worker 359 contributed
the full-center, open-kernel formulation and size-weighted coordinates.
Worker 430 contributed the actual retraction and projector formulation used
to control every later fine Hom map. Worker 1114 rechecked the statement
against the imported files and sources and revised this explanation.

## Statement

Fix a prime, an actual p-adic field `F`, its realization `T`, a positive
ambient rank `n`, and a block shape `B`. The coarse representation `π` is
arbitrary, subject to irreducibility and the existing analytic predicate
`RelativeRegularComparison.IsLeviTempered T B π`. For any strictly decreasing
coarse vector `t`, the statement uses the actual representations

- `πt = Rep.of (T.leviRealPowerTwist B t π.ρ)`;
- `X = CuspidalJacquetMultiplicity.induced T B πt`;
- `E = CuspidalJacquetMultiplicity.oppositeJacquet T B X`.

The conclusion constructs actual `B.Levi F.Carrier` intertwiners
`i : πt → E` and `r : E → πt`. Their composite `r ∘ i` is the identity on
every vector of `πt`. The other composite `i ∘ r` fixes every vector of
`generalizedCentralCharacterSpace E.ρ χ`, for every full-center character
`χ` with open kernel whose block-scalar restriction has real part
`fun k => (B.size k : ℝ) * t k`. The same maps work simultaneously for all
these characters. The real-part condition is exactly `T.IsRealPartOf`, with
restriction along `B.blockScalarToCenter F.Carrier`. The open-kernel
condition uses the topology on the center induced by `T.topology`.

These are uniform generalized central-character spaces from `Exponents.Central`,
including all their finite nilpotent exponents. The statement does not replace
them by scalar eigenspaces or by composition-factor counts. It neither asserts
nor requires that the entire Jacquet representation be semisimple.

The grouped real central block `PadicField.TopologicalData.realCentralBlock`
(module `Langlands.Representation.Exponents.RealCentralBlock`) is already in
the Library, but this statement does not import or use it. That block is
defined as the supremum of exactly the generalized spaces quantified here, and
`i ∘ r` is linear. So, as a remark not stated in Lean, the per-character
conclusion is equivalent to `i ∘ r` fixing every vector of
`T.realCentralBlock B E.ρ (fun k => (B.size k : ℝ) * t k)`.

## Universes and premises

The coefficient field is `ℂ`. The field universe `uF` and coarse-carrier
universe `uV` are independent. The twist `πt` keeps the original coarse
carrier in `uV`. The actual induction `X` and its opposite Jacquet module `E`
live in `max uF uV`, as the existing constructions dictate. No carrier
equivalence or universe equality is supplied as an assumption. There are no
fine or middle data, support hypotheses, quotient representations,
finite-dimensionality assumptions, finite-generation or finite-length
assumptions, supplied filtrations, exponent exclusions, or retraction maps
among the premises. The one-block case is included, since `StrictAnti` is
then vacuous.

The actual upper induction keeps right translation and positive-half-modulus
covariance. The opposite Jacquet representation is the existing bundled
construction with its fixed normalization (the coinvariant action is twisted
by `δ_P^{1/2}`). The real coordinate contains the block size because
evaluating `|det|^t` on a scalar matrix of size `d` gives the scalar absolute
value to the power `d*t`. The residue-normalized absolute value and the
existing order of the blocks are unchanged.

## Provenance

The provenance is internal. Renard, *Représentations des groupes réductifs
p-adiques*, corrected French 2026 version, VII.3.1–VII.3.4, printed
pp.232–236 (PDF pp.238–242), orders `P\G/Q` by the Bruhat order and
filters `r^G_Q ∘ i^G_P` by support (VII.3.2). The identity double coset `1̄`
has layer `F^{<1̄}/F^{≤1̄} ≅ Id`. VII.3.3 defines `PQ`-regularity through
comaximal annihilator ideals `I_σ + I^{PQ}_σ = ℂ[A_M]` in the group algebra
of the split component `A_M`. VII.3.4 obtains an actual retraction `r_σ` of
the identity-layer inclusion `i_σ` by the action of an element
`ε_σ ∈ I^{PQ}_σ` with `1 ∈ ε_σ + I_σ`; hence `r_σ` commutes with `M`.
VII.4.1, printed pp.241–242 (PDF pp.247–248), separates the real exponents
of the nonidentity layers from the inducing real exponent for a tempered
input and a strictly positive parameter. In particular, its formulas
(VII.4.1.1) and (VII.4.1.2) combine the tempered cone bound with strict Weyl
displacement. These passages motivate the retraction and the real-part test.
They do not literally state this Lean proposition. In particular, Renard does
not state that `i_σ ∘ r_σ` fixes whole generalized central-character spaces.

Ban–Jantzen, “Jacquet modules and the Langlands classification” (2008),
Proposition 5.3, printed pp.647–648 (published PDF pp.11–12), separately
isolates the inducing simple subquotient with its real central exponent,
with multiplicity one. It works with `L(P,ν,τ)` for `ν` in the negative
chamber and the usual Jacquet module `r_{M,G}`. A multiplicity-one count by
itself does not prove the displayed identities on actual generalized spaces.

The relevant 2010 Renard errata were also read at PDF pp.16–18 (printed
pp.17–18). They correct the filtration-image notation (p.267), the arrow of
the retraction `r_σ`, which is surjective so that `↪` becomes `→` (p.270,
l.15), modular-character reasoning (p.275), the Weyl pairings and scalar
products (pp.277–278), and later opposite-Jacquet indices (pp.279–280).
Those page locators refer to the 2010 edition. The corrected 2026 text
above governs this proposal; no unverified equality between the two
editions is used.

## Convention adapter required by a proof

A proof must translate Renard's conventions to the Lean constructions.

- Take `P` the upper block parabolic with Levi `B.Levi F.Carrier`, and
  `Q = P̄`. Then `X` corresponds to `i^G_P(πt)` and `E` to `r^G_{P̄}(X)`,
  both normalized. Each normalization must be matched to the Lean
  half-modulus conventions.
- By Renard V.3.20, printed pp.115–116 (PDF pp.121–122), `𝔞*_ℂ → X(M)`
  sends `χ ⊗ s` to `g ↦ |χ(g)|_F^s`, and `ℜ(χ) = ln|χ|`. So
  `T.leviRealPowerTwist B t` has real part `t` in determinant coordinates.
  The Lean residue-normalized absolute value must be matched with `|·|_F`.
- By Renard V.3.15, printed p.113 (PDF p.119), the positive chamber of `P`
  is given by `⟨μ, β̌⟩ > 0` for `β ∈ Δ(P)`. For `μ = Σ t_k det_k` these
  pairings are `t_k - t_{k+1}`, so the positive chamber is `StrictAnti t`.
- The split component `A_M` consists of the block scalars. The full center of
  `B.Levi F.Carrier` is identified with them by
  `B.blockScalarCenterEquiv F.Carrier`, built from
  `B.blockScalarToCenter_bijective F.Carrier`. Restricting `|det_k|^{t_k}` to
  the block scalars gives the coordinate `(B.size k : ℝ) * t k`.
- For `Q = P̄` the identity coset is the largest one (VII.3.1). The cell
  `P P̄` is open and dense. A locally constant function supported off
  `P P̄` is therefore zero, so `F^{≤1̄} = 0`. The identity layer `F^{<1̄} ≅ πt`
  is then a subrepresentation of `E` itself, which is the source of `i`.

## Proof obligations

A later proof must construct the actual identity layer in `E` for these
Lean constructions. It must derive the tempered exponent cone bound from the
analytic predicate `IsLeviTempered` (a Casselman-criterion step). It must
also prove the strict exclusion of the real part `size * t` from the
nonidentity layers, in the required normalization. Finiteness facts, such as
finite length of the actual Jacquet module, must be proved for these actual
representations; they are not premises. The final step is the derivation
that `i ∘ r` fixes every qualifying generalized space, retaining nilpotents.
For example, a vector in such a space would map to zero in the quotient by
the identity layer and so lie in that layer, where `ε` acts as the identity.
Renard does not state this step.

Registered originals:

- `renard-2026-representations-groupes-reductifs-padiques`, SHA-256
  `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`;
- `ban-jantzen-2008-jacquet-langlands`, SHA-256
  `bb4a03020067de5fdefc71e1acbecad13d1d7eaee9c50ab741256ed7244196f6`;
- `renard-2010-corrections-complements`, SHA-256
  `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`.

## Scope

This statement supplies no comparison for an outer quotient `J`, no
restriction-of-surjections theorem for generalized blocks, no fine Hom
factorization, and no relative cosocle or classification conclusion. A proof
must avoid the false unrestricted wording of Silberger's Lemma 5.3 and
the downstream results that consume the relative Hom comparison.
