# Matching the terms of a twisted and an ordinary finite geometric expansion

Module `Langlands.TraceFormula.BaseChangeTermPairing`, namespace `Langlands.TraceFormula`.
It imports `Langlands.TraceFormula.SingleOrbitGeometricTrace`, which defines
`TwistedGeometricMeasures Γ θ δ μ` (a right-invariant centralizer measure, finite on compacts
and positive on nonempty open sets, an orbital quotient measure compatible with `μ` and it,
and a rational quotient measure compatible with it and the counting measure) and
`TwistedGeometricMeasures.term`, the product of the rational covolume and the twisted orbital
integral.

The module is abstract: `GW` and `GG` are topological groups with Borel measurable structures,
`RW ≤ GW` and `RG ≤ GG` are subgroups, `θ : GW →* GW`, and the ordinary side uses
`MonoidHom.id GG`. It is the combinatorial step of the comparison of a twisted and an
ordinary simple trace formula (Arthur–Clozel, *Simple algebras, base change, and the advanced
theory of the trace formula*, Chapter 1, §4, (4.4)–(4.6); Henniart–Lemaire, *Changement de
base et induction automorphe pour GL_n en caractéristique non nulle*, II.6.6): the classes
in the two finite sums are paired through a norm relation and the paired terms are compared.
The Lean formulation and its proof are derived from that argument.

## Definitions

- `TwistedTermMatchesOrdinaryTerm RW RG θ μW μG φ f c x y`: for every
  `d : TwistedGeometricMeasures RW θ x μW` there is
  `d' : TwistedGeometricMeasures RG (MonoidHom.id GG) y μG` with
  `d.rational Set.univ = d'.rational Set.univ` and
  `twistedOrbitalIntegral θ x d.orbital φ = c * orbitalIntegral y d'.orbital f`.
- `OrdinaryTermMatchesTwistedTerm RW RG θ μW μG φ f c x y`: for every
  `d' : TwistedGeometricMeasures RG (MonoidHom.id GG) y μG` there is
  `d : TwistedGeometricMeasures RW θ x μW` with
  `twistedOrbitalIntegral θ x d.orbital φ = c * orbitalIntegral y d'.orbital f`.

These two propositions name the two directions of term matching used below; the proof of
`GeneralLinearBaseChangeTraceComparisonStatement` produces them in
`Langlands.TraceFormula.GeneralLinearBaseChangeTermMatching`.

## Results

- `exists_twistedOrbit_ne_zero_of_twistedOrbitalIntegral_ne_zero`: if
  `twistedOrbitalIntegral θ δ ν f ≠ 0`, then `f (x⁻¹ * δ * θ x) ≠ 0` for some `x`. Proof: if
  `f` vanishes on the twisted orbit, the orbit function `twistedOrbitFunction θ δ f` is zero
  (by induction on the quotient), so the integral is `0`.
- `geometricExpansion_eq_mul_of_termPairing`: let `T = ∑ j, (d j).term φ` for every choice of
  measures `d` at `r : Fin m → RW`, and `U = ∑ k, (d k).term f` for every choice at
  `q : Fin m' → RG`. Assume that the `r j` are pairwise not rationally `θ`-conjugate, the `q k`
  are pairwise not rationally conjugate, the `r j` cover every rational point with a twisted
  orbit meeting the nonzero locus of `φ` (`hrC`), and the `q k` cover every rational point
  with an orbit meeting the nonzero locus of `f` (`hqC`). Assume predicates `regW`, `regG`
  holding at every `r j` and `q k`, and measures for each term (`hrM`, `hqM`). Let `A` be a
  relation between `RW` and `RG` with these properties:
  - every `x` with `regW x` is related to some `y` (`hNorm`);
  - `A x y` is invariant under rational `θ`-conjugation of `x` (`hAW`) and rational
    conjugation of `y` (`hAG`);
  - two points related to the same point are rationally (twisted) conjugate, on either side
    (`hUW`, `hUG`);
  - for `A x y` with `regW x ∨ regG y`, both `TwistedTermMatchesOrdinaryTerm` and
    `OrdinaryTermMatchesTwistedTerm` hold at `(x, y)` (`hMatchW`, `hMatchG`);
  - for `y` with `regG y` related to no `x`, every ordinary orbital integral of `f` at `y`
    vanishes (`hOff`).

  Then `T = c * U`.
- `geometricExpansion_eq_mul_of_termPairing_continuousMulEquiv`: the same for a topological
  group automorphism `θ : GW ≃ₜ* GW` with `θ.toMonoidHom` in the terms. The distinctness and
  covering hypotheses are stated with membership in `RW`, `RG`, in the form produced by the
  simple (twisted) trace formulas. It is a direct application of the previous theorem.
- `exists_twistedGeometricMeasures_map`: let `e` be a topological group isomorphism of twisted
  centralizers `twistedCentralizer θ₁ δ₁ ≃ₜ* twistedCentralizer θ₂ δ₂` matching the points of
  `Γ₁` and `Γ₂`. Assume the target centralizer is commutative, `G₂` is Hausdorff, locally
  compact and second countable, `θ₂` is continuous and `μ₂` is a right-invariant Haar measure.
  Then each `d : TwistedGeometricMeasures Γ₁ θ₁ δ₁ μ₁` has a
  `d' : TwistedGeometricMeasures Γ₂ θ₂ δ₂ μ₂` with `d'.centralizer = d.centralizer.map e` and
  the same rational covolume.

## Proofs

**`geometricExpansion_eq_mul_of_termPairing`.** Put `P j k := A (r j) (q k)`. By `hUG` and
`hqD`, each `j` has at most one `k` with `P j k`; by `hUW` and `hrD`, each `k` has at most one
`j`. Fix measures `d j` from `hrM`. For each `k`, choose `d' k` as follows. If `P j k` for
some `j`, take the measures given by `hMatchW` at `(r j, q k)` applied to `d j`; they have
the same covolume and matching orbital integral. Otherwise take any measures from `hqM`.
Then:

- *Rows.* `(d j).term φ = ∑ k, if P j k then (d j).term φ else 0`. If the term is nonzero, its
  twisted orbital integral is nonzero. `hNorm` gives `y` with `A (r j) y`, and `hMatchW`
  gives a nonzero orbital integral of `f` at `y`. By
  `exists_twistedOrbit_ne_zero_of_twistedOrbitalIntegral_ne_zero` and `hqC`, `y` is
  conjugate to some `q k`; `hAG` gives `P j k`, and this `k` is unique.
- *Columns.* `c * (d' k).term f = ∑ j, if P j k then (d j).term φ else 0`. If `P j k`, the
  covolumes and orbital integrals of the chosen measures match. If no `j` has `P j k`
  and the left side is nonzero, then `c ≠ 0` and the orbital integral at `q k` is nonzero.
  If some `x` has `A x (q k)`, then `hMatchG` gives a nonzero twisted orbital integral at `x`.
  The covering property `hrC` and `hAW` then give a `j` with `P j k`, a contradiction.
  Otherwise `hOff` makes the orbital integral zero.

Rewriting `T` and `U` with `hT d` and `hU d'` and exchanging the finite double sum gives
`T = c * U`.

**`exists_twistedGeometricMeasures_map`.** The pushed measure `d.centralizer.map e` is
right-invariant, finite on compacts and positive on open sets. It is left-invariant because the
target is commutative, so it is a Haar measure on the closed (hence locally compact and second
countable) target centralizer. `compatibleMeasureExists` gives a compatible orbital quotient
measure. The rational quotient measure is transported along the homeomorphism of quotients
induced by `e` (`isCompatible_map_equiv`, with the pushforward of the counting measure being
the counting measure). The covolume is unchanged because the preimage of `Set.univ` is
`Set.univ`.
