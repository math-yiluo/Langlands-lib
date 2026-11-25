# Nonempty joint convergence interior of the c-family (statement)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionJointDomain`,
namespace `Langlands.HarishChandraSchwartz.WeakExpansion`.

## Purpose and status

The published structure `WeightedCExtension` (module `RationalWeakExpansionTargets`) is the
conclusion of the regularity target `WeightedCRegularityBorelStatement` (Waldspurger, Corollary
V.2.3). Its field `interior_nonempty` asks that the domain `cWeightedDomain` of the weighted
c-family `c̃_{P'|P}(s, ·)` have nonempty interior. The published
`cWeightedDomain_interior_nonempty_iff` (module `RationalWeightedCDomain`) splits this into two
inputs:

1. the interior of the joint convergence domain `cDomain` is nonempty;
2. the lower density package's canonical scalar is nonzero.

Input 2 is proved in the Library (`lowerDensityCanonicalScalarNonzero`, module
`RationalWeakExpansionDensityNonzero`). This module states input 1 and proves that the two
together give the field `interior_nonempty`.

- `CDomainInteriorNonemptyStatement` is **not proved** here or anywhere in the Library.
- `cWeightedDomain_interior_nonempty_of_cDomain` is proved.
- Nothing here proves `WeightedCRegularityBorelStatement`, `WeightedWeakExpansionStatement`,
  `WeightedCDecompositionBorelStatement` or `WeightedPacketIdentityStatement`.

## Data

The data are those of `RationalWeakExpansionTargets` (see its Markdown, section "Data"). The
ambient group is connected reductive (`hG`) with maximal split torus `i` (`hi`) and generic
cocharacter `ν` (`hν`). `I` and `I'` are sets of simple roots, and `ζ`, `ζ'` are standard
cocharacters for them (`hζ`, `hζ'`); so `M = M_I`, `P = P_I`, `M' = M_{I'}` and `P' = P(ζ')`. The
normalizer point `n` lifts `s`, and `hn` says `s·M ⊆ M'`. `K` is a compact open subgroup of `G(F)`
(`hKc`). `sc` is a split component of the Levi scheme of `M` (`hs`), and `C_M`
(`rationalLeviSplitCenter I sc`) is the group of its rational points. `π` is an irreducible
admissible representation of `M(F)`. `μ` is a Haar measure on `M(F)/C_M`.

`cDomain hG hi hν I I' hζ hζ' n hn K hKc π.obj` (module `RationalWeakExpansionCFamily`) is the set
of unramified characters `z` of `M(F)` at which both standard integrals of the c-family converge
on every vector (`CConverges`):

- `J_{P_s|s·P}` on the conjugate `ⁿ(π ⊗ z)`, where `P_s = (M' ∩ s·P)U'`;
- `J_{P̃_s|s·P}` on the conjugate `ⁿ((π ⊗ z)ˇ)` of the smooth dual, where `P̃_s = (M' ∩ s·P)Ū'`.

The quotient measures are normalized at `K`. The published definition asserts neither openness
nor nonemptiness of this set.

## The statement

**Definition `CDomainInteriorNonemptyStatement`.** Its explicit arguments are
`hG hi hν I I' hζ hζ' n hn hKc sc hs π mu`. It also takes the instance argument
`[BorelSpace (M(F)/C_M)]` as an explicit binder, with the measurable structure
and Haar instance of `μ`. Its body has three premises:

1. `π` is square integrable modulo `C_M` for `μ` (`IsSquareIntegrableModCentralSubgroup`);
2. `K` is the special maximal compact subgroup (`IsSpecialVertexCompact ν hi K`);
3. `K` is an Iwasawa complement of the standard minimal parabolic
   (`IsIwasawaPair (standardParabolicPoints i ν ∅) K`).

Its conclusion: the interior of `cDomain … n hn K hKc π.obj` is nonempty.

The premises are among those of `WeightedCRegularityBorelStatement`: premises 1 and 2 are arrows
of its body, and premise 3 is its explicit argument `hPK`. The statement is for one lift `n`; the
target quantifies over all `s`.

## The proved reduction

**Theorem `cWeightedDomain_interior_nonempty_of_cDomain`.** Assume
`CDomainInteriorNonemptyStatement` for these data, square integrability of `π` modulo `C_M`, and
premises 2 and 3. Then for all density packages `PG` (of `G`) and `PM` (of the lower Levi), the
interior of `cWeightedDomain … PG PM` is nonempty.

Proof as implemented: the right-to-left direction of `cWeightedDomain_interior_nonempty_iff`.
Its first input is the statement applied to the three premises. Its second input,
`PM.canonicalScalar ≠ 0`, is `lowerDensityCanonicalScalarNonzero` applied to square integrability.

## Relation to the source

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, registered as
`waldspurger-2003-plancherel` (SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`).

- IV.1, Proposition IV.1.1 (printed p.278): the integral `J_{P'|P}(σ ⊗ χ)` converges for `χ`
  in an open cone of parameters, namely where the real part of `χ` is large on the coroots of the
  roots of `A_M` in `U_P ∩ Ū_{P'}`.
- V.1 (printed pp.288–289): the definition of `c_{P'|P}(s, ω)` through `J_{P_s|s·P}(sω)` and
  `J_{P̃_s|s·P}(sω̌)`. Their simultaneous convergence is implicit in the source, which works with
  the rational continuations.

The statement is **derived**: the source does not state it separately. It is true for the
following reason, which is a plan for a proof and is not formalized here. The roots of the first
integral are the roots `α` of `A_{s·M}` that are positive on `s·P` and pair negatively with `ζ'`.
The roots of the second are those positive on `s·P` that pair positively with `ζ'`. The second
integral is evaluated at `(π ⊗ z)ˇ = π̌ ⊗ z⁻¹`, whose real part is `−Re z`. `ζ'` is central in
`M' ⊇ s·M`, so it lies in `a_{s·M}`. Let `λ` be the image of `−ζ'` in `a*_{s·M}` under a
nondegenerate Weyl-invariant form. Then `⟨tλ, α̌⟩` is a positive multiple of `−t⟨α, ζ'⟩`. For
`t` large, `Re(sz) = tλ` satisfies the convergence thresholds of both integrals. Square
integrability gives unitarizability, hence bounded coefficients for `π` and `π̌`, so the
thresholds come from the published convergence results (for instance the common-Levi
continuation in `ActualCommonLeviUnitaryContinuation` and its cone-decay input). The threshold
conditions are strict inequalities in `Re z`, so they define an open set.

## Imports

`RationalWeakExpansionTargets` (`IsSpecialVertexCompact`), `RationalWeightedCDomain`
(`cWeightedDomain_interior_nonempty_iff`) and `RationalWeakExpansionDensityNonzero`
(`lowerDensityCanonicalScalarNonzero`). No axioms, no `sorry`.
