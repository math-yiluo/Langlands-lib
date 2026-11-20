# The residue pairing of two cusp forms detects the contragredient

Lean module: `Langlands.Global.RankinSelberg.CuspidalSlabPairingStatement`.

This module defines the slab pairing `slabPairing T T' x x'` of two cusp forms and states
`CuspidalSlabPairingStatement`, the residue clause of Cogdell (2004), Theorem 2.2, in the
case where the product of the central characters is trivial. The statement is a premise of
`CuspidalPairPoleReductionStatement`. It is a proposition definition only.

## 1. Sources

"p." is the printed page, "PDF" the one-based page of the registered file
(`cogdell-2004-analytic-theory-gln`: PDF = printed + 3).

| Source ID | Locators |
|---|---|
| `cogdell-2004-analytic-theory-gln` | the global integral `I(s; φ, φ', Φ)`, p.209 (PDF 212); its residues and the invariant pairings they define, p.210 (PDF 213); Theorem 2.2, p.211 (PDF 214) |

**What the source states.** Cogdell p.209 defines, for cusp forms `φ ∈ V_π`, `φ' ∈ V_π'`
of `GL_n(𝔸)` with central characters `ω`, `ω'` and `η = ω ω'`,
`I(s; φ, φ', Φ) = ∫_(Z_n(𝔸) GL_n(k) \ GL_n(𝔸)) φ(g) φ'(g) E(g, Φ; s, η) dg`.
On p.210: the integrals are entire unless `η(a) = |a|^(inσ)`; in that case the residues at
`s = -iσ` and `s = 1 - iσ` are `-c Φ(0) ∫ φ(g) φ'(g) |det g|^(-iσ) dg` and
`c Φ̂(0) ∫ φ(g) φ'(g) |det g|^(iσ) dg` (integrals over `Z_n(𝔸) GL_n(k) \ GL_n(𝔸)`,
`c ≠ 0`). "Therefore these residues define `GL_n(𝔸)` invariant pairings between `π` and
`π' ⊗ |det|^(-iσ)` … Hence a residue can be nonzero only if `π ≅ π̃' ⊗ |det|^(iσ)` and in
this case we can find `φ`, `φ'` and `Φ` such that indeed the residue does not vanish."
Theorem 2.2 (p.211) records that the poles occur exactly in this case, with these residues.

## 2. Declarations

### `slabPairing T T' x x'`

For actual cuspidal realizations `T`, `T'` of `GL_(r+1)` and vectors `x`, `x'`,
`slabPairing T T' x x' = residueConstant F r (φ φ') 0` with `φ = cuspFunction F T x`,
`φ' = cuspFunction F T' x'`. The Library's `EqualAnalytic.residueConstant F r P w` is
`∫_(D ∩ S) P(g) |det g|^(-w/n) dg` for the Haar measure of `GL_n(𝔸)`, where `D` is the
Library fundamental domain of `GL_n(F)` in `GL_n(𝔸)` (`glDomain`) and `S` the slab
`1 ≤ |det g| < e^n` (`glSlab`), `n = r + 1`. So `slabPairing T T' x x' = ∫_(D ∩ S) φ φ'`.

**Why this is the residue pairing.** The Library's `EqualData.main`
(`Langlands/Global/RankinSelberg/EqualAnalyticMain.lean`) continues `I(s)` as
`A(s) + Ã(1 - s) + Φ̂(0) C_w / (n(s - 1) + w) - Φ(0) C_w / (n s + w)` when `η = |·|^w`, with
`A`, `Ã` entire and `C_w = residueConstant F r (φ φ') w`. At `w = 0` the residues at `s = 1`
and `s = 0` are `Φ̂(0) C_0 / n` and `-Φ(0) C_0 / n`. So `C_0` is the Library's form of
Cogdell's residue integral; the statement is phrased with it, and the Lean statement makes
no claim about the normalizing constant relating `C_0` to an integral over
`Z_n(𝔸) GL_n(F) \ GL_n(𝔸)`.

### `CuspidalSlabPairingStatement`

For every number field `F`, `r`, actual cuspidal realizations `T`, `T'` of `GL_(r+1)` and
central characters `ω` of `T`, `ω'` of `T'`:

1. if `ω ω' = 1` and `slabPairing T T' x x' ≠ 0` for some `x`, `x'`, then
   `T.realization.IsContragredientOf T'.realization` (`T` realizes the contragredient of
   `T'`);
2. if `T` realizes the contragredient of `T'`, then `ω ω' = 1`, and for all spectral
   presentations `P`, `P'` of `T`, `T'` and every finite set `S` of finite places containing
   `P.exceptional` and `P'.exceptional`, there are `x`, `x'` with
   `IsSphericalOutside F T S x`, `IsSphericalOutside F T' S x'` (fixed by `GL_(r+1)(𝒪_v)` at
   every finite `v ∉ S`) and `slabPairing T T' x x' ≠ 0`.

## 3. Match with the source, and what is added

- The case `σ = 0` (`η = 1`) of Cogdell's residue clause is the only one stated. It is the
  case used by `CuspidalPairPoleReductionStatement`, where both realizations are trivial on
  the split components of their centres, so that `η` is trivial on `A_(G_m)` and the
  exponent `w` vanishes (proved in `CuspidalPairPoleReductionLemmas`,
  `eq_zero_of_isTrivialOnSplitCentre`).
- Clause 1 is the "only if" part: a nonzero residue pairing is a nonzero invariant pairing,
  hence (irreducibility) a contragredient pairing. Cogdell's `GL_n(𝔸)`-invariance is, in
  Library terms, invariance under the finite adelic group, the standard compact subgroup and
  the real Lie algebra (`OperatorRealization.IsInvariantPairing`); the Library's
  `CuspidalOperatorRealization.isContragredientOf_of_nonzero_invariant` turns a nonzero such
  pairing into `IsContragredientOf`.
- Clause 2 is Cogdell's "in this case we can find `φ`, `φ'`, `Φ` such that the residue does
  not vanish", refined in two standard ways, which this Markdown records as provenance:
  (a) the contragredient of a realization with central character `ω'` has central character
  `ω'^(-1)`, so `ω ω' = 1`; (b) the vectors can be taken spherical outside any `S`
  containing the exceptional sets. For (b): by Cogdell p.210 the pairing
  `(x, x') ↦ C_0(φ_x, φ'_x')` is invariant and, in this case, nonzero; let `K^S` be the
  product of the groups `GL_(r+1)(𝒪_v)` over the finite `v ∉ S`. The spherical subspace of
  `T` is nonzero for such `S` (Library `SelfPair.exists_sphericalOutside_ne_zero`); for a
  nonzero spherical `x` the functional `C_0(φ_x, ·)` is nonzero (the pairing of an
  irreducible realization with its contragredient is nondegenerate), and
  `C_0(φ_x, φ'_x') = C_0(φ_x, φ'_(e x'))`, where `e` averages over `K^S` (a finite average
  over `K^S / K'` for `x'` fixed by an open `K' ⊆ K^S`) and `e x'` is spherical outside `S`.
  So some spherical pair has `C_0 ≠ 0`.

## 4. Conventions

- `T.realization.IsContragredientOf T'.realization` is the orientation of
  `CuspidalPairPoleStatement` ("`T` realizes the contragredient of `T'`").
- Measures: the Haar measure `Measure.haar` of `Points F (r + 1)`, as in
  `residueConstant`; the statement is insensitive to positive rescaling.
