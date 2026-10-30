# Factorization of a bi-equivariant cell distribution over the compatible torus: proof

Authors: Worker 634 and Worker 1081. Worker 634 wrote the complete private proof
`BruhatCellFactorizationCore.factorization` of the identical private design statement,
shared in parent draft revision 8 of task `f79ca82c-d050-4ffa-821b-c347b60e36e0`
(`Langlands/Representation/Whittaker/BruhatCellFactorizationCore.lean`, SHA256
`ebf5b237d809a1a6ec6eaf23a6324eba27241eee6d75757d7c8ea3a19d885895`). Worker 1081 ported
it unchanged in substance into this module: the helpers moved to the namespace
`Langlands.Whittaker.BruhatCellFactorization`, the final theorem was renamed
`Langlands.Whittaker.bruhatCellFactorization` and now targets the published statement,
and the docstrings and this Markdown were written for the production pair.

This module proves `Langlands.Whittaker.bruhatCellFactorization.{uF}`, whose type is
exactly the published proposition `Langlands.Whittaker.BruhatCellFactorizationStatement.{uF}`
of `Langlands.Representation.Whittaker.BruhatCellFactorizationStatement`. The statement
module and everything it imports are used unchanged. Besides the statement module, the
proof imports only the published modules

- `Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof`, for `cellSection`
  and `upperBruhatTorusMap_cellSection` (and, through its imports, the published
  coordinate theorem `Langlands.GeneralLinear.upperBruhatCoordinates`);
- `Langlands.Representation.Whittaker.BruhatCompatibleSupportProof`, for
  `Langlands.Whittaker.bruhatCompatibleSupport`;
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof`, for
  `Langlands.HarmonicAnalysis.Distribution.characterAverageFactorization`;

and Mathlib's `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`. It adds no
hypothesis, axiom or proof hole. The only axioms of the theorem are `propext`,
`Classical.choice` and `Quot.sound`.

## What is proved

Everything the statement quantifies is kept: the universe `uF`, every prime `p`, every
p-adic field `F : PadicField.{uF} p` with its canonical normed field structure, every
`n : ℕ` (so every rank `n + 1`, rank one included), every unitary additive character `ψ`,
every permutation `w`, every s-finite right-invariant Haar measure `μ` on `U`, every
right-invariant Haar measure `ν` on `P = U_w⁺`, every complex-linear
`I : SchwartzBruhat M →ₗ[ℂ] SchwartzBruhat C` satisfying only the evaluation formula

    I α (upperBruhatTorusMap (n + 1) w m) = bruhatFiberAverage (n + 1) F.Carrier w ν α m,

and every algebraic distribution `D : Distribution C` with
`IsBiEquivariantBruhatCellDistribution n F.Carrier w ψ D`. The conclusion is the
statement's: a unique `τ : Distribution H` with
`τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)` and
`Distribution.characterAverageDual (standardCharacterContinuous ψ n) μ τ = D.comp I`,
uniqueness being over the conjunction. Here `U`, `P`, `H = Fin (n + 1) → F.Carrierˣ`,
`M = U × (H × U)` and `C = UpperBruhatCell (n + 1) F.Carrier w` are the statement's
actual groups, torus, product and cell with their actual topologies, and `D`, `τ` are
arbitrary complex-linear functionals on test functions, with no continuity.

No surjectivity, support control or equivariance of `I` is assumed. Only the evaluation
formula is used, together with surjectivity of the torus multiplication map
`upperBruhatTorusMap` onto the cell, which is proved here from published coordinates.

## Declarations

All auxiliary declarations are in `Langlands.Whittaker.BruhatCellFactorization`.
Write `T_{a,b}` for the product translation
`(Homeomorph.mulLeft a).prodCongr ((Homeomorph.refl H).prodCongr (Homeomorph.mulRight b))`
of `M`, which sends `(m₁, (d, m₂))` to `(a * m₁, (d, m₂ * b))`; it is literally the
homeomorphism appearing in the published `CharacterAverageFactorizationStatement`. Write
`h(d) = Iwasawa.diagonalUnits d` and `p_w = permutation (n + 1) K w`.

The section `Generic` works over any field `K` with a topology making it a topological
ring, for `w : Equiv.Perm (Fin (n + 1))`.

- `fiberAct_productTranslate a b u m`:
  `bruhatFiberAct u (T_{a,b} m) = T_{a,b} (bruhatFiberAct u m)`. The published fiber
  action sends `(m₁, (d, m₂))` to `(m₁ p_w h(d) u⁻¹ h(d)⁻¹ p_w⁻¹, (d, u m₂))`; the first
  coordinates agree by associativity of matrix multiplication, the torus coordinates are
  both `d`, and the last coordinates are `u (m₂ b) = (u m₂) b`.
- `torusMap_productTranslate a b m`:
  `upperBruhatTorusMap (n + 1) w (T_{a,b} m) = bruhatCellBiTranslate n K w a b
  (upperBruhatTorusMap (n + 1) w m)`, that is
  `(a m₁) p_w h(d) (m₂ b) = a (m₁ p_w h(d) m₂) b`, again by associativity.

Assume further `T2Space K` and a measure `ν` on `P` (with its Borel σ-algebra) that is
finite on compacts, as `bruhatFiberAverage` requires.

- `fiberAverage_pullback_productTranslate a b α m`:
  `bruhatFiberAverage ν (pullback T_{a,b} α) m = bruhatFiberAverage ν α (T_{a,b} m)`.
  Both sides are `∫ u, _ ∂ν` by `bruhatFiberAverage_apply`, and the integrands are equal
  at every `u` by `fiberAct_productTranslate`. No change of variables in the measure is
  made.
- `fiberAverage_pullback_fiberAct hν u α m`: for a left-invariant `ν`,
  `bruhatFiberAverage ν (pullback (bruhatFiberActHomeomorph u) α) m =
  bruhatFiberAverage ν α m`. The left integrand is
  `α (bruhatFiberAct u (bruhatFiberAct v m)) = α (bruhatFiberAct (u * v) m)` by the
  published composition law `bruhatFiberAct_bruhatFiberAct`, and Mathlib's
  `integral_mul_left_eq_self` removes the left translation `v ↦ u * v` of the
  integration variable.

Now fix a linear map `I` from test functions on `M` to test functions on the cell with
the evaluation formula `hI`, and assume `hπ`: `upperBruhatTorusMap (n + 1) w` is
surjective.

- `orbitalIntegral_pullback_productTranslate a b α`:
  `I (pullback T_{a,b} α) = pullback (bruhatCellBiTranslate n K w a b) (I α)`. Two test
  functions on the cell are equal if they agree at every `c`; write
  `c = upperBruhatTorusMap (n + 1) w m` by `hπ`. Then the left side is
  `bruhatFiberAverage ν (pullback T_{a,b} α) m = bruhatFiberAverage ν α (T_{a,b} m)`,
  which by `hI` is `I α (upperBruhatTorusMap (T_{a,b} m))`, and by
  `torusMap_productTranslate` this is `I α (bruhatCellBiTranslate a b c)`, the right side.
- `orbitalIntegral_pullback_fiberAct hν u α`:
  `I (pullback (bruhatFiberActHomeomorph u) α) = I α` for a left-invariant `ν`. At
  `c = upperBruhatTorusMap m`, both sides are fiber averages by `hI`, and they agree by
  `fiberAverage_pullback_fiberAct`.

The section `Coordinates` works over a Hausdorff topological division ring `K` of any
rank `r`.

- `torusMap_surjective w`: `upperBruhatTorusMap r w` is surjective. The second component
  of the published `upperBruhatCoordinates K r w` gives a homeomorphism `eT` from
  `U × H × U_w⁻` onto the cell with `(eT x).val = x₁ p_w h(x₂) x₃`. The published
  `cellSection eT c` and `upperBruhatTorusMap_cellSection` give a preimage of each cell
  point `c`.

## The main proof

`bruhatCellFactorization` introduces `p`, `hp`, `F`, installs
`F.canonicalNormedField`, introduces `n`, `ψ`, `w` and the local names `U`, `P`, `H`,
`M`, `C` with the statement's Borel structures, and then `μ`, its instances, `ν`, its
instances, `I`, `hI`, `D` and `hD`, exactly as the statement binds them.

1. **Topology.** The published `F.canonicalUpperUnipotentTopologicalGroup`,
   `canonicalUpperUnipotentT2Space`, `canonicalUpperUnipotentLocallyCompactSpace` and
   `canonicalUpperUnipotentNonarchimedean` supply the topological group, Hausdorff,
   locally compact and nonarchimedean structures that
   `CharacterAverageFactorizationStatement` requires of `G = U`. For `Y = H`, the
   canonical field is a finite-dimensional normed space over `Padic p`
   (`F.canonicalNormedAlgebra`), hence proper (`FiniteDimensional.proper`), so `Fˣ` and
   the finite product `H` are locally compact and Hausdorff by instance search. The
   spectral norm is nonarchimedean (`isNonarchimedean_spectralNorm`), so the distance is
   ultrametric and `F.Carrier` is totally disconnected; `Units.isEmbedding_val₀` embeds
   `Fˣ` into `F.Carrier`, so `Fˣ` and then `H` are totally disconnected. These are the
   actual topologies of the statement; nothing is replaced.
2. **Surjectivity of the torus map.** `hπ := torusMap_surjective w` over `F.Carrier`.
3. **Product bi-equivariance of `D.comp I`.** For `a, b : U` and `α`,
   `(D.comp I) (pullback T_{a,b} α) = D (I (pullback T_{a,b} α))
   = D (pullback (bruhatCellBiTranslate a b) (I α))` by
   `orbitalIntegral_pullback_productTranslate`, and this is
   `((χ a : ℂ) * (χ b : ℂ)) * D (I α)` by the bi-equivariance hypothesis `hD` applied to
   the test function `I α`, with `χ = standardCharacterContinuous ψ n`. Both character
   factors are positive, exactly as in the published generic statement.
4. **Generic factorization.** The published
   `Distribution.characterAverageFactorization` (proving
   `CharacterAverageFactorizationStatement` for `G = U`, `Y = H`, `χ`, `μ` and the
   distribution `D.comp I` on `U × (H × U) = M`) yields `τ` with
   `characterAverageDual χ μ τ = D.comp I` (`hτ`) and uniqueness among all `τ'` with the
   same equality (`hunique`). The averaging weight is the published
   `characterAverage`'s inverse product `((χ z₁ : ℂ) * (χ z₂ : ℂ))⁻¹`, unchanged.
5. **Support.** The published `bruhatCompatibleSupport p hp F n ψ w μ τ` reduces
   `τ ∈ Distribution.supportedOn (compatibleTorus ψ n w)` to invariance of
   `characterAverageDual χ μ τ` under pullback by every fiber action
   `bruhatFiberActHomeomorph u`. Rewriting with `hτ`, this is
   `D (I (pullback (bruhatFiberActHomeomorph u) α)) = D (I α)`, which follows from
   `orbitalIntegral_pullback_fiberAct`, using the left invariance of `ν` that its
   `IsHaarMeasure` instance supplies.
6. **Uniqueness.** Any `τ'` satisfying both clauses satisfies the factorization clause,
   so `τ' = τ` by `hunique`.

## Remarks on the route

- The statement's right-invariance hypothesis on `ν` is not used; the fiber invariance
  in step 5 uses left invariance of the Haar measure `ν`. The hypotheses `SFinite μ` and
  `μ.IsMulRightInvariant` are passed to the two published theorems that require them.
- No algebraic distribution is commuted with an integral. The only integrals are the
  raw fiber averages of individual test functions in the two `fiberAverage_*` lemmas,
  compared pointwise in the integration variable (or by Mathlib's left-translation
  invariance of the Bochner integral). `D` and `τ` are only ever applied to single test
  functions, and the identities in steps 3 and 5 are identities of test functions on the
  cell proved by evaluating at each cell point.
- Surjectivity of `I` is neither assumed nor needed. Only surjectivity of the
  multiplication map `upperBruhatTorusMap` is used, to show that the evaluation formula
  determines `I α` at every point of the cell.

## Provenance

The proof route is internal; it supplies the steps outlined in the statement's Markdown
(intended steps 1–4), with left rather than right invariance of `ν` in the fiber step.
The target is motivated by J. A. Shalika, *The multiplicity one theorem for GL_n*,
Ann. of Math. (2) **100** (1974), 171–193 (registered `shalika-1974-multiplicity-one`):
Lemma 1.10 and formula (1.11) on printed p.176, and Propositions 1.12 and 1.13 on printed
p.177. The statement's companion Markdown explains the derived scope, the inverse
convention of the source's `U × U` action and the `γ`/`δ` misprint in the proof of
Proposition 1.13; this proof depends on neither. The proof does not follow the source's
argument for Proposition 1.12, whose proof the source omits; it uses the published
generic character-average factorization instead.

## Scope

This proves only `BruhatCellFactorizationStatement`. It establishes neither cell
vanishing, cell or global Weyl-transpose invariance, finite-filtration assembly,
Shalika's distribution-invariance theorem nor multiplicity one; those are separate tasks.
