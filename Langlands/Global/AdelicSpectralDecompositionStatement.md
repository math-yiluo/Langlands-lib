# Langlands' spectral decomposition of `L²([G])`

Module `Langlands.Global.AdelicSpectralDecompositionStatement` states
`Langlands.Global.SpectralDecompositionStatement` as a proposition
definition. It supplies no proof.

## Sources

- Getz–Hahn, *An introduction to automorphic representations*, registered
  as `getz-hahn-2024-automorphic-representations`, §10.5, pp.281–282 (PDF
  pages 293–294): Theorem 10.5.1 (Langlands),
  `L²([G]) = ⊕_𝒫 L²_𝒫([G])`, the sum over the association classes `𝒫` of
  parabolic subgroups of `G`, together with (10.21) ("the (finite) direct
  sum") and the remark `L²_G([G]) = L²_disc([G])`.
- J. Arthur, *An introduction to the trace formula*, Clay Math. Proc. 4
  (2005), registered as
  `arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, Theorem 7.2(b)
  and (7.5), printed p.35 (PDF page 47): the orthogonal direct sum
  decomposition `L²(G(F) \ G(𝔸)) = ⊕_𝒫 L²_𝒫(G(F) \ G(𝔸))` into closed
  `G(𝔸)`-invariant subspaces. GH note that their theorem is Arthur's, with
  `L²([G])` in place of `L²(G(F) \ G(𝔸))`.
- P. Delorme, *On the spectral theorem of Langlands*, registered as
  `delorme-2023-spectral-theorem-langlands`, Theorem 6.1, Lemma 6.2 and
  Theorem 7.9 (PDF pages 22 and 33): a complete proof of the surjectivity
  half, with Lapid's Theorem 2 for the isometry.

## Statement

The data, for a number field `F : Type`: `G` connected reductive (`hG`); a
maximal compact subgroup `K` of `G(𝔸)`; a closed matrix embedding `rho`;
the smooth-structure data `hsmooth`, `hcalc`. The statement then holds for
every minimal parabolic `p₀ : P₀ → G` (`IsMinimalParabolicSubgroup p₀`,
`p₀` a closed immersion, `P₀` affine) with `P₀(𝔸)K = G(𝔸)`
(`IsIwasawaCompact p₀ K`).

A presented standard parabolic is: `p : P → G` a closed immersion with
`SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p` (that is,
`P₀ ⊆ P`), `iU : U → P` with `LeviSubgroup.IsGeometricUnipotentRadical iU`,
a Levi `l : M → P`, a split component `a : A → M`, a presentation
`r : ParabolicRootPresentation p l a` with its instance arguments, `hA`,
`hT`, and `hK : IsIwasawaCompact p K`. For it, `L²_P([G])` is
`parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT` (module
`Langlands.Global.AdelicParabolicSpectrum`), the closed span in
`L²([G]) = Lp ℂ 2 (canonicalMeasure F G)` of the wave packets of `P` over
`i(𝔞_M^G)^*`. Let `S` be the set of all subspaces `L²_P([G])` of presented
standard parabolics. The conclusion is the conjunction of:

1. `S` is finite and the closure of the sum of its members is `⊤`.
2. For every presented standard parabolic `P`:
   - if `p` is an isomorphism, `L²_P([G]) = discreteSpectrum F G hG`;
   - for every presented standard parabolic `P'`, if there are a rational
     point `w` of `G` and `c : M' → M` with
     `IsWeylConjugation p l p' l' w c`, then `L²_P([G]) = L²_{P'}([G])`;
   - for every presented standard parabolic `P'`, if there are no such `w`
     and `c`, then `L²_P([G]) ⟂ L²_{P'}([G])` (`Submodule.IsOrtho`).

## Correspondence with the source

- Association. `IsWeylConjugation p l p' l' w c` says that `c : M' → M` is
  an isomorphism with `l(c(m')) = w⁻¹ l'(m') w`, that is, `w M w⁻¹ = M'` for
  the rational point `w`. Two parabolics are associate exactly when their
  Levi subgroups are `G(F)`-conjugate, that is, when
  `W(𝔞_M, 𝔞_{M'}) ≠ ∅` (GH §10.2, p.273).
- Standard parabolics. GH and Arthur index the families (10.22) by the
  standard parabolics `P ∈ 𝒫`, those containing the fixed minimal parabolic
  `P₀`. Every parabolic is `G(F)`-conjugate to a standard one, and
  conjugate parabolics are associate, so every association class contains a
  standard parabolic and there are finitely many classes. Every standard
  `P` satisfies `P(𝔸)K ⊇ P₀(𝔸)K = G(𝔸)`, so the hypothesis
  `hK : IsIwasawaCompact p K` is automatic for it. A standard `P` also has
  presentations: choose a maximal split torus `T` in a Levi subgroup of
  `P₀`, the Levi subgroup `M ⊇ T` of `P`, its split component `A ⊆ T`, and
  the root data of `T` with the positive system defined by `P₀`. The
  Library does not prove this existence (the type
  `ParabolicRootPresentation p l a` may be empty a priori), so the
  statement is about the presented standard parabolics; mathematically
  these are all standard parabolics. Parabolics not containing `P₀` are not
  used. This is explanatory and not proved here.
- The choice of Levi subgroup. For a standard `P` the space does not depend
  on the Levi `l` or on the presentation, by the second item applied to two
  presentations of the same `P`: the Levi subgroups of `P` are conjugate
  under `U(F)`, which gives `w` and `c`. Directly: for `u ∈ U(F)` and
  `a ∈ A_M`, `a u⁻¹ = (a u⁻¹ a⁻¹) a` with `a u⁻¹ a⁻¹ ∈ U(𝔸)`, so for a
  function `φ` left invariant under `U(𝔸)P(F)` one has
  `φ(u a u⁻¹ g) = φ(a g)`. Hence Lapid's conditions defining `A^2_P` are the
  same for `M` and `uMu⁻¹`, and so are the Eisenstein series. This is
  explanatory and not proved here.
- The direct sum. By the second and third items, distinct members of `S`
  come from non-associate parabolics and are orthogonal. With the first
  item, `L²([G])` is the orthogonal direct sum of the finitely many closed
  subspaces in `S`, one for each association class. This is the
  decomposition (10.21) of GH Theorem 10.5.1 with `L²_𝒫([G]) = L²_P([G])`
  for a standard `P ∈ 𝒫`: the Markdown of
  `Langlands.Global.AdelicParabolicSpectrum` explains why the closed span of
  the wave packets of one `P ∈ 𝒫` is GH's `L²_𝒫([G])` once the second item
  holds. This is explanatory and not proved here.
- `L²_disc`. GH have `L²_G([G]) = L²_disc([G])` by definition. Here the
  space of `G` (which contains `P₀`) is the closed span of the
  square-integrable automorphic forms on `[G]` (the Markdown of
  `Langlands.Global.AdelicParabolicSpectrum`, case `P = G`). Its equality
  with the discrete part of the right regular representation is part of the
  classical theory (each square-integrable automorphic form generates a
  finite sum of irreducible subrepresentations, and the `K`-finite,
  `Z`-finite vectors of an irreducible subrepresentation are
  square-integrable automorphic forms and are dense in it). It is stated as
  the first part of the second item.
- The compact subgroup. GH, Arthur and Delorme fix `K` in good position
  with respect to a minimal Levi subgroup, contained in `P₀`, for which
  `G(𝔸) = P₀(𝔸)K`. Here `K` is any maximal compact subgroup with
  `P₀(𝔸)K = G(𝔸)`, and the statement is required for every minimal
  parabolic `P₀` with this property; it is vacuous if there is none. This
  reduces to their case. Fix `K₀` in good position with respect to a Levi
  subgroup of `P₀`. As in the Markdown of
  `EisensteinAbsoluteConvergenceStatement`, the Eisenstein series formed
  with `K` are finite sums of right translates, by a fixed element of
  `G(F_∞)`, of Eisenstein series formed with `K₀`, with coefficients
  `exp⟨λ, c_j⟩`; on `i𝔞_P^*` these are smooth in `λ` of absolute value `1`.
  So every wave packet for `K` is a finite sum of right translates of wave
  packets for `K₀`, and conversely. Since Arthur's `L²_𝒫` is
  `G(𝔸)`-invariant, the spaces for `K` and `K₀` agree. This is explanatory
  and not proved here.
- Measures and normalizations do not affect the conclusion: spans, closures
  and orthogonality are unchanged by positive multiples of the measure on
  `[G]` and of `dλ`.
- The universe of `F` is `Type`, as in the other global statements.

## Scope

The statement does not construct the Hilbert space `L_𝒫` of Weyl-invariant
families (GH (10.22)) or the unitary map onto `L²_𝒫([G])` (Arthur
Theorem 7.2(b)); the isometry for compactly supported smooth families is
`WavePacketIsometryStatement` and the density half is
`WavePacketCompletenessStatement`, both on `L²(G(F) \ G(𝔸))`. It does not
describe the residual spectrum (GH (10.27)) and makes no claim about
parabolics that do not contain `P₀`.
