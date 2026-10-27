# Proof of the equal-rank Frobenius equivalence

This module proves the unchanged Library proposition
`Langlands.RankinSelberg.EqualRankFrobeniusStatement.{uF,uV,uW}` from
`Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement`. The
theorem is

```lean
theorem Langlands.RankinSelberg.equalRankFrobenius {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    EqualRankFrobeniusStatement.{uF, uV, uW} F T n
```

with the three independent universe parameters `uF`, `uV`, `uW`, in this
order. For every pair of smooth complex representations `ρ`, `σ` of
`G = GL_{n+1}(F)` on arbitrary carriers and every `s : ℂ`, it builds an
explicit complex-linear equivalence from the full space of invariant trilinear
forms on row test functions vanishing at zero (weight `|det g|^(-s)`) to the
actual mirabolic `InvariantBilinear.forms` space (weight `|det p|^(1-s)`). The
source and target types are exactly those of the statement. Rank one (`n = 0`)
and zero carriers are covered by the same argument without special cases. The
only hypotheses used are those of the statement: smoothness of `ρ` and `σ`.
The theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Route

The task asks for a proof of the exact target and allows a route different
from the suggested one. The proof does not build the quotient `P\G`, compact
induction or a general Frobenius reciprocity theorem. It works directly on the
nonzero-row orbit inside row space `X = F^{n+1}` with an additive Haar measure
`μ` on `X`. Write `η = (0,…,0,1)`, `α(g) = |det g|` for the normalized absolute
value `abv = normalizedAbsoluteValue T`, and `lastRow g = ηg`.

* **Forward map** (`fwd`, `fwdForm`). For a mirabolic covariant form `β`,

  ```text
  B_β(v, w, Φ) = ∫_X Φ(x) · β(ρ(g_x) v, σ(g_x) w) · α(g_x)^(s-1) dμ(x),
  ```

  where `g_x = lift x` is a chosen invertible matrix with last row `x`. The
  choice does not matter: by `dens_lastRow`, the integrand at `x = ηg` equals
  `β(ρ(g)v, σ(g)w) α(g)^(s-1)` for every `g`, because two choices differ by a
  left mirabolic factor `p`. The factors `α(p)^(1-s)` (covariance of `β`) and
  `α(p)^(s-1)` then cancel.
* **Backward map** (`bwd`, `bwdFun`, `valueAt`). For an invariant trilinear
  form `B`,

  ```text
  β_B(v, w) = B(v, w, 1_{ηH}) / μ(ηH),
  ```

  where `H` is any compact open subgroup fixing `v` and `w` on which
  `α = 1` (`Good`), and `1_{ηH}` is the indicator of the compact open orbit
  `ηH` (`indS (orbitSet H 1)`). The proof shows that this quotient does not
  depend on `H` (`valueAt_eq`).

### The exponent `1 - s`

The modular factor enters only through the Haar scaling of row space:
`μ(E k⁻¹) = α(k)^(-1) μ(E)`, i.e. `μ.map (· ᵥ* k) = α(k)^(-1) • μ`
(hypothesis `hscale`, discharged by the published
`HarmonicAnalysis.haarMeasure_map_matrix`). Then:

* `fwdForm_invariant`: substituting `x ↦ xk` gives the factor `α(k)^(-1)`.
  The density transforms with `α(k)^(1-s)` (`dens_translate`), so `B_β` has
  weight `α(k)^(1-s) α(k)^(-1) = α(k)^(-s)`.
* `bwdFun_mirabolic`: for `p` mirabolic, the subgroup `pHp⁻¹` is good for
  `(ρ(p)v, σ(p)w)`, and `1_{η pHp⁻¹}` is the right translate of `1_{ηH}` by
  `p`. Hence the numerator gains `α(p)^(-s)` and the mass gains
  `α(p)^(-1)`, so `β_B` has covariance `α(p)^(-s) / α(p)^(-1) = α(p)^(1-s)`.

This is the shift of JPSS (2.10.5)–(2.10.6): their `δ_P = α`, and an
invariant pairing with `δ_P^{-1}` amounts to `α^(1-s)` covariance after the
twist `α^s` is removed.

## Generic construction

All constructions are carried out in the namespace
`Langlands.RankinSelberg.EqualRankFrobenius` over an arbitrary Hausdorff
topological field `K` (`[Field K] [TopologicalSpace K]
[IsTopologicalDivisionRing K] [T2Space K]`), with:

* a Borel measurable structure on `Fin (n+1) → K` and an additive Haar
  measure `μ` on it;
* an absolute value `abv` and a map `χ : K →*₀ ℝ≥0` with
  `(χ a : ℝ) = abv a` (`hχ`), and the scaling law
  `μ.map (fun x => x ᵥ* k) = (χ (det k))⁻¹ • μ` for every `k` (`hscale`);
* `hgood : ∀ v w, ∃ H, Good abv ρ σ v w H`, derived in `exists_good` from
  smoothness, openness of `{g | abv (det g) = 1}` and the existence of a
  compact open subgroup.

The generic result is
`EqualRankFrobenius.frobeniusEquiv : SourceSpace abv ρ σ s ≃ₗ[ℂ]
TargetSpace abv ρ σ s`. `SourceSpace` and `TargetSpace` are abbreviations for
exactly the `invariantForms` and `InvariantBilinear.forms` spaces of the
statement.

### Geometry of the nonzero-row orbit (section `Geometry`)

* `exists_lastRow_eq`, `lift`, `lastRow_lift`: every nonzero row is the last
  row of an invertible matrix, constructed by replacing a row of the identity
  and permuting it to the last position (`Matrix.det_updateRow_sum`,
  `Matrix.det_permute`).
* `mul_inv_mem_mirabolic_of_lastRow_eq`, `lastRow_mirabolic_mul`: the fibres
  of the last-row map are exactly the left mirabolic cosets.
* `orbitSet H g = {η g h : h ∈ H}` with `orbitSet_mul_right`,
  `orbitSet_eq_of_lastRow_eq` and `orbitSet_eq_of_mem_inter` (two orbits that
  meet coincide). `conj k H = kHk⁻¹` with `mem_conj`, `conj_conj_inv`.
* `preimage_vecMul_orbitSet`: the preimage of `orbitSet H g` under `x ↦ xk`
  is `orbitSet (conj k H) (g k⁻¹)`. `orbitSet_conj_mirabolic`: for `p`
  mirabolic, `orbitSet (conj p H) p⁻¹ = orbitSet (conj p H) 1`.
* `isOpenMap_lastRow`: the last-row map is open. It uses the published
  `lastRow_image_mem_nhds` at the identity and right translation by
  `rowHomeomorph`. Hence `isOpen_orbitSet` holds for open `H`, and
  `isCompact_orbitSet` holds for compact `H`.

These lemmas carry out the first proof obligation of the statement Markdown
directly on the orbit: surjectivity onto nonzero rows, the fibres, openness,
and right equivariance. No quotient space or global section is needed.

### Test functions vanishing at zero (sections `Indicator`, `Mass`)

* `Splus K n` is `(rowVanishingAtZero (F := K) (n := n + 1)).toSubmodule` and
  `splusRep K n` its published `toRepresentation`; `splusRep_apply` is `rfl`.
* `indS O` is the indicator of a compact open set `O` with `0 ∉ O`, as an
  element of `Splus` (built from the published `compactOpenIndicator`), and
  `0` otherwise. `splusRep_indS_orbitSet` computes its right translate.
* `mass μ : SchwartzBruhat X →ₗ[ℂ] ℂ` is the Haar integral, linear because
  test functions are continuous with compact support. `mass_rowTranslate`
  is the change of variables `integral_map_equiv` combined with `hscale`.
  `mass_indS_orbitSet_ne_zero` holds because a nonempty compact open orbit
  has positive finite measure.

The second obligation (restriction and extension by zero) is replaced by a
direct use of `Splus`. In `isLocallyConstant_mul_dens`, the function
`Φ(x) · density(x)` is locally constant at `x = 0` because `Φ` vanishes near
`0`. At `x ≠ 0` it is locally constant because the density is constant on the
open orbit `orbitSet H (lift x)` of a good subgroup `H`. Its support lies in
the compact support of `Φ`. So `prodS` is again a Schwartz–Bruhat function.
The uniform right stabilizer of a test function comes from the published
`HarmonicAnalysis.rowTestSmooth`.

### Orbit decompositions (section `Decomposition`)

* `core H N = {c | h⁻¹ c h ∈ H ∩ N for all h ∈ H}` is a subgroup normalized
  by `H` (`conj_core`) and contained in `H` and `N`. For `H` compact open and
  `N` open it is open (`isOpen_core`): apply `generalized_tube_lemma` to
  `(h, c) ↦ h⁻¹ c h` on `H × {1}`.
* `exists_card_sum`: for `C ≤ H` open, there is one natural number `N` such
  that every linear functional `l` on `Splus` that takes the same value on all
  `1_{orbitSet C h}` (`h ∈ H`) satisfies
  `l(1_{ηH}) = N · l(1_{ηC})`. Here `ηH` is covered by finitely many
  pairwise disjoint `C`-orbits (compactness, `Finset.indicator_biUnion_apply`).
* `exists_eq_sum_indS`: a function in `Splus` that is right invariant under a
  compact open `H` is a finite linear combination of the indicators of
  pairwise disjoint `H`-orbits.

### Independence of the subgroup and the backward map

`Good abv ρ σ v w H` means that `H` is compact open, fixes `v` and `w`, and
satisfies `abv (det h) = 1` on `H`. It is stable under smaller open subgroups,
sums and scalar multiples of the vectors, and conjugation (`Good.conj`).

`valueAt_eq_of_le` applies `exists_card_sum` twice, with the same `N`, to
`l = B v w` and to `l = mass`. Invariance of `B` and the scaling of `mass`
make both functionals constant on the `C`-orbits when `C` is normalized by
`H`. So both numerator and denominator are multiplied by `N`, and
`N ≠ 0` because the mass is nonzero. `valueAt_eq` compares two good
subgroups `H₁`, `H₂` through `C = core H₁ H₂` and `C' = core H₂ C`.

`goodChoice` picks a good subgroup by choice, and `bwdFun B v w` is
`valueAt` at it. By independence, `bwdFun` may be evaluated at any good
subgroup (`bwdFun_eq`). This gives bilinearity (`bwdFun_add_left`, …, using
a common good subgroup `H₁ ⊓ H₂`) and the mirabolic covariance
`bwdFun_mirabolic`. Thus `bwd` is a linear map from `SourceSpace` to
`TargetSpace`.

### Forward map and inverse laws

* `dens β v w x = β(ρ(lift x)v)(σ(lift x)w) · determinantWeight abv (lift x)
  (s - 1)`, with `dens_lastRow` and `dens_translate` as above.
* `prodS β v w Φ` is `Φ · dens` as a Schwartz–Bruhat function. `fwdForm β`
  is `(v, w, Φ) ↦ mass μ (prodS β v w Φ)`, trilinear by the pointwise
  identities `prodS_add_left`, …, `prodS_smul_test`. `fwd` is linear in `β`.
* `bwdFun_fwdForm`: on the orbit `ηH` of a good `H`, the density is the
  constant `β v w`. So `prodS β v w 1_{ηH} = β(v,w) · 1_{ηH}`, and
  `bwd ∘ fwd = id`.
* `eq_zero_of_bwdFun_eq_zero`: if all backward values of an invariant `B`
  vanish, then `B = 0`. Given `v`, `w`, `Φ`, take a good `H` that also
  stabilizes `Φ` (`rowTestSmooth`), decompose `Φ` into `H`-orbit indicators
  (`exists_eq_sum_indS`), and write each `1_{orbitSet H g}` as the right
  translate by `g⁻¹` of `1_{η gHg⁻¹}`. The value of `B` there is a multiple of
  `bwdFun B (ρ(g)v) (σ(g)w) = 0`.
* `fwdForm_bwd`: `fwd (bwd B) - B` is invariant and its backward values
  vanish by `bwdFun_fwdForm`, hence it is zero. So `fwd ∘ bwd = id`.
* `frobeniusEquiv` is `LinearEquiv.ofLinearMap bwd fwd` with these two
  inverse laws.

This completes the fourth obligation: explicit bilinear Frobenius maps, their
linearity, and both inverse laws. The curried-form comparison is built in,
because both spaces consist of curried linear maps, and no tensor product is
formed.

## Instantiation for the supplied p-adic field

In `equalRankFrobenius`, the topology, valuation and local-field structure
come from `T`. Hausdorffness comes from `T.fieldT2` and second countability
from `T.secondCountableTopology`. The Borel structure on `F.Carrier` is
installed, and row space carries the product structure. Then:

* `μ = Measure.addHaar` on `Fin (n+1) → F.Carrier`.
* `χ = T.normalizedAbsHom`, whose real coercion is `normalizedAbsoluteValue T`
  by definition. The scalar law
  `addHaar.map (a * ·) = (T.normalizedAbsHom a)⁻¹ • addHaar` for `a ≠ 0` is
  the published `HarmonicAnalysis.padicScalarHaarScaling`.
* `hscale` is `HarmonicAnalysis.haarMeasure_map_matrix` applied to the
  transpose `kᵀ`, using `Matrix.toLin'_apply`, `Matrix.mulVec_transpose`
  (`kᵀ *ᵥ x = x ᵥ* k`) and `Matrix.det_transpose`. This is the third
  obligation: the modular factor of the source is matched with the supplied
  normalized absolute value, through this Haar-scaling identity.
* `{g | abv (det g) = 1}` is the kernel of `T.determinantNorm (n+1)`, which is
  open by `T.isOpen_ker_determinantNorm`.
* The compact open subgroup is
  `GeneralLinearGroup.integralSubgroup (Fin (n+1)) T.Integers`, open and
  compact by `isOpen_integralSubgroup` and `isCompact_integralSubgroup`
  together with `T.isOpen_integers` and `T.isCompact_integers`.

`exists_good` then provides `hgood` from `IsSmooth ρ` and `IsSmooth σ`, and
`frobeniusEquiv` gives the required `Nonempty` equivalence.

## Sources

The target, its normalization and the source correspondence are documented
in the statement's Markdown. It cites JPSS 1983 (`jpss-1983-rankin-selberg`),
printed pp.376–378, p.380 (1.3) and p.397 (2.10.5)–(2.10.6), and BZ76
(`bernstein-zelevinsky-1976-representations-gln`), pp.23–24. In JPSS p.397,
the map `g ↦ η_r g` identifies `P\G` with `F^r − {0}` and `S⁺` with
`C_c^∞(P\G)`. Frobenius reciprocity then identifies the space (5) of
invariant pairings on the induced side (the Lean `SourceSpace`, invariant
trilinear forms on `S⁺`) with the space (6) of mirabolic covariant bilinear
forms, `Bil_P(π ⊗ α^{s-1}|P, π'|P)` (the Lean `TargetSpace`). The Lean proof
implements this reciprocity concretely. Integration against Haar measure on
the orbit is the map `fwd : TargetSpace →ₗ[ℂ] SourceSpace`, from mirabolic
bilinear forms to invariant trilinear forms on `S⁺`; this is the direction
of the explicit integral in BZ76, p.24, Proposition 2.29. Normalized
evaluation at small orbit indicators is the reverse map
`bwd : SourceSpace →ₗ[ℂ] TargetSpace`, and the two are mutually inverse.
The modular character `δ_P = α` appears as the Haar scaling
`α(k)^(-1)`. This is a different but complete proof of the exact target. It
uses no Whittaker, admissibility, finite-length or irreducibility hypotheses,
and no supplied reciprocity theorem.
