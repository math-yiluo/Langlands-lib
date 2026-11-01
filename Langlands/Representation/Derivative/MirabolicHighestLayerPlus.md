# The highest mirabolic layer as an iterated plus induction

Module `Langlands.Representation.Derivative.MirabolicHighestLayerPlus`.

Author: Worker 805. The module uses the maps `phiPlusPost` and `psiPlusBaseEmbedding`
of Worker 1185's published helper `MirabolicHighestLayerPlusMaps`; see
[Authorship](#authorship).

This is the second of three modules proving the actual highest mirabolic layer for
task `3826dc7b-ec07-4059-9425-ee376ebcf07b`. It proves that, for a smooth
representation `B` of `P_(m+2)`, the orbit map `w ↦ (x ↦ [x·w])` is an isomorphism of
representations from the radical relations `R(B)` onto the published normalized
`Φ⁺(Φ⁻ B)`. As a consequence, one lifting step `liftStep` of
`MirabolicHighestLayerLift` is the range of an injective intertwining map from `Φ⁺` of
the source of any injective map into `Φ⁻ B` (`exists_plusStep`). The module
`MirabolicHighestLayerProof` iterates this to identify the layer with an embedded
`(Φ⁺)^(k-1) Ψ⁺ (A^(k))`.

All declarations live in namespace `Langlands.Derivative.Mirabolic.HighestLayer` and
are internal to this proof. Unqualified names refer to that namespace.

## Notation and the published plus functor

Notation is as in `MirabolicHighestLayerLift.md`: `P_(m+2) = mirabolic (m+1) F.Carrier`,
radical elements `radicalElement c`, `levi`, `successor`, `projection` (the Levi part,
in `GL_(m+1)`), the radical relations `R(B)` and the quotient map
`q = phiMinusQuotient T ψ m B : B → Φ⁻ B`. Further:

- `Q = plusSubgroup m F.Carrier ⊆ P_(m+2)` is the preimage of `P_(m+1)` under
  `projection`, with `plusProjection : Q → P_(m+1)` (published
  `MirabolicProjection`, Worker 749), and `thetaPlus ψ m` is the published character
  `q ↦ ψ(q_(m+1,m+2))` of `Q` (published `MirabolicPlus`, Worker 723).
- For a smooth representation `τ` of `P_(m+1)`, the published normalized
  `(phiPlus T ψ m).obj τ` (`MirabolicPlusNormalization`, Worker 984) is the space of
  smooth functions `f : P_(m+2) → τ`, compactly supported modulo `Q`, with
  `f(q x) = thetaPlus(q) · phiPlusCharacter(pq) · (pq)·f(x)` for `q ∈ Q`, `pq` its
  `plusProjection`, and `phiPlusCharacter = |det|^(1/2)`; the group acts by right
  translation. Vectors are built with `phiPlusNormalizedMk` from such a function, an
  open subgroup of right stabilizers and compactness of the projected support, and
  read with `phiPlusNormalizedEval`.
- `projectionRow x` is the last row of `projection x`.

## Conjugation and the orbit function (section `Orbit`)

- `mul_radicalElement`: `x · radicalElement c = radicalElement(projection(x)·c) · x`.
- `orbitFun B w x = q(x·w) ∈ Φ⁻ B` (`orbitFun_apply`).
- `orbitFun_mul`: `f_w(x g) = f_(g·w)(x)`.
- `orbitFun_radicalElement`: `f_(u_c·w)(x) = ψ(projectionRow(x)·c) · f_w(x)` for
  `u_c = radicalElement c`, from `mul_radicalElement` and the `θ`-coinvariance of `q`.
- `orbitFun_plus_mul`: for `q ∈ Q`, `q = radicalElement(lastColumn q) · successor(plusProjection q)`
  inside `P_(m+2)`, so `f_w(q x)` is `ψ` of the corner entry times `q` of the
  successor translate.
- `phiMinus_orbitFun` rewrites that successor translate with the published
  `phiMinus_action`, and `phiPlusCharacter_smul_phiMinusCharacter_smul` cancels the
  two determinant twists using the published
  `phiPlusCharacter_mul_phiMinusCharacter` (`|det|^(1/2) · |det|^(-1/2) = 1`).
- `orbitFun_covariant`: `f_w(q x) = thetaPlus(q) · phiPlusCharacter(pq) · (pq)·f_w(x)`.
  This is exactly the covariance of normalized `Φ⁺(Φ⁻ B)`: the `-1/2` twist of `Φ⁻`
  and the `+1/2` twist of `Φ⁺` cancel.
- Linearity in `w`: `orbitFun_add`, `orbitFun_smul`, `orbitFun_zero`, `orbitFun_sub`,
  `orbitFun_sum`.

## Last rows (section `Row`)

- `projectionRow_mul` (`row(x y) = row(x) ·ᵥ projection(y)`), `projectionRow_plus_mul`
  (`row(q x) = row(x)` for `q ∈ Q`, from the published
  `EqualRankFrobenius.lastRow_mirabolic_mul`), `projectionRow_levi`,
  `projectionRow_ne_zero` (the last row of an invertible matrix is nonzero) and
  `mulVec_last_eq_dotProduct`.
- `exists_plus_mul_levi`: if `row(x)` is the last row of `g ∈ GL_(m+1)`, then
  `x ∈ Q · levi g` (published `EqualRankFrobenius.mul_inv_mem_mirabolic_of_lastRow_eq`).

## Supports (section `Support`)

- `exists_openSubgroup_fixing` and `exists_latticeBox_fixing`: a vector `w` is fixed by
  an open subgroup and by a radical lattice box `l`.
- `projectionRow_mem_of_orbitFun_ne_zero`: if `w` is fixed by the radical box `l` and
  `f_w(x) ≠ 0`, then `row(x)` lies in the dual box of exponent `cond(ψ) - l`: by
  `orbitFun_radicalElement`, `ψ(row(x)·c) = 1` for all `c` in the box (published
  `mem_latticeBox_of_forall_character_eq_one`).
- `exists_orbitFun_eq_zero_of_mem_relations`: for `w ∈ R(B)` there is `N` with
  `f_w(x) = 0` whenever `row(x)` lies in the box `N`. By span induction: for a
  generator `u_c·v - v`, `f(x) = (ψ(row(x)·c) - 1) · f_v(x)`, which vanishes for small
  `row(x)`.
- `isCompact_quotientSupport_of_projectionRow`: a function on `P_(m+2)` whose zero set
  is left `Q`-stable, which is right invariant under an open subgroup `K`, and whose
  support has rows in a compact set `C ∌ 0`, has compact projected support in
  `Q \ P_(m+2)`. The support is closed by right `K`-invariance. For the compact open
  `J = GL_(m+1)(O)` (published `GeneralLinearGroup.integralSubgroup`), the open sets
  `EqualRankFrobenius.orbitSet J (lift y)` of last rows of `lift y · J`, `y ∈ C`
  (`isOpen_orbitSet`), cover `C`; finitely many suffice. So the support lies in
  finitely many sets `Q · levi(lift y · J)` (`exists_plus_mul_levi`), each with
  compact image in the quotient.

## The orbit map (section `Theta`)

- `mem_liftStep_top`: `liftStep ⊤ = R(B)` as sets.
- `orbitFun_isCompact`: for `w ∈ R(B)`, `f_w` has compact projected support, with
  rows in `C = box(cond(ψ) - l) \ box N`.
- `thetaFun` (`thetaFun_eval`): `f_w` as a vector of normalized `Φ⁺(Φ⁻ B)`, built
  with `phiPlusNormalizedMk` from `orbitFun_covariant`, the stabilizer of `w` and
  `orbitFun_isCompact`.
- `theta B : R(B) → Φ⁺(Φ⁻ B)` (`theta_eval`), an intertwining map from the
  representation on `liftStep ⊤` by `orbitFun_mul`.
- `liftStep_bot`: `liftStep ⊥ = ⊥` (from `liftStep_imageStep` and `imageStep_bot`).
- `theta_injective`: if `f_w = 0`, every translate of `w` has class `0`, so
  `w ∈ liftStep ⊥ = ⊥`.

## Surjectivity (section `Surjective`)

Let `φ ∈ Φ⁺(Φ⁻ B)`.

- `sum_character_out`: for lattice boxes `box(l) ⊆ box(M)` of rank `k` and a row
  `y ∈ box(cond(ψ) - l)`, the sum of `ψ(y·c)` over representatives `c` of
  `box(M)/box(l)` is `|box(M)/box(l)|` if `y ∈ box(cond(ψ) - M)` and `0` otherwise
  (published `sum_out_eq_zero` for the nontrivial character).
- `exists_orbitFun_eq_near`: for every nonzero row `y` there are `w ∈ B` and an open
  neighbourhood of `y` on which `φ` agrees with `f_w`: take `x₀ = levi(g)` with last
  row `y`, a vector `w₀` with `q(w₀) = φ(x₀)`, and `w = x₀⁻¹·w₀`. Both functions are
  `Q`-covariant (`orbitFun_covariant`, `phiPlusNormalizedEval_covariant`) and right
  invariant under `J = levi⁻¹(K_φ) ∩ levi⁻¹(K_w)`, so they agree on the orbit set
  `Q·x₀·J`, which is the set of `x` whose row lies in an open neighbourhood of `y`
  (`exists_plus_mul_levi`).
- `exists_cutoff`: for `w`, a row `z` and a box `r` with `z ∉ box(r)` (so the coset
  `z + box(r)` avoids `0`),
  the Fourier cutoff `w' = |G/L|⁻¹ Σ_(c ∈ G/L) ψ(-z·c) · u_c·w` over a quotient of
  radical boxes lies in `R(B)`, because its coefficients sum to `0`; and
  `f_(w')(x)` is `f_w(x)` when `row(x) - z ∈ box(r)` and `0` otherwise
  (`orbitFun_radicalElement`, `sum_character_out`).
- `exists_compact_rows`: the rows of the support of `φ` lie in a compact set `C ∌ 0`,
  the image of the compact projected support under the continuous row map, which is
  well defined on `Q \ P_(m+2)` by `projectionRow_plus_mul` and nonzero by
  `projectionRow_ne_zero`.
- `exists_relation_orbitFun_eq`: cover `C` by finitely many neighbourhoods from
  `exists_orbitFun_eq_near`, contain `C` in a box `N₁`, and take a box `r` small enough
  that each coset of `box(r)` meeting `C` lies in one neighbourhood and avoids `0`.
  The sum of the cutoffs of the corresponding `w` over the finitely many cosets of
  `box(r)` in `box(N₁)` meeting `C` is a vector `w ∈ R(B)` with `f_w = φ`.
- `theta_surjective`: hence `theta` is surjective.

## One plus step (section `OneStep`)

- `relationsSubtype` (`relationsSubtype_apply`): the inclusion `R(B) → B` as an
  intertwining map.
- `thetaInv`: the inverse of the bijective `theta`, with `theta_thetaInv` and
  `thetaInv_theta`.
- `exists_phiPlusPost_eq_of_mem`: if `v ∈ R(B)` and every class `q(x·v)` lies in the
  range of an injective `E : τ → Φ⁻ B`, then `theta v` lies in the range of
  `phiPlusPost E` (Worker 1185's `mem_range_phiPlusPost`).
- `plusStepMap B E hE = relationsSubtype ∘ thetaInv ∘ phiPlusPost E hE`, an
  intertwining map `Φ⁺ τ → Φ⁺(Φ⁻ B) ≅ R(B) ⊆ B` (`plusStepMap_apply`), injective
  (`plusStepMap_injective`), with `mem_range_plusStepMap`: its range is
  `liftStep T ψ m B E.range`.
- `exists_plusStep`:

```lean
theorem exists_plusStep :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      {τ : SmoothRep.{0, uF, uW} ℂ (mirabolic m F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation
        ((phiMinus T ψ m).obj B).representation),
      Function.Injective E →
        ∃ E' : Representation.IntertwiningMap ((phiPlus T ψ m).obj τ).representation
            B.representation,
          Function.Injective E' ∧ E'.range = liftStep T ψ m B E.range
```

The carrier universe `uW` of `τ` is independent of `uV`; `Φ⁺ τ` lands in
`max uF uW`.

## Sources

Bernstein–Zelevinsky 1977 (literature ID `bernstein-zelevinsky-1977-induced-i`,
SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`), §3.2,
printed p.451, PDF page 12: `Φ⁺` is normalized compact induction from `Q` twisted by
`θ`, and the exact sequence 3.2(e) `0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0` identifies `Φ⁺Φ⁻ B`
with the kernel `R(B)` of `B → Ψ⁺Ψ⁻ B`; §1.8 (printed p.444, PDF page 5) fixes the
`mod^(±1/2)` normalizations. The Lean statements are the derived form of 3.2(e) at
one representation: `theta` is an isomorphism `R(B) ≅ Φ⁺(Φ⁻ B)` given by the explicit
orbit map. The implemented proof differs from BZ77's (which uses l-sheaves and the
adjunctions): it proves compact support, injectivity and surjectivity directly by
last-row supports, lattice-box character sums and Fourier cutoffs. The normalization
of `phiPlus` itself is not reproved here; the covariance check above uses only the
published identity `phiPlusCharacter · phiMinusCharacter = 1`, and
`MirabolicHighestLayerLift.md` compares `phiMinusCharacter` with BZ77's `mod^(-1/2)`.

## Imports

- `Langlands.Representation.Derivative.MirabolicHighestLayerLift` (`liftStep`,
  `imageStep`, the lattice comparison);
- `Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps` (Worker 1185:
  `phiPlusPost`, `mem_range_phiPlusPost`);
- `Langlands.Representation.Derivative.MirabolicPlusNormalization` (Worker 984:
  normalized `phiPlus`, `phiPlusNormalizedMk`, `phiPlusNormalizedEval`,
  `phiPlusCharacter_mul_phiMinusCharacter`);
- `Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof` (last-row lemmas,
  `lift`, `orbitSet`, `isOpen_orbitSet`, `isOpenMap_lastRow`; through its imports also
  the compact open `GeneralLinearGroup.integralSubgroup` of `IntegralSubgroup`).

The complete import and declaration closures of the three modules are listed in
`MirabolicHighestLayerProof.md`.

## Authorship

Worker 805 wrote this module. Worker 1185 wrote the imported helper
`MirabolicHighestLayerPlusMaps` (postcomposition `phiPlusPost` and the base embedding
`psiPlusBaseEmbedding`), to a split of the work agreed with Worker 805 for this task,
and reviewed the normalization comparison. Worker 1185 is credited as coauthor of the
submission.
