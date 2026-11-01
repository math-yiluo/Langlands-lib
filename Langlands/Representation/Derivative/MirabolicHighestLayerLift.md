# Lifting invariant subspaces through one `Φ⁻` step

Module `Langlands.Representation.Derivative.MirabolicHighestLayerLift`.

Authors: Worker 805 and Worker 806. Worker 805 wrote the module. The averaging
lemma `exists_levi_translates_mem` adapts Worker 806's published proof of
`eq_bot_or_eq_top_of_radicalQuotient`; see [Authorship](#authorship).

This is the first of three modules proving the actual highest mirabolic layer for task
`3826dc7b-ec07-4059-9425-ee376ebcf07b`:

1. this module builds one lifting step through `Φ⁻` and proves the one-step lattice
   comparison, the base step and the level bounds;
2. `Langlands.Representation.Derivative.MirabolicHighestLayerPlus` identifies one
   lifting step with the published normalized `Φ⁺`;
3. `Langlands.Representation.Derivative.MirabolicHighestLayerProof` assembles the layer
   by induction and proves the target theorem `Langlands.Derivative.mirabolicHighestLayer`.

All declarations here live in namespace `Langlands.Derivative.Mirabolic.HighestLayer`
and are internal to this proof. Unqualified names below refer to that namespace. The
module states no theorem from the literature by itself; its lemmas are the
invariant-subspace form of Bernstein–Zelevinsky 1977 §3.2(e) and §3.3(a) (see
[Sources](#sources)).

## Notation

`mirabolic n F.Carrier` is `P_(n+1)`. Its radical `V` (Lean: `radical n F.Carrier`)
consists of the matrices `radicalElement c` with last column `(c,1)`, `c : Fin n → F`.
Its Levi factor is `GL_n`, embedded by `levi g = diag(g,1)`. The map
`successor = levi ∘ subtype : P_(n+1) → P_(n+2)` embeds one mirabolic in the next.
For `B` a representation of `P_(m+2)`, define:

- `R(B) = relations B.representation (radical (m+1) F.Carrier) 1`, the span of the
  vectors `u·v - v` for `u ∈ V`;
- `R_θ(B)`, the analogous span of `u·v - θ(u)v` for the published character
  `T.mirabolicTheta ψ m`, whose value on `radicalElement c` is `ψ(c_last)`;
- `Ψ⁻ B = (psiMinus T (m+1)).obj B`, the coinvariants `B / R(B)` with quotient map
  `psiMinusQuotient`, a representation of `GL_(m+1)`;
- `Φ⁻ B = (phiMinus T ψ m).obj B`, the coinvariants `B / R_θ(B)` with quotient map
  `q = phiMinusQuotient T ψ m B`, a representation of `P_(m+1)`.

`isOpen_ker_one` records that the trivial character of the radical has open kernel,
the hypothesis under which the published relation lemmas apply to `R(B)`.

All of these are the published functors of `MirabolicMinus`. Both carry the
determinant twist `|det|^(-1/2)` (see [Normalization](#normalization)).

## One step: lifting and taking images (section `Step`)

Let `B` be a smooth representation of `P_(m+2)`.

- `liftStep T ψ m B X`, for an invariant subspace `X` of `Φ⁻ B`, is the set of
  `v ∈ R(B)` whose translates all have classes in `X`:
  `∀ g ∈ P_(m+2), q(g·v) ∈ X` (`mem_liftStep`). It is an invariant subspace of `B`,
  and it lies in `R(B)` by construction. Stability of `R(B)` comes from the published
  `radicalRelations_stable`.
- `imageStep T ψ m B W`, for an invariant subspace `W` of `B`, is `q(W)`. It is
  invariant: by the published formula `phiMinus_action`,
  `h·q(v) = |det h|^(-1/2) q(successor h · v)`, and `W` is stable under successor
  translates. `mem_imageStep`: `x ∈ imageStep W ↔ ∃ v ∈ W, q(v) = x`.
- `successor_mem`: if `q(v) ∈ X` then `q(successor h · v) ∈ X`, because the
  determinant factor is a unit.

## The one-step lattice comparison

### Element-level left exactness

`mem_relations_subrepresentation`: let `S` be an invariant subspace of a smooth `A`
and `χ` a character of the radical with open kernel. A vector `v ∈ S` that lies in
the ambient relations `R_χ(A)` already lies in `R_χ(S)`, the relations of the
subrepresentation. For `n = 0` the radical is trivial and `R_χ(A) = 0`. For a positive
rank the proof applies the published `CharacterAveraging.apply_eq_zero_of_mem_relations`
(Worker 831). The exhaustion uses the compact radical boxes of the published
`MinusVanishing.radicalBox`; every point lies in one of them by `exists_mem_latticeBox`.
The argument shows that every linear functional on the `χ`-coinvariants of `S` kills
the class of `v`.

Consequences:

- `phiMinus_map_subtype_injective` and `psiMinus_map_subtype_injective`: `Φ⁻` and `Ψ⁻`
  of the inclusion `S ↪ A` are injective.
- `range_phiMinus_map_subtype` and `phiMinusSubIso`:
  `Φ⁻(S) ≅ imageStep S` as subrepresentations of `Φ⁻ A`, through the published
  `LevelCalculus.isoRange`.

This is the only exactness used: element-level left exactness for invariant subspaces,
proved in this module. The published `MinusExactnessStatement` is never used as a
hypothesis or a theorem (see the exclusions section of `MirabolicHighestLayerProof.md`).

### Averaging

`exists_levi_translates_mem` is stated abstractly for a representation `ξ` of
`P_(m+2)`, a linear map `q : V → W` and a subspace `σ ⊆ W`. It assumes that `q`
transforms radical elements by `ψ(c_last)`, that `σ` is stable under successor
translates of representatives, and that `S` is an invariant subspace. Given `x ∈ S`
with `q(x) ∈ σ`, it produces `x'' ∈ S` with `q(x'') = q(x)` and
`q(levi g · x'') ∈ σ` for every `g ∈ GL_(m+1)`.

The proof runs as follows. Choose an open compact `K` fixing `x` and set
`J = levi⁻¹(K)`. Choose a lattice box `n₀` of last-row perturbations realized by
elements of `J`, using the published `lastRow_image_mem_nhds`, and a box `l` of
radical coordinates fixing `x`. Average over the finite quotient `B/L` of the boxes
`M = max(l, cond(ψ) - n₀)` and `l`:
`x' = Σ_{c ∈ B/L} ψ(-c_last) · radicalElement(c)·x`. Conjugating radical elements past
`levi g` gives `q(levi g · x') = (Σ_c χ_g(c)) · q(levi g · x)` with
`χ_g(c) = ψ((g c)_last - c_last)`.

- If the last row of `g` is close to that of `1`, meaning it pairs trivially with
  the lattice `M`, then it lies in the last-row image of `J`. By the published
  `lastRow_mem_image_iff`, `g = a·j` with `a ∈ P_(m+1)` and `j ∈ J`. Hence
  `q(levi g · x) = q(successor a · levi j · x) = q(successor a · x) ∈ σ`.
- Otherwise the character `χ_g` is nontrivial on `B/L`. It is trivial on `L` whenever
  `q(levi g · x) ≠ 0`, so the sum vanishes by the published `sum_out_eq_zero`.

Taking `g = 1` gives `q(x') = |B/L| · q(x)`, and `x'' = |B/L|⁻¹ x'`. The averaged
vector is a combination of translates of `x`, so it stays in `S`.

### Lift and image are inverse

- `exists_radical_difference`: there are a fixed `u₀ ∈ V` and `c ∈ ℂ` with
  `q(c(u₀·v - v)) = q(v)` for all `B` and `v`. Take
  `u₀ = radicalElement(t·e_last)` with `ψ(t) ≠ 1` and `c = (θ(u₀) - 1)⁻¹`.
- `exists_mem_liftStep`: if `b ∈ S` and `q(b) ∈ X`, there is `s ∈ liftStep X ∩ S`
  with `q(s) = q(b)`. Averaging gives `x ∈ S`. Every `g ∈ P_(m+2)` factors as
  `radicalElement(·) · levi(projection g)` (published `eq_radicalElement_mul_levi`),
  so `q(g·x) ∈ X` for all `g`. Then `s = c(u₀·x - x)` lies in `R(B)`, has all
  translates in `X`, lies in `S`, and has `q(s) = q(x) = q(b)`.
- `imageStep_liftStep`: `imageStep (liftStep X) = X`. For `⊆` take `g = 1`; for `⊇`
  apply `exists_mem_liftStep` with `S = ⊤`.
- `liftStep_imageStep`: if `W ⊆ R(B)` is invariant, then `liftStep (imageStep W) = W`.
  `le_liftStep_imageStep` gives `⊇`. For `⊆`, let `L` be the lift, `D` the
  representation on `L`, and `Z = D/W`. Then:
  - `Ψ⁻ Z = 0`: every `y ∈ L` lies in `R(B)`, hence in `R(D)` by element-level left
    exactness, and `Ψ⁻` is functorial on the quotient map (`psiMinus_map_quotient`).
  - `Φ⁻ Z = 0`: for `y ∈ L` there is `w ∈ W` with `q(w) = q(y)`. Then `y - w ∈ R_θ(B)`,
    hence `y - w ∈ R_θ(D)`, and `w ↦ 0` in `Z`.

  The published `MinusVanishing.subsingleton_of_psiMinus_phiMinus` (Worker 1025) then
  gives `Z = 0`, so `L ⊆ W`. That theorem is the analytic input: a smooth `P_(m+2)`
  representation with vanishing `Ψ⁻` and `Φ⁻` is zero.
- `stepIso`: `Set.Iic (liftStep X) ≃o Set.Iic X`, given by `imageStep` with inverse
  `liftStep`. Everything below a lift lies in `R(B)`, and both maps are monotone
  (`liftStep_mono`, `imageStep_mono`).
- `inf_imageStep_ne_bot_iff`: `X ⊓ imageStep S ≠ ⊥ ↔ liftStep X ⊓ S ≠ ⊥`. The forward
  direction uses `exists_mem_liftStep`. The backward direction applies
  `liftStep_imageStep` to `liftStep X ⊓ S`, whose image lies in `X ⊓ imageStep S`.

Order bookkeeping in section `Lattice`: `ne_bot_iff_exists` (a subrepresentation is
nonzero exactly when it has a nonzero vector), `liftStep_mono`, `imageStep_mono` and
`imageStep_bot`.

## The base step: `Ψ⁻` when the radical acts trivially

- `radical_trivial_of_level_le_one`: if `level T ψ A ≤ 1`, the radical acts trivially.
  For `N = 0` the radical of `P_1` is trivial (published `radical_acts_trivially_zero`).
  For `N = M+1`, the published `LevelCalculus.nontrivial_phiMinus_iff`
  (`Nontrivial (Φ⁻A) ↔ 1 < level A`) gives `Φ⁻A = 0`. The published
  `radical_acts_trivially_of_phiMinus` (MirabolicHighestDerivativeDescent) then applies.
- `psiMinusQuotient_injective`: with trivial radical action, `R(A) = 0` (published
  `relations_one_eq_bot`), so the quotient map to `Ψ⁻ A` is bijective.
- Helpers: `nontrivial_iff_of_bijective` (a bijection preserves nontriviality),
  `nontrivial_subrepresentation_iff` (the representation on `S` is nontrivial exactly
  when `S ≠ ⊥`) and `radical_trivial_subrepresentation` (trivial radical action passes
  to invariant subspaces).
- `psiIso`: `Subrepresentation A ≃o Subrepresentation (Ψ⁻ A)` by image
  (`psiImage`) and preimage (`psiPreimage`). Preimage invariance uses
  `g = radicalElement(·) · levi(projection g)`.

## Levels of invariant subspaces (section `Levels`)

- `radical_trivial_of_level_le_one` is described in the base step above.
- `hasNonzeroDerivative_one_of_subrepresentation`: if an invariant subspace `S` of `A`
  has a nonzero derivative of order one, so does `A`. This is
  `psiMinus_map_subtype_injective`: `Ψ⁻ S` embeds into `Ψ⁻ A`.
- `hasNonzeroDerivative_of_subrepresentation`: the same for every order. The proof is
  by induction on the order and the rank, using
  `LevelCalculus.hasNonzeroDerivative_succ_iff` (a nonzero derivative of order `k+1`
  is a nonzero derivative of order `k` of `Φ⁻`) and `phiMinusSubIso`
  (`Φ⁻ S ≅ imageStep S ⊆ Φ⁻ A`), transported by `LevelCalculus.nontrivial_iff_of_iso`.
- `level_subrepresentation_le`: `level T ψ S ≤ level T ψ A` for every invariant
  subspace `S`. `level` is a `Nat.findGreatest` over the same range of orders, so this
  follows from the previous lemma.

## Normalization

The published minus functors twist the unnormalized coinvariant actions by explicit
residue-normalized determinant characters at exponent `-1/2`:
`psiMinusCharacter T n = |det|^(-1/2)` on `GL_n` and
`phiMinusCharacter T n = |det ∘ subtype|^(-1/2)` on `P_(n+1) ⊂ GL_(n+1)`.
They act by `g·[v] = |det g|^(-1/2)[levi g · v]` (`psiMinus_action`) and
`h·[v] = |det h|^(-1/2)[successor h · v]` (`phiMinus_action`).

**Source normalization.** The registered original, Bernstein–Zelevinsky 1977, printed
p.444 (one-based PDF page 5), was visually checked from the rendered page. In §1.7, the
module of an automorphism `σ` of `U` is defined by
`∫_U f(σ⁻¹u) dμ(u) = mod_U(σ) ∫_U f(u) dμ(u)` for a Haar measure `μ`. For `g`
normalizing `U`, `mod_U(g)` is the module of `u ↦ g u g⁻¹`. In §1.8(b), `r_{U,θ}(E)`
carries the action `δ(m)(ξ + E(U,θ)) = mod_U^(-1/2)(m)·(π(m)ξ + E(U,θ))`. In §3.2,
`Ψ⁻ = r_{V,1}` (with `M = G_(n-1)`) and `Φ⁻ = r_{V,θ}` (with `M = P_(n-1)`), both
normalized this way.

**What the Lean proves (section `Normalization`).** Transport the Haar measure on `V`
to column coordinates `X ∈ Matrix (Fin n) (Fin 1) F` through `radicalElement`. The
identity `∫ f(σ⁻¹u) dμ = mod(σ) ∫ f dμ` then says `μ.map σ⁻¹ = mod(σ) • μ`.

- `levi_inv_conj_column`: `(levi g)⁻¹ · radicalElement(X) · levi g = radicalElement(g⁻¹X)`.
  So for `σ = (u ↦ levi g · u · (levi g)⁻¹)`, the inverse `σ⁻¹` is `X ↦ g⁻¹X` in
  column coordinates. This follows from the published `levi_conjugate_radicalElement`.
- `map_inv_mul_haar`: for every additive Haar measure `μ` on the column space,
  `μ.map (X ↦ g⁻¹X) = |det g| • μ`, with `|·|` the residue-normalized absolute value
  `T.determinantNorm`. This is Worker 110's published `padicRectangularHaarScaling`
  with `r = n`, `s = 1`, `A = g⁻¹`, `B = 1`.
- `map_inv_mul_haar_iff`: a scalar `c : ℝ≥0` satisfies `μ.map (X ↦ g⁻¹X) = c • μ`
  exactly when `c = |det g|`. Uniqueness evaluates both sides on a compact
  neighbourhood of `0`, which has positive finite Haar measure. So the Haar modulus
  of conjugation by `levi g` on `V` is `mod_V(levi g) = |det g|`.
- `psiMinusCharacter_eq_modulus`: if `c` is that modulus for `g ∈ GL_n`, then
  `psiMinusCharacter T n g = c^(-1/2)`.
- `phiMinusCharacter_eq_modulus`: if `c` is the modulus of conjugation by
  `successor h = levi h` on the radical of `P_(n+2)`, with columns of length `n+1`,
  then `phiMinusCharacter T n h = c^(-1/2)`.

So the inherited `|det|^(-1/2)` twists are exactly BZ77's `mod_V^(-1/2)`
normalizations of `r_{V,1}` and `r_{V,θ}`, not just equal up to some other character.
The published functors `psiMinus` and `phiMinus` are therefore BZ77's normalized
`Ψ⁻` and `Φ⁻` on the actual coinvariant quotients.

**Use in the proof.** The lattice arguments use the twist only as a nowhere-zero
scalar character: `imageStep` invariance, `successor_mem`, `psiImage` and
`psiPreimage`. Twisting by such a character changes neither the invariant subspaces,
nor nontriviality, nor kernels. The comparison above shows that the published
normalization is the source's. The declaration closure of `mirabolicHighestLayer` does
not contain the `Normalization` section; its separate closure is listed in
`MirabolicHighestLayerProof.md`.

## Sources

- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive p-adic
  groups I*, Ann. Sci. ÉNS 10 (1977). Literature ID
  `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. Read for this
  module: §1.7–1.8 (printed p.444, PDF page 5, visually checked for the sign of the
  `mod^(-1/2)` normalization), §3.2 (printed p.451, PDF page 12), in particular the
  exact sequence 3.2(e) `0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0`, and §3.3(a) (`Φ⁻` and `Φ⁺` are
  quasi-inverse on representations killed by `Ψ⁻`).

The lemmas here are derived statements, not verbatim source theorems. BZ77 obtains the
lattice comparison from the functors `Φ⁺`, `Ψ⁺` and their adjunctions. This module
proves the invariant-subspace version directly: `liftStep` and `imageStep` are inverse
order isomorphisms, by the averaging argument and the published vanishing theorem
`subsingleton_of_psiMinus_phiMinus`. The next module identifies `liftStep` with the
image of the published normalized `Φ⁺`.

## Imports

- `Langlands.Representation.Derivative.MirabolicHighestLayerStatement` (the target
  statement and `level`, `IsHomogeneous`, `mirabolicDerivativeOfOrder`);
- `Langlands.Representation.Derivative.LevelCalculus`;
- `Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing`;
- `Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent`;
- `Langlands.Representation.Derivative.MirabolicLatticeBox`;
- `Langlands.Group.GL.MirabolicProjection`;
- `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof` (used only by section
  `Normalization`).

The complete import and declaration closures of the three modules are listed in
`MirabolicHighestLayerProof.md`.

## Authorship

Worker 805 wrote this module. The averaging lemma `exists_levi_translates_mem` adapts
the averaging argument of Worker 806's published proof of
`eq_bot_or_eq_top_of_radicalQuotient` (`MirabolicMinusIrreducibleProof`, not imported): the
same choice of an open compact fixer, last-row boxes and the character-sum
cancellation `sum_out_eq_zero`, here applied to a subspace `σ` and an invariant
subspace `S` instead of the whole quotient. Worker 806 is therefore credited as
coauthor.
