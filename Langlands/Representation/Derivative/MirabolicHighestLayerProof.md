# Proof of the actual highest mirabolic layer

Module `Langlands.Representation.Derivative.MirabolicHighestLayerProof`.

Authors: Worker 805, Worker 806 and Worker 1185. Worker 805 wrote this module and the
two helper modules it builds on. The averaging lemma of `MirabolicHighestLayerLift`
adapts Worker 806's published proof of `eq_bot_or_eq_top_of_radicalQuotient`. Worker
1185 wrote the imported published helper `MirabolicHighestLayerPlusMaps`. See
[Authorship](#authorship).

## Result

```lean
theorem Langlands.Derivative.mirabolicHighestLayer {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    MirabolicHighestLayerStatement.{uF, uV} F T
```

The conclusion is exactly the published proposition
`Langlands.Derivative.MirabolicHighestLayerStatement.{uF,uV} F T` from
`Langlands.Representation.Derivative.MirabolicHighestLayerStatement` (statement
artifact `aab6502d-ffdb-4615-bfe5-754f68eff06e`). The outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`, with
independent universes `uF` and `uV`. The theorem has no other hypotheses, whether
explicit, implicit or in typeclasses.

Unfolded, the theorem says the following. Fix a nontrivial continuous unitary additive
character `ψ`, a natural number `N`, and an actual smooth representation
`A : SmoothRep.{0,uF,uV} ℂ (GeneralLinear.mirabolic N F.Carrier)` of `P_(N+1)`. Fix
an order `k` with `hk : 0 < k ∧ k ≤ N+1`, and assume `Nontrivial A` and
`k = level T ψ A`. Then one invariant subspace `U : Subrepresentation A.representation`
satisfies:

1. `U ≠ ⊥`;
2. `Nonempty (Subrepresentation ((mirabolicDerivativeOfOrder T ψ N k hk).obj A).representation ≃o Set.Iic U)`;
3. `IsHomogeneous T ψ A ↔ ∀ S : Subrepresentation A.representation, S ≠ ⊥ → U ⊓ S ≠ ⊥`.

All three properties use the same `U`. The order isomorphism covers the whole
subrepresentation lattice of the actual order-`k` quotient derivative and the whole
interval of actual invariant subspaces of `A` below `U`. The hypothesis `Nontrivial A`
is not needed: `k = level T ψ A` with `k > 0` already implies it. The proof introduces
the hypothesis and leaves it unused.

The target theorem is the specialization of a second public theorem of this module,
written with `k = j + 1` and `N = n + j`:

```lean
theorem Langlands.Derivative.mirabolicHighestLayer_plusModel {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (n j : ℕ)
      (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic (n + j) F.Carrier))
      (hk : 0 < j + 1 ∧ j + 1 ≤ n + j + 1),
      j + 1 = level T ψ A →
        ∃ U : Subrepresentation A.representation,
          U ≠ ⊥ ∧
          Nonempty (Subrepresentation
            ((mirabolicDerivativeOfOrder T ψ (n + j) (j + 1) hk).obj A).representation ≃o
              Set.Iic U) ∧
          (IsHomogeneous T ψ A ↔
            ∀ S : Subrepresentation A.representation, S ≠ ⊥ → U ⊓ S ≠ ⊥) ∧
          Mirabolic.HighestLayer.IsPlusLayerImage T ψ n j A U
```

Its fourth conclusion is about the same `U`. `IsPlusLayerImage T ψ n j A U` says that
`U` is the range of an injective intertwining map into `A` from
`(Φ⁺)^j Ψ⁺ (A^(j+1)) = (Φ⁺)^(k-1) Ψ⁺ (A^(k))`. Here `Φ⁺` and `Ψ⁺` are the published
normalized plus functors and `A^(k)` is the actual order-`k` derivative (see
[The plus model](#the-plus-model-of-the-layer-section-model)). This is the formal
identification of `U` with the source's highest layer. The target proposition does
not mention it, and `mirabolicHighestLayer` drops it. `mirabolicHighestLayer_plusModel`
does not assume `Nontrivial A`.

The auxiliary declarations live in namespace
`Langlands.Derivative.Mirabolic.HighestLayer`. Below, unqualified names refer to that
namespace.

## The three modules

The proof consists of three new paired modules, all submitted together:

1. `Langlands.Representation.Derivative.MirabolicHighestLayerLift`
   (`MirabolicHighestLayerLift.md`). It defines one lifting step `liftStep` through
   `Φ⁻` and its inverse `imageStep`. It proves the one-step lattice comparison
   (`stepIso`, `inf_imageStep_ne_bot_iff`), element-level left exactness
   (`phiMinusSubIso`), the base step (`psiIso`) and the level bound for invariant
   subspaces (`level_subrepresentation_le`). Its section `Normalization` compares the
   minus twists with BZ77's Haar modulus.
2. `Langlands.Representation.Derivative.MirabolicHighestLayerPlus`
   (`MirabolicHighestLayerPlus.md`). For a smooth representation `B` of `P_(m+2)`, the
   orbit map `theta : R(B) → Φ⁺(Φ⁻ B)`, `w ↦ (x ↦ q(x·w))`, is a bijective intertwining
   map. Consequently (`exists_plusStep`), for every injective intertwining map
   `E : τ → Φ⁻ B` there is an injective intertwining map `E' : Φ⁺ τ → B` whose range is
   `liftStep T ψ m B E.range`.
3. This module. It iterates the two previous modules by induction on the order: it
   builds the layer together with its plus model and proves the target.

The module-level details are in the two helper Markdown files. This file describes
the assembly and carries the audits for all three modules.

## Notation and ranks

`mirabolic n F.Carrier` is `P_(n+1)`. Its radical `V` (Lean: `radical n F.Carrier`)
consists of the matrices `radicalElement c` with last column `(c,1)`, `c : Fin n → F`.
Its Levi factor is `GL_n`, embedded by `levi g = diag(g,1)`. The map
`successor = levi ∘ subtype : P_(n+1) → P_(n+2)` embeds one mirabolic in the next.
For `B` a representation of `P_(m+2)`, define:

- `R(B) = relations B.representation (radical (m+1) F.Carrier) 1`, the span of the
  vectors `u·v - v` for `u ∈ V`;
- `Ψ⁻ B = (psiMinus T (m+1)).obj B`, the coinvariants `B / R(B)`, a representation of
  `GL_(m+1)`;
- `Φ⁻ B = (phiMinus T ψ m).obj B`, the coinvariants of `B` for the published character
  `T.mirabolicTheta ψ m` (value `ψ(c_last)` on `radicalElement c`), with quotient map
  `q = phiMinusQuotient T ψ m B`, a representation of `P_(m+1)`;
- `Ψ⁺ D = (psiPlus T n).obj D`, for `D` a representation of `GL_n`: the published
  normalized inflation to `P_(n+1)`, that is, twist by `psiPlusCharacter T n = |det|^(1/2)`
  and let the radical act trivially (`MirabolicPlusNormalization`, Worker 984);
- `Φ⁺ τ = (phiPlus T ψ m).obj τ`, for `τ` a representation of `P_(m+1)`: the published
  normalized compact induction to `P_(m+2)` from the subgroup `plusSubgroup m`,
  twisted by the character `thetaPlus ψ m` and by `phiPlusCharacter T m = |det|^(1/2)`
  (`MirabolicPlus`, Worker 723, and `MirabolicPlusNormalization`, Worker 984). Its
  carrier universe is `max uF uV` when that of `τ` is `uV`.

The minus functors are the published functors of `MirabolicMinus` and carry the
twist `|det|^(-1/2)` (see [Normalization](#normalization)).

The statement reads the order-`k` derivative through
`mirabolicDerivativeOfOrder T ψ N k hk`. This transports `A` along
`N = (N+1-k) + (k-1)` and applies `mirabolicDerivative T ψ (N+1-k) (k-1)`, that is,
`k-1` changing-rank `Φ⁻` steps `P_(N+1) → P_N → … → P_(N+2-k)` followed by
`Ψ⁻ : P_(N+2-k) → GL_(N+1-k)`. The proof writes `k = j+1` and `N = n+j`, so the
derivative is `A^(j+1) = (mirabolicDerivative T ψ n j).obj A`: `j` steps `Φ⁻` and then
`Ψ⁻` to `GL_n`. By definition, `mirabolicDerivative T ψ n (j+1)` applied to `A` is
`mirabolicDerivative T ψ n j` applied to `Φ⁻ A`: the first step is `Φ⁻` at the top
rank (`derivative_obj_succ`, by `rfl`).

On the plus side the ranks go back up: `Ψ⁺ : GL_n → P_(n+1)` and
`Φ⁺ T ψ m : P_(m+1) → P_(m+2)`. So `(Φ⁺)^j Ψ⁺` takes the representation `A^(j+1)` of
`GL_n` to a representation of `P_(n+j+1)`, the group of `A`.

## The plus model of the layer (section `Model`)

- `plusLayerSucc T ψ n j D` is `(Φ⁺)^(j+1) Ψ⁺ D` for a representation `D` of `GL_n`. It
  is a representation of `P_(n+j+2)` (`mirabolic (n+j+1)`) with carrier universe
  `max uF uV`, defined by recursion on `j`:
  `plusLayerSucc T ψ n 0 D = (phiPlus T ψ n).obj ((psiPlus T n).obj D)` and
  `plusLayerSucc T ψ n (j+1) D = (phiPlus T ψ (n+j+1)).obj (plusLayerSucc T ψ n j D)`
  (`plusLayerSucc_zero`, `plusLayerSucc_succ`, both by `rfl`).
- `IsPlusLayerImage T ψ n j A U`, for `A` a representation of `P_(n+j+1)` and `U` an
  invariant subspace of `A`, is defined by cases on `j`:
  - `j = 0`: there is an injective intertwining map
    `E : Ψ⁺ ((mirabolicDerivative T ψ n 0).obj A) → A` with `E.range = U`; the source is
    `Ψ⁺ (Ψ⁻ A)`;
  - `j = j'+1`: there is an injective intertwining map
    `E : plusLayerSucc T ψ n j' ((mirabolicDerivative T ψ n (j'+1)).obj A) → A` with
    `E.range = U`.

  In both cases the source is `(Φ⁺)^j Ψ⁺ (A^(j+1))`. The unfolding lemmas are
  `isPlusLayerImage_zero` and `isPlusLayerImage_succ` (`Iff.rfl`). The definition
  splits into cases because `Ψ⁺` keeps the carrier universe `uV` while `Φ⁺` passes to
  `max uF uV`, so the sources for `j = 0` and for `j = j'+1` live in different
  universes. The maps are Mathlib's heterogeneous `Representation.IntertwiningMap`s.
  `E.range` is the Mathlib subrepresentation `Representation.IntertwiningMap.range`.
  So `U` is an actual invariant subspace of `A`, its inclusion is the subspace
  inclusion, and `E` is a linear bijection from `(Φ⁺)^j Ψ⁺ (A^(j+1))` onto `U` that
  commutes with the actions.
- `isPlusLayerImage_top`: if the radical acts trivially on a representation `A` of
  `P_(n+1)`, then `IsPlusLayerImage T ψ n 0 A ⊤`. The map is Worker 1185's published
  `psiPlusBaseEmbedding T n A h : Ψ⁺ (Ψ⁻ A) → A`. It inverts the quotient map
  `A → Ψ⁻ A` (bijective because the radical acts trivially); the `|det|^(1/2)` and
  `|det|^(-1/2)` twists cancel. It is injective with range `⊤`
  (`psiPlusBaseEmbedding_injective`, `psiPlusBaseEmbedding_range`).
- `isPlusLayerImage_liftStep`: let `A` be a representation of `P_(n+j+2)` and `U'` an
  invariant subspace of `Φ⁻ A` with `IsPlusLayerImage T ψ n j (Φ⁻ A) U'`. Then
  `IsPlusLayerImage T ψ n (j+1) A (liftStep T ψ (n+j) A U')`. By `derivative_obj_succ`,
  the required source is `Φ⁺` of the source of the embedding `E` of `U'`.
  `exists_plusStep` applied to `E` gives an injective `E' : Φ⁺ (source of E) → A` with
  range `liftStep (E.range) = liftStep U'`. In both cases `j = 0` and `j = j'+1`, the
  source of `E'` is `(phiPlus T ψ (n+0)).obj …` resp.
  `(phiPlus T ψ (n+(j'+1))).obj …`. The proof rewrites the functor itself, by the
  `rfl` equations `phiPlus T ψ (n+0) = phiPlus T ψ n` and
  `phiPlus T ψ (n+(j'+1)) = phiPlus T ψ (n+j'+1)`, so that the source matches
  `plusLayerSucc`.

## The layer, by induction on the order (section `Layer`)

`exists_layer j` proves, for every `n` and every `A` on `P_(n+j+1)` with
`level T ψ A = j+1`, that some invariant subspace `U` of `A` satisfies four things:

- `U ≠ ⊥`;
- `Nonempty (Subrepresentation ((mirabolicDerivative T ψ n j).obj A).representation ≃o Set.Iic U)`;
- for every invariant subspace `S`,
  `Nontrivial ((mirabolicDerivative T ψ n j).obj (SmoothRep.subrepresentation A S)) ↔ U ⊓ S ≠ ⊥`;
- `IsPlusLayerImage T ψ n j A U`.

The layer is defined in the induction:

- `j = 0`: `U = ⊤`;
- `j+1`: `U = liftStep T ψ (n+j) A U'`, where `U'` is the layer already built for
  `Φ⁻ A`, a representation of `P_(n+j+1)` of level `j+1`.

**Base `j = 0`.** The level is `1`, so the radical acts trivially
(`radical_trivial_of_level_le_one`) and `A` is nontrivial
(`LevelCalculus.nontrivial_of_level_ne_zero`). Take `U = ⊤ ≠ ⊥`
(`LevelCalculus.top_ne_bot`). The order isomorphism is `psiIso` followed by
`OrderIso.IicTop`. For `S`, the radical also acts trivially on `S`, so the quotient
map `S → Ψ⁻ S` is bijective. Then `Nontrivial (Ψ⁻ S) ↔ S ≠ ⊥ ↔ ⊤ ⊓ S ≠ ⊥`. The plus
model is `isPlusLayerImage_top`.

**Step `j+1`.** `A` lives on `P_(n+j+2)` and has level `j+2`. By
`LevelCalculus.hasNonzeroDerivative_succ_iff`, `Φ⁻A` has a nonzero derivative of
order `j+1`, so its level is positive. `LevelCalculus.level_eq_level_phiMinus_succ`
then gives `level (Φ⁻A) = j+1`. The induction hypothesis supplies `U'` for `Φ⁻A`.
Set `U = liftStep U'`.

- `U ≠ ⊥`: otherwise `U' = imageStep (liftStep U') = imageStep ⊥ = ⊥`.
- The order isomorphism is
  `Sub(A^(j+2)) = Sub((Φ⁻A)^(j+1)) ≃o Set.Iic U' ≃o Set.Iic (liftStep U')`,
  the last map being `stepIso` inverted.
- For `S`: the derivative of `S` is the derivative of `Φ⁻ S`. By `phiMinusSubIso`,
  `Φ⁻ S ≅ imageStep S` as a subrepresentation of `Φ⁻A`, and the derivative functor
  preserves this isomorphism (`LevelCalculus.nontrivial_iff_of_iso`). The induction
  hypothesis turns nontriviality into `U' ⊓ imageStep S ≠ ⊥`, and
  `inf_imageStep_ne_bot_iff` turns that into `liftStep U' ⊓ S ≠ ⊥`.
- The plus model is `isPlusLayerImage_liftStep` applied to the plus model of `U'`.

**Unwinding.** `U = liftStep(liftStep(… liftStep(⊤)…))` with `k-1` lifts, where the
innermost `⊤` is the whole of `(Φ⁻)^(k-1) A`. Every stage is an actual invariant
subspace of the representation at that stage, and the outermost one is an actual
invariant subspace of the supplied `A`. Correspondingly, the embedding
`(Φ⁺)^(k-1) Ψ⁺ (A^(k)) → A` starts from `psiPlusBaseEmbedding` on `(Φ⁻)^(k-1) A`. It
is then pushed up by `k-1` applications of `exists_plusStep`, whose map is `plusStepMap`
of `MirabolicHighestLayerPlus`. No supplied layer, abstract model or lattice
hypothesis is used.

**Relation to the source filtration.** For a representation `τ` of `P_n`,
Bernstein–Zelevinsky 1977 §3.5 defines a filtration `τ_k = (Φ⁺)^(k-1)(Φ⁻)^(k-1) τ` by
subrepresentations with `τ_k/τ_(k+1) ≅ (Φ⁺)^(k-1) Ψ⁺(τ^(k))`. At the highest order
`τ_(k+1) = 0`, so the highest layer is `τ_k ≅ (Φ⁺)^(k-1) Ψ⁺(τ^(k))`. The fourth
conclusion formalizes exactly this for `U`: `U` is the image in `A` of
`(Φ⁺)^(k-1) Ψ⁺ (A^(k))` under an injective intertwining map. The Lean proof does not
construct the lower members `τ_i`, `i < k`, of the filtration or its other quotients;
only the highest layer is needed.

**Rank transport.** The main theorem writes `k = j+1` and `N = n+j`.
`derivative_cast` identifies the lattice of `mirabolicDerivativeOfOrder T ψ (n+j) (j+1) hk`
(transport along `mirabolic_rank_eq_of_order hk`, with `n+j+1-(j+1) = n` and
`j+1-1 = j`) with the lattice of `mirabolicDerivative T ψ n j` applied to `A`
(transport along `rfl`). Composing with the isomorphism from `exists_layer` gives the
required `Nonempty (… ≃o Set.Iic U)`.

## Homogeneity criterion

This is Zelevinsky 1980 §5.1(1) iff (2). Zelevinsky's proof (printed p.187, PDF
page 24) shows `σ^(k) = 0 ⇔ σ ∩ τ_k = 0` for submodules `σ`, using BZ77 §3.5 and
§3.3(a). The Lean proof establishes the same equivalence
`HasNonzeroDerivative S (j+1) ↔ U ⊓ S ≠ ⊥` by the induction above, through
`inf_imageStep_ne_bot_iff`. `mirabolicHighestLayer_plusModel` then uses three facts:

- `level_subrepresentation_le` (`MirabolicHighestLayerLift`): a nonzero derivative of
  an invariant subspace is a nonzero derivative of `A`, so `level S ≤ level A`.
- From `exists_layer` and `LevelCalculus.hasNonzeroDerivative_succ_iff_cast`:
  `HasNonzeroDerivative T ψ S (j+1) ↔ U ⊓ S ≠ ⊥` for every `S`.
- Published `isHomogeneous_iff`: homogeneity means `level S = level A` for every
  `S ≠ ⊥`.

Proof of the equivalence, with `level A = j+1`:

- (⇒) If `S ≠ ⊥`, then `level S = j+1 ≠ 0`. So `S` has a nonzero derivative of order
  `j+1` (`LevelCalculus.hasNonzeroDerivative_level`), and therefore `U ⊓ S ≠ ⊥`.
- (⇐) If `S ≠ ⊥`, then `U ⊓ S ≠ ⊥`. So `S` has a nonzero derivative of order `j+1`,
  and `level S ≥ j+1` (`le_level_of_hasNonzeroDerivative`). With
  `level S ≤ level A = j+1`, equality follows.

`mirabolicHighestLayer` substitutes `k = j+1` and `N = n+j` (with `j = k-1` and
`n = N-j`, using `hk`), applies `mirabolicHighestLayer_plusModel` and keeps its first
three conclusions.

## Normalization

**Minus side (formalized in `MirabolicHighestLayerLift`, section `Normalization`).**
The published `psiMinus` and `phiMinus` twist the coinvariant actions by
`psiMinusCharacter T n = |det|^(-1/2)` and `phiMinusCharacter T n = |det ∘ subtype|^(-1/2)`,
with `|·|` the residue-normalized absolute value. BZ77 §1.8(b) (printed p.444, PDF
page 5, visually checked) normalizes `r_{U,θ}` by `mod_U^(-1/2)`, where `mod_U(g)` is
the module of `u ↦ g u g⁻¹` on `U`. The Lean lemmas `map_inv_mul_haar_iff`,
`psiMinusCharacter_eq_modulus` and `phiMinusCharacter_eq_modulus` prove that the Haar
modulus of conjugation by `levi g` on the radical is `|det g|`, and that both minus
characters are its `-1/2` power. The proof uses Worker 110's published
`padicRectangularHaarScaling`. So the inherited `|det|^(-1/2)` twists are exactly
BZ77's `mod_V^(-1/2)`. Worker 710's published `MirabolicMinusNormalization`
(`psiMinusHaarInverseHalf_eq`, `phiMinusHaarInverseHalf_eq`) states the same
agreement with the actual radical Haar character. It is in the import closure but not
used; this proof's comparison is its own.

**Plus side (published, reused by name).** BZ77 §1.8(a)(1) (same page) normalizes the
induction `i_{U,θ}` by `mod_U^(1/2)`: its functions satisfy
`f(umg) = θ(u) mod_U^(1/2)(m) ρ(m)(f(g))`. This is the inverse of the quotient
normalization. The published
`phiPlus` and `psiPlus` (`MirabolicPlusNormalization`, Worker 984) twist by
`phiPlusCharacter T n` and `psiPlusCharacter T n`. Published lemmas fix these
characters:

- `phiPlusCharacter_eq_inv` and `psiPlusCharacter_eq_inv`: they are the inverses of
  the minus characters, that is, `|det|^(1/2)`;
- `phiPlusCharacter_mul_phiMinusCharacter` and
  `psiPlusCharacter_mul_psiMinusCharacter`: their products with the minus characters
  are `1`;
- `phiPlus_haarNormalization`, `psiPlus_haarNormalization`, `phiPlusHaarHalf_eq` and
  `psiPlusHaarHalf_eq`: these identify the twists with the positive half of the actual
  radical Haar modulus.

This proof does not re-prove the plus normalization. The last four theorems are not
in its declaration closure.

**Where the normalization enters.** In `MirabolicHighestLayerPlus`,
`orbitFun_covariant` shows that the orbit function `f_w(x) = q(x·w)` satisfies the
covariance of the normalized `Φ⁺(Φ⁻ B)` exactly:
`f(q'x) = thetaPlus(q') · phiPlusCharacter(p q') · (p q')·f(x)` for `q'` in
`plusSubgroup`, with `p` the `plusProjection`. The proof uses `phiMinus_action`,
which contributes `phiMinusCharacter(p q')`, and the published
`phiPlusCharacter_mul_phiMinusCharacter`. Likewise `psiPlusBaseEmbedding` is
equivariant because `psiPlusCharacter · psiMinusCharacter = 1`. With any other twist
on `Φ⁺` or `Ψ⁺`, the orbit map and the base embedding would not be intertwining. The
embedded `(Φ⁺)^(k-1) Ψ⁺ (A^(k))` therefore carries the published normalizations,
which are the source's.

**Use in the lattice argument.** The lattice comparison uses the minus twist only as
a nowhere-zero scalar character. Twisting by such a character changes neither the
invariant subspaces, nor nontriviality, nor kernels. The `Normalization` section of
`MirabolicHighestLayerLift` is not in the declaration closure of
`mirabolicHighestLayer`; its separate closure is listed below.

## Ranks, boundary cases and the zero-default convention

- `mirabolic N F.Carrier` is `P_(N+1)`. The order-`k` derivative goes through
  `k-1 = j` decreasing-rank `Φ⁻` steps `P_(n+j+1) → … → P_(n+1)` and then
  `Ψ⁻ : P_(n+1) → GL_n`, where `n = N+1-k`. Each step of `exists_layer` lowers the rank
  by one, and each `Φ⁺` of the plus model raises it by one. The induction is on `j`
  for all `n` at once. No positivity of `n` is assumed.
- `N = 0, k = 1` is `j = 0, n = 0`: `P_1 → GL_0`. The radical of `P_1` is trivial,
  `U = ⊤`, `psiIso` gives the lattice isomorphism, and the plus model is
  `psiPlusBaseEmbedding : Ψ⁺ (Ψ⁻ A) → A` with range `⊤`.
- The top order `k = N+1` is `n = 0`, `j = N`: the last `Ψ⁻` lands in `GL_0`, and the
  plus model is `(Φ⁺)^N Ψ⁺ (A^(N+1))` with `A^(N+1)` a representation of `GL_0`. The
  same induction covers it.
- `level T ψ A = Nat.findGreatest (HasNonzeroDerivative T ψ A) (N+1)`, with default `0`
  when no valid order has a nonzero derivative. The theorem only concerns a supplied
  positive order `k` equal to the level. Positivity of `j+1` is what makes
  `hasNonzeroDerivative_level` applicable. The proof does not assert that every
  nonzero representation has positive level. Published detection enters only through
  `LevelCalculus.nontrivial_phiMinus_iff` in the base step, to conclude `Φ⁻A = 0` from
  `level A ≤ 1`. No strong-indecomposability conclusion is stated or used.

## Sources

- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive p-adic
  groups I*, Ann. Sci. ÉNS 10 (1977). Literature ID
  `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`, file
  `/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.
  Read for this proof: §1.7–1.8 (printed p.444, PDF page 5, visually checked for the
  signs of the `mod^(∓1/2)` normalizations), §3.2–3.3 (printed p.451, PDF page 12),
  including the definition of `Φ⁺`, `Ψ⁺` and the exact sequence 3.2(e)
  `0 → Φ⁺Φ⁻ → Id → Ψ⁺Ψ⁻ → 0`, and §3.4–3.5 (printed p.452, PDF page 13), the filtration
  `τ_k` and its quotients.
- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
  irreducible representations of GL(n)*, Ann. Sci. ÉNS 13 (1980). Literature ID
  `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`, §5.1(1) iff (2),
  printed p.187, PDF page 24.

The existential interface with `Set.Iic U` and the `IsPlusLayerImage` conclusion are
derived forms, not verbatim source theorems. The Lean route differs from the sources'.
It proves the lattice comparison of §3.3(a) directly at the level of invariant
subspaces, by an averaging argument and the published vanishing theorem
`subsingleton_of_psiMinus_phiMinus`. It proves the case of 3.2(e) needed here, the
isomorphism `R(B) ≅ Φ⁺(Φ⁻ B)` given by the orbit map, directly by supports and
character sums (`MirabolicHighestLayerPlus`). It uses no adjunction and no exactness
theorem for `Φ⁺`, `Ψ⁺`, `Φ⁻` or `Ψ⁻`. No errata note for these sources was found in
the project or public `notes` locations.

## Mathematical proof-dependency audit

Every lower result used as a theorem is an accepted, published proof in Library
commit `4bec44eec4c7f23def3d25d5c43f4f2a034af469`. Every reused construction is
published there as well. The substantive inputs of the three modules:

| Lower result or construction | Module (author) | Use |
|---|---|---|
| `Mirabolic.subsingleton_of_psiMinus_phiMinus` | `MinusVanishing` (Worker 1025; artifact `c6026915-8731-45a8-bd21-ef1ac39654b8`) | `Ψ⁻Z = Φ⁻Z = 0 ⇒ Z = 0` in `liftStep_imageStep` |
| `Mirabolic.radical_acts_trivially_of_phiMinus` | `MirabolicHighestDerivativeDescent` (Worker 1024; joint artifact `f957ae76-3779-4436-bdcb-98bc63561e07` of Workers 1024 and 805) | base step |
| `Mirabolic.radical_acts_trivially_zero`, `relations_one_eq_bot` | `MirabolicDerivativeVanishing` (Worker 1024; same artifact) | base step |
| `Mirabolic.radicalRelations_stable` | `MirabolicPhiMinusNondegeneratePairing` (Worker 805; same artifact) | invariance of `liftStep` |
| `mirabolicDerivativeDetection` (via `LevelCalculus.level_pos` inside `nontrivial_phiMinus_iff`) | `MirabolicDerivativeDetectionProof` (Worker 658), a wrapper of `MirabolicDerivativeVanishing.derivativeDetection` | `Nontrivial (Φ⁻A) ⇒ 1 < level A` in the base step |
| `apply_eq_zero_of_mem_relations` | `Jacquet.CharacterAveraging` (Worker 831) | element-level left exactness |
| `latticeBox` API, `exists_latticeBox_subset`, `finite_latticeBox_quotient`, `sum_out_eq_zero`, `eq_one_of_smul_eq_self`, `mem_latticeBox_of_forall_character_eq_one` | `MirabolicLatticeBox` (Worker 806) | averaging; supports and character sums in `MirabolicHighestLayerPlus` |
| `radicalBox`, `isCompact_radicalBox`, `radicalBox_mono`, `exists_mem_latticeBox` | `MinusVanishing` (Worker 1025) | exhaustion in left exactness |
| `lastRow_image_mem_nhds`, `lastRow_mem_image_iff`, `continuous_lastRow`, `lastRow_ne_zero` | `RankinSelberg.LastRowCompactOrbitProof` (Worker 714) | averaging; last-row supports |
| `lift`, `lastRow_lift`, `orbitSet`, `mem_orbitSet`, `lastRow_mem_orbitSet`, `isOpen_orbitSet`, `isOpenMap_lastRow`, `exists_lastRow_eq`, `lastRow_mirabolic_mul`, `mul_inv_mem_mirabolic_of_lastRow_eq` | `RankinSelberg.EqualRankFrobeniusProof` (author not recorded in its Markdown); its main theorem is not used | last rows, open orbit sets and the compact-support criterion in `MirabolicHighestLayerPlus` |
| `GeneralLinearGroup.integralSubgroup`, `isCompact_integralSubgroup`, `isOpen_integralSubgroup` | `Group.GL.IntegralSubgroup` (author not recorded in its Markdown) | compact open subgroup in the support cover |
| `rowHomeomorph` | `HarmonicAnalysis.RowSchwartzAction` (author not recorded in its Markdown) | only inside `EqualRankFrobeniusProof.isOpenMap_lastRow` |
| `phiPlus`, `psiPlus`, `phiPlusNormalizedMk`, `phiPlusNormalizedEval` with `_covariant`, `_injective`, `_exists_openSubgroup`, `_isCompact_quotientSupport`; `phiPlusCharacter_eq_inv`, `phiPlusCharacter_mul_phiMinusCharacter`, `psiPlusCharacter_eq_inv`, `psiPlusCharacter_mul_psiMinusCharacter` | `MirabolicPlusNormalization` (Worker 984) | the normalized `Φ⁺`, `Ψ⁺`; vectors of `Φ⁺` and the covariance check |
| `thetaPlus`, `phiPlusUnnormalized`, `psiPlusUnnormalized`, `phiPlusMk`, `phiPlusEval` and its laws | `MirabolicPlus` (Worker 723) | the unnormalized constructions under the normalized functors |
| `compactInduced`, `quotientSupport`, `quotientMap` and the function spaces | `Induction.Definitions` (Worker 15) | compact induction underlying `Φ⁺`; quotient supports |
| `plusSubgroup`, `plusProjection`, `mem_plusSubgroup`, `plus_eq_radicalElement_mul_successor`, `projection_radicalElement_mul_levi`, `lastColumn_mul_last`, continuity lemmas | `MirabolicProjection` (Worker 749) | the inducing subgroup of `Φ⁺` and the factorizations in `MirabolicHighestLayerPlus` |
| `phiPlusPost`, `phiPlusPost_injective`, `mem_range_phiPlusPost`, `psiPlusBaseEmbedding`, `psiPlusBaseEmbedding_injective`, `psiPlusBaseEmbedding_range` | `MirabolicHighestLayerPlusMaps` (Worker 1185 with Worker 805; artifact `a88fbb0e-6c1c-4f3a-9151-b45d9b90f868`) | `exists_plusStep`; the base `isPlusLayerImage_top` |
| `padicRectangularHaarScaling` | `HarmonicAnalysis.PadicRectangularHaarScalingProof` (Worker 110) | `Normalization` section of `MirabolicHighestLayerLift` only |
| `LevelCalculus` lemmas (`hasNonzeroDerivative_succ_iff`, `hasNonzeroDerivative_succ_iff_cast`, `level_eq_level_phiMinus_succ`, `nontrivial_phiMinus_iff`, `level_le_of_imp`, `isoRange`, …) | `LevelCalculus` (Workers 1070/745) | level bookkeeping |
| Definitions and elementary API of `Φ⁻`, `Ψ⁻`, `θ`, `level`, `IsHomogeneous`, derivative iteration, rank maps | `MirabolicMinus` (Worker 749), `MirabolicCharacter` (Worker 653), `Homogeneity`, `Iteration` (Worker 818), `MirabolicRadical` (Worker 653), `MirabolicProjection` (Worker 749) | definitions |

The guarantees used from the reused plus constructions are their published explicit
laws: `phiPlusNormalizedEval_covariant` (left covariance),
`phiPlusNormalizedEval_exists_openSubgroup` (right smoothness),
`phiPlusNormalizedEval_isCompact_quotientSupport` (compact support modulo
`plusSubgroup`), `phiPlusNormalizedEval_injective`, the constructor
`phiPlusNormalizedMk` from exactly these three properties, and the group action by
right translation. Worker 1185's maps are characterized by their published range and
injectivity lemmas. No theorem about `Φ⁺` or `Ψ⁺` beyond these laws and the character
identities is used.

Shared lower inputs were checked for independence as follows. The detection chain
(`MirabolicDerivativeDetectionProof` → `MirabolicDerivativeVanishing` →
`MirabolicHighestDerivativeDescent`, `MirabolicPhiMinusNondegeneratePairing`,
`MinusVanishing`) is the general Bernstein–Zelevinsky 1977 derivative route. Its own
published audits record compliance with the operator's detection conditions
(`/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md`). It uses no
Zelevinsky 1980 segment derivative formula (§3.5 or §9.6) and no task from the
exclusion lists. This proof adds no such dependency. `LevelCalculus` is shared with a
segment-socle consumer, but it is a lower module: it imports nothing from that
consumer. Its results that mention exactness (`mapsShortExact_phiMinusIterate`,
`mapsShortExact_mirabolicDerivative`, `mapsShortExact_mirabolicDerivativeOfOrder`,
`level_eq_zero_iff_subsingleton`) are not in this proof's declaration closure. The
plus-side inputs (`MirabolicPlus`, `MirabolicPlusNormalization`,
`MirabolicHighestLayerPlusMaps`, `Induction.Definitions`, `EqualRankFrobeniusProof`,
`IntegralSubgroup`, `RowSchwartzAction`) are constructions and lemmas about compact
induction, characters and last rows. They lie in the import closure listed below,
which contains none of the excluded modules.

## Independence and exclusions

- Not used: `Langlands.Derivative.MirabolicStrongIndecomposabilityReduction`, its
  proof task `08fe06ea-e64e-4f3a-b899-3e0acacf61db`, their proof successors and
  consequences, and any strong-indecomposability conclusion.
- Not used: the generic lattice transport/essential-interval unit (statement
  `ec62132d-2b17-4cbd-bd75-d5fd43de7cde`, proof task
  `a2baddab-056b-4503-865e-74d58ecb3812`). These modules prove their own concrete
  lattice statements and do not duplicate that algebraic unit.
- Not used: the paused minus-exactness task `b65bc667-6951-4bd5-82af-10fb7046df7f`.
  The statement module `MirabolicMinusExactnessStatement` is in the import closure only
  because `LevelCalculus` imports it (through `ShortExactFunctorLaws`). None of its
  constants is in the declaration closure. Only element-level left exactness for
  invariant subspaces is proved and used.
- Plus functors: the published constructions `phiPlus` and `psiPlus` are used as
  constructions, with the laws listed in the audit. No adjunction, exactness,
  filtration, finite-length, admissibility or irreducibility theorem is used or
  assumed. In the imported Lean files the word "adjunction" occurs only in a
  docstring of `MirabolicPlus`, which says that no adjunction is stated there.
- None of the following, nor their mathematical conclusions, proof successors or
  transitive proof dependencies, occur in the import or declaration closure:
  ordered-socle existence `23189526-80b0-4828-a6d4-7ebec2cbeef5`; socle exhaustion
  `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`; analytic segment classification
  `aca8805b-054f-4d56-8045-12db7f623404`; segment-socle product irreducibility
  `23e98d90-6055-4e35-91a9-b0f5d8a84961`; the final segment-socle irreducibility
  criterion `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`; `AdjacentUnlinkedSegmentSocleSwap`;
  `TwoSegmentSocleCommutation`; special-head product criterion
  `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`; special-head exhaustion
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`; ordered special-head existence
  `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`; quotient coverage
  `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`; tempered block uniqueness
  `52e97845-36bb-457d-b76f-70753334b88c`; `SquareIntegrableLanglandsClassification` /
  `1cb45da2-7007-4351-a694-594fb148b8d1`; square-integrable exhaustion
  `cd8ab97c-0b78-4bce-97c4-d307a28159a4`; regular exhaustion
  `bf433f0a-921a-428c-b0c0-6475438125ac`; `GenericSegmentProductUniqueness` /
  `30341ae4-65f2-4a0e-9283-763db01a409e`; ordered special-segment conversion
  `8252833d-c269-41a9-824c-5879e531b23b`; forward special-segment essential
  square-integrability `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807`.
- Also absent, as required by the inherited detection restrictions: individual
  special-head existence `67279e36-f3c2-42e3-9302-11729784042e`; segment-socle
  existence `4ca79bbd-589e-476b-9f65-661e799984b5`; adjacent socle commutation
  `e3634665-571b-4852-9f4c-bab8a1053434`; `SegmentFullJacquetFormula` /
  `ed48ae06-964c-4c84-9e62-978f5a953ca7`; `SegmentHeadJacquetFormula` /
  `55ad1e10-62d8-46b7-a081-909ef0056426`; `SegmentSocleJacquetFormula` /
  `b95105c6-f8bb-4641-ae53-2f49d1e7f034`;
  `SegmentSpecialJacquetExponentNormFormula` /
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`; the segment-socle part of
  `8e5b4563-0365-41c7-b134-70f2a0b36292`; Zelevinsky 1980 §3.5, §4.2, §9.3, §9.6
  and §9.7.
- Check performed: the 131 imported Lean files and the three new modules contain
  none of the identifiers `StrongIndecomposab`, `SocleExistence`, `SocleExhaustion`,
  `SegmentSocle`, `SocleSwap`, `SocleCommutation`, `SquareIntegrable`,
  `GenericSegmentProduct`, `JacquetFormula`, `SpecialEssential`, `SpecialHead`,
  `QuotientCoverage`, `TemperedBlock`, `RegularExhaustion`, `SegmentClassification`,
  `SpecialSegment`, `Leibniz`, `Adjunction`, `MirabolicSmoothPhiPlus`,
  `EssentialInterval` or `LatticeTransport`. The lowercase word `adjunction` occurs
  only in `MirabolicPlus` (the docstring above). Only
  `MirabolicMinusExactnessStatement`, `ShortExactFunctorLaws` and `LevelCalculus`
  mention `MinusExactnessStatement`.
- Coordination: the plus constructions are reused by Lean name from the published
  modules of Workers 723 and 984. The one new plus-side helper,
  `MirabolicHighestLayerPlusMaps`, was split off to Worker 1185 by agreement within
  this task and is published. Worker 157's finite-length scope
  `0717fd42-d711-4f42-8269-f6ae4c8da1e9`, Worker 357's mixed-product/restriction/Leibniz
  scope, Worker 288's order-zero adapter and Worker 127's controls are untouched. No
  new task was split off.

## Validation

- Lake build of the three modules `MirabolicHighestLayerLift`,
  `MirabolicHighestLayerPlus` and `MirabolicHighestLayerProof` in environment
  `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with declaration inspection of
  `Langlands.Derivative.mirabolicHighestLayer`: diagnostic
  `cc31c958-eff3-4a83-9a13-c5ffe0b96371`, 0 errors, 0 warnings. Axioms are `propext`,
  `Classical.choice` and `Quot.sound` only. Level parameters are `uF` and `uV`. No
  `sorry`, no new axiom, no `native_decide`.
- Lean file SHA256: `MirabolicHighestLayerLift.lean`
  `9ac1a4a5a75b22b0ac3b63393288781ba48775566b3cd9d3a83f0cfad9537f94`,
  `MirabolicHighestLayerPlus.lean`
  `14bb209d1044412168a508a44a560ca616602e0e9c8c494a4da20ee2f9ff8a59`,
  `MirabolicHighestLayerProof.lean`
  `2f268182472ae941c1f4c98d950c9af506f5722aed2ffe130674399016778a5d`.
- Unchanged target: the statement pair in the workspace has SHA256
  `18167297f5a3657e1b35b1d09a87eb24430248f08baa2bdf9a1b46eae13a6c0d` (Lean) and
  `038132bad17090900b65626b9b168205e311906d32c96ba4c6e5eaae49e588b1` (Markdown). These
  equal the published pair recorded for artifact `aab6502d` and the Library at the
  base commit.
- Unchanged imports: all 262 Lean/Markdown files of the 131 imported project modules
  are byte-identical to Library `4bec44eec4c7f23def3d25d5c43f4f2a034af469`. The only
  new files are the three pairs of this submission.

## Complete project import closure

The closure was computed by recursive enumeration of the `import` lines of the
project modules. It has 131 project modules, not counting the three new modules,
which appear as named rows in dependency order. The direct imports are rows 55, 85,
118, 119, 70, 117 and 106 for `MirabolicHighestLayerLift`; `MirabolicHighestLayerLift`
and rows 131, 130 and 108 for `MirabolicHighestLayerPlus`; and
`MirabolicHighestLayerPlus` for this module. Mathlib and core imports are omitted. The
third column lists each module's direct project imports by row number.

| # | Module | Direct project imports (#) |
|---|---|---|
| 1 | `Langlands.Group.GL.Basic` | - |
| 2 | `Langlands.Group.GL.UpperUnipotent` | 1 |
| 3 | `Langlands.Group.GL.Mirabolic` | 2 |
| 4 | `Langlands.LocalField.Definitions` | - |
| 5 | `Langlands.LocalField.Canonical` | 4 |
| 6 | `Langlands.LocalField.Topology` | 4 |
| 7 | `Langlands.Group.GL.Padic` | 1, 5, 6 |
| 8 | `Langlands.Group.GL.RankMaps` | 1, 7 |
| 9 | `Langlands.Group.GL.MirabolicRadical` | 3, 8 |
| 10 | `Langlands.Group.GL.NonarchimedeanStatement` | - |
| 11 | `Langlands.Group.GL.Nonarchimedean` | 10 |
| 12 | `Langlands.Topology.Nonarchimedean.Subgroup` | - |
| 13 | `Langlands.Representation.Jacquet.Coinvariants` | - |
| 14 | `Langlands.Representation.Smooth.Definitions` | - |
| 15 | `Langlands.Representation.Smooth.Transfer.PullbackStatement` | 14 |
| 16 | `Langlands.Representation.Smooth.Transfer.PullbackProof` | 15 |
| 17 | `Langlands.Representation.Smooth.Transfer.SubquotientStatement` | 14 |
| 18 | `Langlands.Representation.Smooth.Transfer.SubquotientProof` | 17 |
| 19 | `Langlands.Representation.Twist.Definitions` | - |
| 20 | `Langlands.Representation.Twist.SmoothStatement` | 19, 14 |
| 21 | `Langlands.Representation.Twist.SmoothProof` | 20 |
| 22 | `Langlands.Representation.Jacquet.SmoothTwist` | 13, 16, 18, 21 |
| 23 | `Langlands.Representation.Category.Basic` | 14 |
| 24 | `Langlands.Representation.Jacquet.Localization` | 22, 23 |
| 25 | `Langlands.HarmonicAnalysis.Basic` | - |
| 26 | `Langlands.Representation.MatrixCoefficient.Definitions` | - |
| 27 | `Langlands.Representation.Dual.Definitions` | - |
| 28 | `Langlands.Representation.MatrixCoefficient.LawsStatement` | 26, 27, 14 |
| 29 | `Langlands.Representation.MatrixCoefficient.LawsProof` | 28 |
| 30 | `Langlands.Representation.Whittaker.Algebraic` | 26, 14 |
| 31 | `Langlands.Representation.Whittaker.GeneralLinear` | 2, 25, 29, 30 |
| 32 | `Langlands.Representation.Twist.ContinuousCharacterStatement` | - |
| 33 | `Langlands.Representation.Twist.ContinuousCharacterProof` | 32 |
| 34 | `Langlands.Representation.Derivative.MirabolicCharacter` | 9, 11, 12, 24, 31, 33 |
| 35 | `Langlands.Representation.Twist.AdmissibilityStatement` | 19, 14 |
| 36 | `Langlands.Representation.Smooth.Admissibility.CofinalStatement` | 14 |
| 37 | `Langlands.Representation.Smooth.Admissibility.CofinalProof` | 36 |
| 38 | `Langlands.Representation.Twist.AdmissibilityProof` | 35, 21, 37 |
| 39 | `Langlands.Representation.Twist.AlgebraStatement` | 19 |
| 40 | `Langlands.Representation.Twist.AlgebraProof` | 39 |
| 41 | `Langlands.Representation.Twist.SubquotientDefinitions` | 19 |
| 42 | `Langlands.Representation.Twist.SubquotientStatement` | 41 |
| 43 | `Langlands.Representation.Twist.SubquotientProof` | 42 |
| 44 | `Langlands.Representation.Category.Twist` | 23, 38, 40, 43 |
| 45 | `Langlands.Representation.Twist.RealPower` | 21 |
| 46 | `Langlands.LocalField.Normalization.Definitions` | 4 |
| 47 | `Langlands.LocalField.Normalization.Statement` | 46 |
| 48 | `Langlands.LocalField.Normalization.Proof` | 47 |
| 49 | `Langlands.Topology.CompactNormCharacter` | - |
| 50 | `Langlands.Group.GL.NormalizedCharacter` | 7, 48, 49 |
| 51 | `Langlands.Representation.Derivative.MirabolicMinus` | 34, 44, 45, 16, 50 |
| 52 | `Langlands.Representation.Derivative.Iteration` | 51 |
| 53 | `Langlands.Representation.Category.Subquotients` | 23, 18 |
| 54 | `Langlands.Representation.Derivative.Homogeneity` | 52, 53 |
| 55 | `Langlands.Representation.Derivative.MirabolicHighestLayerStatement` | 54 |
| 56 | `Langlands.Representation.Derivative.MirabolicMinusExactnessStatement` | 51 |
| 57 | `Langlands.Representation.Derivative.ShortExactFunctorLaws` | 56 |
| 58 | `Langlands.Analysis.Local.QuotientMeasure` | - |
| 59 | `Langlands.Representation.RankinSelberg.QuotientIntegrals` | 31, 8, 58 |
| 60 | `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement` | 4, 59 |
| 61 | `Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement` | 4, 3, 59 |
| 62 | `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof` | 61, 6 |
| 63 | `Langlands.HarmonicAnalysis.Conductor` | 25, 46, 33 |
| 64 | `Langlands.LocalFactor.Harmonic.Statement` | 46, 25 |
| 65 | `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof` | 63, 48, 64 |
| 66 | `Langlands.HarmonicAnalysis.PadicHaarScalingStatement` | 50 |
| 67 | `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` | 66, 6 |
| 68 | `Langlands.HarmonicAnalysis.PadicLatticeTopology` | 65, 67 |
| 69 | `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` | 60, 62, 65, 67, 68 |
| 70 | `Langlands.Representation.Derivative.MirabolicLatticeBox` | 69 |
| 71 | `Langlands.Representation.Compact.FiniteMean` | - |
| 72 | `Langlands.Representation.Compact.OrbitMeanTranslation` | 71 |
| 73 | `Langlands.Representation.Compact.Definitions` | 71, 14 |
| 74 | `Langlands.Representation.Compact.ProjectionStatement` | 73 |
| 75 | `Langlands.Representation.Compact.ProjectionProof` | 74 |
| 76 | `Langlands.Representation.Jacquet.CharacterAveraging` | 72, 75, 24, 21, 30 |
| 77 | `Langlands.Representation.Derivative.MinusVanishing` | 51, 70, 76, 7 |
| 78 | `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement` | 54 |
| 79 | `Langlands.Representation.Derivative.MirabolicDerivativeVanishing` | 77, 78 |
| 80 | `Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof` | 79 |
| 81 | `Langlands.Representation.Smooth.SmoothPart.Definitions` | 14 |
| 82 | `Langlands.Representation.Smooth.SmoothPart.BasicStatement` | 81 |
| 83 | `Langlands.Representation.Smooth.SmoothPart.BasicProof` | 82 |
| 84 | `Langlands.Representation.Category.Abelian` | 23, 83, 18 |
| 85 | `Langlands.Representation.Derivative.LevelCalculus` | 54, 57, 80, 84 |
| 86 | `Langlands.Representation.Filtration.Definitions` | - |
| 87 | `Langlands.Representation.Filtration.ObjectDefinitions` | 86 |
| 88 | `Langlands.Representation.Filtration.InvariantBilinear` | 87 |
| 89 | `Langlands.Representation.Conductor.Congruence` | - |
| 90 | `Langlands.Representation.RankinSelberg.Measures` | 25, 89, 2 |
| 91 | `Langlands.Representation.RankinSelberg.RationalZeta` | - |
| 92 | `Langlands.Representation.RankinSelberg.RationalContinuation` | - |
| 93 | `Langlands.LocalFactor.Euler.Definitions` | - |
| 94 | `Langlands.LocalFactor.Euler` | 93 |
| 95 | `Langlands.Representation.RankinSelberg.AnalyticStatement` | 59, 90, 91, 92, 48, 94 |
| 96 | `Langlands.Representation.Derivative.MirabolicMinusPairingTransferStatement` | 51, 88, 95 |
| 97 | `Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement` | 95 |
| 98 | `Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction` | 97 |
| 99 | `Langlands.Representation.Hecke.TestFunction` | 25 |
| 100 | `Langlands.HarmonicAnalysis.RowSchwartzAction` | 1, 99 |
| 101 | `Langlands.Representation.Filtration.InvariantBilinearBounds` | 88 |
| 102 | `Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly` | 98, 100, 101, 3 |
| 103 | `Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement` | 102 |
| 104 | `Langlands.HarmonicAnalysis.RowTestSmoothStatement` | 25, 1 |
| 105 | `Langlands.HarmonicAnalysis.RowTestSmoothProof` | 104 |
| 106 | `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof` | 67 |
| 107 | `Langlands.Group.GL.IntegralSubgroup` | - |
| 108 | `Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof` | 103, 62, 105, 106, 50, 107 |
| 109 | `Langlands.HarmonicAnalysis.CharacterTransport` | 25, 4 |
| 110 | `Langlands.Group.GL.Maps` | 7 |
| 111 | `Langlands.Representation.Whittaker.DualTransform` | 31, 110, 16 |
| 112 | `Langlands.Representation.RankinSelberg.LocalFactor` | 109, 59, 91, 92, 111, 19 |
| 113 | `Langlands.Representation.Whittaker.AlgebraicTwist` | 30, 21 |
| 114 | `Langlands.Representation.Whittaker.Twist` | 113, 31 |
| 115 | `Langlands.Representation.RankinSelberg.TwistInvariance` | 112, 114 |
| 116 | `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof` | 96, 70, 108, 115 |
| 117 | `Langlands.Group.GL.MirabolicProjection` | 9 |
| 118 | `Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing` | 116, 77, 75, 117 |
| 119 | `Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent` | 79, 88 |
| MirabolicHighestLayerLift | `Langlands.Representation.Derivative.MirabolicHighestLayerLift` | 55, 85, 118, 119, 70, 117, 106 |
| 120 | `Langlands.Representation.Induction.Definitions` | 23, 81, 19 |
| 121 | `Langlands.Representation.Derivative.MirabolicPlus` | 51, 117, 120 |
| 122 | `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement` | - |
| 123 | `Langlands.Topology.CompactOpen.NeighborhoodBasis` | 122 |
| 124 | `Langlands.Topology.CompactOpen.ConjugationStabilizer` | - |
| 125 | `Langlands.Representation.Jacquet.PositiveCharacter` | - |
| 126 | `Langlands.Group.HaarModulus` | 123, 124, 12, 125, 21 |
| 127 | `Langlands.Group.GL.MirabolicModulusStatement` | 126, 9, 50 |
| 128 | `Langlands.Group.GL.MirabolicModulusProof` | 127, 106 |
| 129 | `Langlands.Representation.Derivative.MirabolicMinusNormalization` | 128, 51 |
| 130 | `Langlands.Representation.Derivative.MirabolicPlusNormalization` | 121, 129 |
| 131 | `Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps` | 130 |
| MirabolicHighestLayerPlus | `Langlands.Representation.Derivative.MirabolicHighestLayerPlus` | MirabolicHighestLayerLift, 131, 130, 108 |
| MirabolicHighestLayerProof | `Langlands.Representation.Derivative.MirabolicHighestLayerProof` | MirabolicHighestLayerPlus |

## Complete project declaration closure

A private diagnostic (draft module importing this one; diagnostic `daa9b3d6-dc17-4a10-b80a-c3a3b2f741e3`, no errors) traversed
`ConstantInfo.getUsedConstantsAsSet` recursively. It covers types and values,
including opaque proof terms, constructors and recursors. The listing below groups the
project constants (module prefix `Langlands`) by defining module.

- **Main theorem.** From the root `Langlands.Derivative.mirabolicHighestLayer`, the
  traversal visits 40,845 constants. Of these, 917 are project constants in 64 project
  modules. They include `MirabolicHighestLayerLift` (69 constants),
  `MirabolicHighestLayerPlus` (65), this module (27) and the statement module (1).
- **Normalization section.** From the roots `levi_inv_conj_column`, `map_inv_mul_haar`,
  `map_inv_mul_haar_iff`, `psiMinusCharacter_eq_modulus` and
  `phiMinusCharacter_eq_modulus` of `MirabolicHighestLayerLift`, there are 41 further
  project constants not already in the main closure. They lie in 6 modules. The only
  module new relative to the main closure is
  `HarmonicAnalysis.PadicRectangularHaarScalingProof` (Worker 110).

No project axiom occurs. A few helper declarations of the new modules are in neither
closure: `mem_imageStep` (`MirabolicHighestLayerLift`) and `projectionRow_mul`,
`projectionRow_levi`, `thetaFun_eval`, `relationsSubtype_apply`
(`MirabolicHighestLayerPlus`). They are stated and proved for the reader and are not
used. Compiler-generated auxiliaries are shown in braces after their parent; for
example, `foo {_proof_1}` stands for `foo` and `foo._proof_1`. `private` marks private
declarations. Each module line states the namespace of the names that follow. The
number after each module is its count of project constants, auxiliaries included.

### Closure of `Langlands.Derivative.mirabolicHighestLayer`

- `Langlands.Group.GL.Basic` (10) in `Langlands`: `GeneralLinear`; in `Langlands.GeneralLinear`: `determinant`, `determinantContinuous {_proof_1}`, `entry {_proof_1}`, `reindex`, `reindexContinuous {_proof_1, _proof_2}`
- `Langlands.Group.GL.IntegralSubgroup` (3) in `Langlands.GeneralLinearGroup`: `integralSubgroup`, `isCompact_integralSubgroup`, `isOpen_integralSubgroup`
- `Langlands.Group.GL.Mirabolic` (13) in `Langlands.GeneralLinear.Mirabolic`: `entry {_proof_1}`, `rankOneSubsingleton`, `rankOne_eq_one {_proof_1_1, _proof_1_2}`; in `Langlands.GeneralLinear`: `mem_mirabolic`, `mirabolic {_proof_1, _proof_2, _proof_3, _simp_1}`, `private lastRow_mul`
- `Langlands.Group.GL.MirabolicProjection` (35) in `Langlands.GeneralLinear.Mirabolic`: `continuous_lastColumn`, `continuous_plusProjection`, `continuous_projection`, `eq_radicalElement_mul_levi`, `ker_projection`, `lastColumn`, `lastColumn_levi`, `lastColumn_mul`, `lastColumn_mul_last`, `mem_plusSubgroup`, `plusProjection {_proof_1, _proof_2, _proof_3, _proof_4}`, `plusSubgroup`, `plus_eq_radicalElement_mul_successor`, `projection {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6, _proof_7, _proof_8, _proof_9}`, `projection_eq_one_iff`, `projection_levi`, `projection_radicalElement`, `projection_radicalElement_mul_levi`, `radical_normal`, `private lastRow`, `private upperLeft_mul`, `private upperLeft_one`
- `Langlands.Group.GL.MirabolicRadical` (62) in `Langlands.GeneralLinear.Mirabolic`: `continuous_levi`, `continuous_radicalCoordinates`, `continuous_radicalElement`, `continuous_successor`, `levi {_proof_1}`, `leviContinuousEquiv {_proof_1, _proof_2}`, `leviEquiv`, `leviEquiv_symm_entry`, `leviSubgroup`, `leviSubgroup_le_normalizer`, `levi_bottom`, `levi_conjugate_radicalElement`, `levi_first`, `levi_injective`, `levi_last`, `levi_mul_radicalElement`, `mem_radical`, `radical {_proof_1, _proof_2, _proof_3}`, `radicalCoordinates`, `radicalCoordinates_element`, `radicalElement`, `radicalElement_add`, `radicalElement_bottom`, `radicalElement_coordinates`, `radicalElement_first`, `radicalElement_last`, `radicalElement_zero`, `radicalEquiv {_proof_1, _proof_2}`, `radical_rankOneSubsingleton`, `successor {_proof_1}`, `successorContinuousEquiv {_proof_1, _proof_2}`, `successorEquiv`, `successorEquiv_symm_entry`, `successorSubgroup`, `successorSubgroup_le_normalizer`, `successor_first`, `successor_injective`, `private columnGL`, `private columnGL_bottom`, `private columnGL_first`, `private columnGL_last`, `private columnUnit {_proof_1, _proof_2}`, `private continuous_columnUnit`, `private continuous_leviEquiv_symm`, `private continuous_successorEquiv_symm`, `private fixedColumn_mul`, `private levi_conjugate_mem`; in `Langlands.GeneralLinear.Mirabolic.radicalToUpperUnipotent`: `_proof_1`; in `Langlands.GeneralLinear.Mirabolic.columnGL`: `private eq_1`
- `Langlands.Group.GL.Nonarchimedean` (10) in `Langlands`: `valuativeGeneralLinearNonarchimedean`, `private existsSmallMatrix`, `private finitePiBasis`, `private matrixZeroBasis`, `private valuativeBallOpen`, `private valuativeMatrixMonoid {_abel_1, _proof_1, _proof_2}`, `private valuativeMatrixMonoidOpen`
- `Langlands.Group.GL.NonarchimedeanStatement` (1) in `Langlands`: `ValuativeGeneralLinearNonarchimedean`
- `Langlands.Group.GL.NormalizedCharacter` (13) in `Langlands.PadicField.TopologicalData`: `determinantNorm`, `isOpen_ker_determinantNorm`, `isOpen_ker_normalizedAbsUnits {_simp_1_1}`, `normalizedAbsHom {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6}`, `normalizedAbsUnits`, `normalizedAbs_eq_one_iff_discreteValuation`
- `Langlands.Group.GL.Padic` (4) in `Langlands.PadicField.TopologicalData`: `generalLinearDeterminant {_proof_1}`, `generalLinearTopologicalGroup`, `generalLinearTopology`
- `Langlands.Group.GL.RankMaps` (23) in `Langlands.GeneralLinear`: `blockSum`, `blockSumContinuous {_proof_1}`, `blockSum_apply_left`, `blockSum_apply_left_right`, `blockSum_apply_right`, `blockSum_apply_right_left`, `rankInclusion {_proof_1, _proof_2}`, `rankInclusionContinuous {_proof_1}`, `rankInclusion_injective`, `private blockSumCoordinates {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6, _proof_7, _proof_8}`, `private continuous_blockSumCoordinates`
- `Langlands.HarmonicAnalysis.Basic` (7) in `Langlands.HarmonicAnalysis`: `UnitaryAdditiveCharacter`; in `Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter`: `complex`, `complex_apply`, `continuous_toFun`, `mk`, `nontrivial`, `toAddChar`
- `Langlands.HarmonicAnalysis.Conductor` (20) in `Langlands.PadicField.TopologicalData`: `AdditiveTrivialAt`, `additiveConductor`, `additiveConductor_spec`, `additiveLattice {_proof_1, _proof_2, _proof_3, _proof_4}`, `additiveLattice_mono`, `additiveTrivialAt_bddAbove`, `exists_additiveConductor`, `exists_additiveLattice_subset {_proof_1_1}`, `exists_additiveTrivialAt`, `mem_additiveLattice {_simp_1}`, `mem_additiveLattice_iff_div_mem_integers`, `mem_additiveLattice_zero`, `mem_integers_iff_discreteValuation_le_one`, `private conductor_uniformizer_value`
- `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof` (5) in `Langlands.PadicField.TopologicalData`: `integer_annihilator_iff_mem_additiveLattice`, `mem_additiveLattice_iff_exists_integer`, `mul_mem_additiveLattice_iff`, `private conductor_uniformizer_ne_zero`, `private discreteValuation_eq_exp_neg_ord`
- `Langlands.HarmonicAnalysis.PadicLatticeTopology` (2) in `Langlands.PadicField.TopologicalData`: `isCompact_additiveLattice`, `isOpen_additiveLattice`
- `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` (2) in `Langlands.PadicField.TopologicalData`: `isCompact_integers`, `isOpen_integers`
- `Langlands.HarmonicAnalysis.RowSchwartzAction` (6) in `Langlands.HarmonicAnalysis`: `rowHomeomorph {_proof_1, _proof_2, _proof_3, _proof_4}`, `rowHomeomorph_apply`
- `Langlands.LocalField.Definitions` (10) in `Langlands`: `PadicField`; in `Langlands.PadicField`: `Carrier`, `TopologicalData`, `algebra`, `field`, `mk`; in `Langlands.PadicField.TopologicalData`: `localField`, `mk`, `topology`, `valuativeRel`
- `Langlands.LocalField.Normalization.Definitions` (11) in `Langlands.PadicField.TopologicalData`: `Integers`, `ResidueField {_proof_1}`, `discreteValuation {_proof_1, _proof_2}`, `normalizedAbs`, `ord`, `residueCardinality`, `uniformizer {_proof_1}`
- `Langlands.LocalField.Normalization.Proof` (16) in `Langlands.PadicField.TopologicalData`: `discreteValuation_uniformizer`, `finite_residueField {_proof_1_1}`, `normalizedAbs_le_iff_of_ne_zero`, `normalizedAbs_mul`, `normalizedAbs_nonneg`, `normalizedAbs_of_ne_zero`, `normalizedAbs_one`, `normalizedAbs_pos`, `normalizedAbs_zero`, `ord_inv`, `ord_mul`, `ord_one`, `ord_uniformizer`, `ord_zpow`, `residueCardinality_gt_one`
- `Langlands.LocalField.Topology` (1) in `Langlands.PadicField.TopologicalData`: `fieldT2`
- `Langlands.Representation.Category.Abelian` (7) in `Langlands.SmoothRep`: `epi_iff_surjective`, `mono_iff_injective`, `smoothRepProperty_containsZero`, `smoothRepProperty_isClosedUnderQuotients`, `smoothRepProperty_isClosedUnderSubobjects`, `toRep_preservesEpimorphisms`, `toRep_preservesMonomorphisms`
- `Langlands.Representation.Category.Basic` (10) in `Langlands`: `SmoothRep`, `smoothRepProperty`; in `Langlands.SmoothRep`: `hom`, `instAddCommGroupVObjRepSmoothRepProperty`, `instModuleVObjRepSmoothRepProperty`, `isSmooth`, `of`, `ofHom`, `representation`, `toRep`
- `Langlands.Representation.Category.Subquotients` (8) in `Langlands.SmoothRep`: `mkQ`, `mkQ_surjective`, `quotient {_proof_1}`, `stable`, `subrepresentation {_proof_1}`, `subtype`
- `Langlands.Representation.Category.Twist` (5) in `Langlands.SmoothRep`: `twist {_proof_1}`, `twistFunctor {_proof_1, _proof_2}`
- `Langlands.Representation.Compact.Definitions` (5) in `Langlands.Compact`: `averageMap {_proof_1, _proof_2}`, `finite_orbit_of_smooth {_proof_1_1}`
- `Langlands.Representation.Compact.FiniteMean` (33) in `Langlands.Compact`: `finiteMean`, `finiteMean_comp`, `finite_orbit_prod`, `orbit`, `orbitAction {_proof_1, _proof_2, _proof_3}`, `orbitMap {_proof_1, _proof_2, _proof_3}`, `orbitMean`, `orbitMean_add {_proof_1_1, _proof_1_2, _proof_1_3}`, `orbitMean_eq_finiteMean`, `orbitMean_map`, `orbitMean_smul {_proof_1_1}`, `orbitNonempty`, `orbitPretransitive`, `representationAction {_proof_1, _proof_2}`, `private fiberEquiv {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6}`
- `Langlands.Representation.Compact.OrbitMeanTranslation` (1) in `Langlands.Compact`: `orbitMean_apply`
- `Langlands.Representation.Derivative.Homogeneity` (19) in `Langlands.Derivative`: `HasNonzeroDerivative`, `IsHomogeneous`, `hasNonzeroDerivative_iff {match_1_1}`, `isHomogeneous_iff`, `le_level_of_hasNonzeroDerivative`, `level`, `level_eq_zero_iff`, `level_eq_zero_of_subsingleton`, `mirabolicDerivativeOfOrder`, `mirabolicDerivativeOfOrder_obj_subsingleton`, `mirabolicDerivativeOfOrder_one`, `mirabolicDerivative_obj_subsingleton`, `mirabolicRankCast`, `mirabolicRankCast_obj_subsingleton`, `mirabolic_rank_eq_of_order {_proof_1_1}`, `phiMinusIterate_obj_subsingleton`, `private subsingleton_of_surjective`
- `Langlands.Representation.Derivative.Iteration` (5) in `Langlands.Derivative`: `mirabolicDerivative`, `mirabolicDerivative_zero`, `phiMinusIterate {_f, match_1}`
- `Langlands.Representation.Derivative.LevelCalculus` (47) in `Langlands.Derivative.LevelCalculus`: `codRestrict {_proof_1, _proof_2}`, `codRestrict_injective`, `hasNonzeroDerivative_iff_of_iso {match_1_1}`, `hasNonzeroDerivative_level`, `hasNonzeroDerivative_succ_iff {_proof_1_1, _proof_1_2, _proof_1_3, _proof_1_4, _proof_1_5}`, `hasNonzeroDerivative_succ_iff_cast {_proof_1_1, _proof_1_2, _proof_1_3, _proof_1_4, _proof_1_5, _proof_1_6}`, `hom_inv_apply`, `isIso_of_bijective`, `isoRange {_proof_1, _proof_2}`, `iso_hom_injective`, `level_eq_level_phiMinus_succ`, `level_le_level_phiMinus_succ {_proof_1_1, _proof_1_2, _proof_1_3, _proof_1_4, _proof_1_5}`, `level_le_of_imp`, `level_le_one_of_subsingleton_phiMinus`, `level_pos`, `mirabolicDerivative_succ_cast_obj`, `nontrivial_iff_of_iso`, `nontrivial_mirabolicDerivative_cast_congr`, `nontrivial_of_hasNonzeroDerivative`, `nontrivial_of_injective`, `nontrivial_of_level_ne_zero`, `nontrivial_phiMinus_iff {_proof_1_1, _proof_1_2}`, `subrepresentation_nontrivial`, `top_ne_bot`
- `Langlands.Representation.Derivative.MinusVanishing` (29) in `Langlands.Derivative.Mirabolic`: `characterAverage_congr`, `characterAverage_eq_zero_of_le`, `coordinateCharacter {_proof_1}`, `coordinateCharacter_apply`, `coordinateCharacter_eq_of_sub_mem {_abel_1_1}`, `coordinateCharacter_eq_one`, `coordinateCharacter_zero`, `eq_zero_of_forall_characterAverage_eq_zero {_proof_1_1, _simp_1_2, _simp_1_3}`, `exists_forall_characterAverage_eq_zero`, `exists_lastRow_eq_of_ne_zero`, `exists_mem_latticeBox`, `isCompact_radicalBox`, `isOpen_ker_coordinateCharacter`, `levi_inv_mem_relations {_simp_1_1, _simp_1_2}`, `mem_radicalBox`, `radicalBox {_proof_1, _proof_2, _proof_3}`, `radicalBox_mono`, `subsingleton_of_psiMinus_phiMinus {_simp_1_1}`
- `Langlands.Representation.Derivative.MirabolicCharacter` (14) in `Langlands.Derivative.Mirabolic`: `lastCoordinate {_proof_1, _proof_2, _proof_3, _proof_4}`, `mulVec_last`, `theta`, `thetaContinuous {_proof_1}`, `theta_isInvariant`, `theta_isOpen_ker`, `theta_radicalElement`; in `Langlands.PadicField.TopologicalData`: `mirabolicTheta`, `mirabolicTheta_isOpen_ker`
- `Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof` (1) in `Langlands.Derivative`: `mirabolicDerivativeDetection`
- `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement` (1) in `Langlands.Derivative`: `MirabolicDerivativeDetection`
- `Langlands.Representation.Derivative.MirabolicDerivativeVanishing` (10) in `Langlands.Derivative.Mirabolic`: `derivativeDetection`, `radical_acts_trivially_zero`, `relations_one_eq_bot`, `subsingleton_of_forall_mirabolicDerivative`, `subsingleton_of_forall_mirabolicDerivativeOfOrder {_proof_1_1, _proof_1_2, _proof_1_3}`, `subsingleton_of_psiMinus_zero`, `subsingleton_rankCast_mirabolicDerivative_congr`
- `Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent` (3) in `Langlands.Derivative.Mirabolic`: `eq_zero_of_forall_mem_relations {_simp_1_1}`, `radical_acts_trivially_of_phiMinus`
- `Langlands.Representation.Derivative.MirabolicHighestLayerLift` (69) in `Langlands.Derivative.Mirabolic.HighestLayer`: `exists_levi_translates_mem {_proof_1_2, _simp_1_1}`, `exists_mem_liftStep`, `exists_radical_difference`, `hasNonzeroDerivative_of_subrepresentation {_proof_1_1, _proof_1_2, _proof_1_3, _proof_1_4}`, `hasNonzeroDerivative_one_of_subrepresentation`, `imageStep {_proof_1, _proof_2, _proof_3, _proof_4}`, `imageStep_bot`, `imageStep_liftStep`, `imageStep_mono`, `inf_imageStep_ne_bot_iff`, `isOpen_ker_one`, `le_liftStep_imageStep`, `level_subrepresentation_le`, `liftStep {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5}`, `liftStep_imageStep`, `liftStep_mono`, `mem_liftStep`, `mem_relations_subrepresentation`, `ne_bot_iff_exists`, `nontrivial_iff_of_bijective`, `nontrivial_subrepresentation_iff`, `phiMinusSubIso {_proof_1}`, `phiMinus_map_subtype_injective`, `psiImage {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5}`, `psiIso {_proof_1, _proof_2, _proof_3}`, `psiMinusQuotient_injective`, `psiMinus_map_subtype_injective`, `psiPreimage {_proof_1, _proof_2, _proof_3, _proof_4}`, `radical_trivial_of_level_le_one {_proof_1_1}`, `radical_trivial_subrepresentation`, `range_phiMinus_map_subtype`, `stepIso {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6, _proof_7}`, `successor_mem`
- `Langlands.Representation.Derivative.MirabolicHighestLayerPlus` (65) in `Langlands.Derivative.Mirabolic.HighestLayer`: `exists_compact_rows`, `exists_cutoff`, `exists_latticeBox_fixing {_simp_1_1}`, `exists_openSubgroup_fixing`, `exists_orbitFun_eq_near`, `exists_orbitFun_eq_zero_of_mem_relations`, `exists_phiPlusPost_eq_of_mem`, `exists_plusStep`, `exists_plus_mul_levi`, `exists_relation_orbitFun_eq {_abel_1_1}`, `isCompact_quotientSupport_of_projectionRow {_simp_1_1, _simp_1_2, _simp_1_3}`, `liftStep_bot`, `mem_liftStep_top`, `mem_range_plusStepMap`, `mulVec_last_eq_dotProduct`, `mul_radicalElement`, `orbitFun`, `orbitFun_add`, `orbitFun_apply`, `orbitFun_covariant`, `orbitFun_isCompact`, `orbitFun_mul`, `orbitFun_plus_mul`, `orbitFun_radicalElement`, `orbitFun_smul`, `orbitFun_sub`, `orbitFun_sum`, `orbitFun_zero`, `phiMinus_orbitFun`, `phiPlusCharacter_smul_phiMinusCharacter_smul`, `plusStepMap`, `plusStepMap_apply`, `plusStepMap_injective`, `projectionRow {_proof_1}`, `projectionRow_mem_of_orbitFun_ne_zero`, `projectionRow_ne_zero`, `projectionRow_plus_mul`, `relationsSubtype {_proof_1}`, `sum_character_out`, `theta {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6, _proof_7}`, `thetaFun {_proof_1, _proof_2}`, `thetaInv {_proof_1}`, `thetaInv_theta`, `theta_eval`, `theta_injective`, `theta_surjective`, `theta_thetaInv`; in `Langlands.Derivative.Mirabolic.HighestLayer.projectionRow`: `eq_1`
- `Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps` (24) in `Langlands.Derivative.Mirabolic.HighestLayer`: `mem_range_phiPlusPost`, `phiPlusPost {_proof_1, _proof_2, _proof_3, _proof_4}`, `phiPlusPost_injective`, `psiMinusQuotient_psiPlusBaseEmbedding`, `psiPlusBaseEmbedding {_proof_1}`, `psiPlusBaseEmbedding_injective`, `psiPlusBaseEmbedding_quotient`, `psiPlusBaseEmbedding_range`, `private phiPlusPostValue {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6, _proof_7}`, `private psiPlusBaseLinear {_proof_1, _proof_2}`
- `Langlands.Representation.Derivative.MirabolicHighestLayerProof` (27) in `Langlands.Derivative.Mirabolic.HighestLayer`: `IsPlusLayerImage {_proof_1, _proof_2}`, `derivative_cast`, `derivative_obj_succ`, `exists_layer {_proof_1_1, _proof_1_2, _proof_1_3, _proof_1_4, _proof_1_5, _proof_1_6}`, `isPlusLayerImage_liftStep`, `isPlusLayerImage_succ`, `isPlusLayerImage_top`, `isPlusLayerImage_zero`, `plusLayerSucc`, `plusLayerSucc_succ`, `plusLayerSucc_zero`; in `Langlands.Derivative`: `mirabolicHighestLayer {_proof_1_1, _proof_1_2}`, `mirabolicHighestLayer_plusModel {_proof_1_1, _proof_1_2, _proof_1_3, _proof_1_4}`
- `Langlands.Representation.Derivative.MirabolicHighestLayerStatement` (1) in `Langlands.Derivative`: `MirabolicHighestLayerStatement`
- `Langlands.Representation.Derivative.MirabolicLatticeBox` (15) in `Langlands.Derivative.Mirabolic`: `character_dotProduct_eq_one`, `character_mul_eq_one`, `coe_latticeBox {_simp_1_1}`, `eq_one_of_smul_eq_self`, `exists_latticeBox_subset`, `finite_latticeBox_quotient`, `isCompact_latticeBox`, `isOpen_latticeBox`, `latticeBox`, `latticeBox_mono`, `mem_latticeBox {_simp_1_2}`, `mem_latticeBox_of_forall_character_eq_one`, `sum_out_eq_zero`
- `Langlands.Representation.Derivative.MirabolicMinus` (38) in `Langlands.Derivative.Mirabolic`: `continuousPullback {_proof_1}`, `continuousPullbackFunctor {_proof_1, _proof_2}`, `continuousPullbackMap {_proof_1, _proof_2}`, `isOpen_ker_phiMinusCharacter`, `isOpen_ker_psiMinusCharacter`, `ker_phiMinusQuotient`, `ker_psiMinusQuotient`, `phiMinus`, `phiMinusCharacter`, `phiMinusQuotient`, `phiMinusQuotient_radical`, `phiMinusQuotient_surjective`, `phiMinusUnnormalized {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5}`, `phiMinus_action`, `phiMinus_map_quotient`, `psiMinus`, `psiMinusCharacter {_proof_1}`, `psiMinusQuotient`, `psiMinusQuotient_surjective`, `psiMinusUnnormalized {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5}`, `psiMinus_action`, `psiMinus_map_quotient`
- `Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing` (2) in `Langlands.Derivative.Mirabolic`: `radicalRelations_stable {_simp_1_1}`
- `Langlands.Representation.Derivative.MirabolicPlus` (29) in `Langlands.Derivative.Mirabolic`: `continuous_thetaPlus`, `isOpen_ker_thetaPlus`, `phiPlusEval`, `phiPlusEval_covariant`, `phiPlusEval_exists_openSubgroup`, `phiPlusEval_injective`, `phiPlusEval_isCompact_quotientSupport`, `phiPlusMk`, `phiPlusUnnormalized {_proof_1}`, `plusLastCoordinate {_proof_1, _proof_2, _proof_3, _proof_4}`, `plusTwistFunctor {_proof_1, _proof_2, _proof_3}`, `plusTwistRepresentation {_proof_1}`, `psiPlusUnnormalized {_proof_1, _proof_2}`, `thetaPlus`, `thetaPlusContinuous {_proof_1}`, `thetaPlus_apply`, `thetaPlus_isOpen_ker`
- `Langlands.Representation.Derivative.MirabolicPlusNormalization` (22) in `Langlands.Derivative.Mirabolic`: `isOpen_ker_phiPlusCharacter`, `isOpen_ker_psiPlusCharacter`, `phiPlus`, `phiPlusCharacter`, `phiPlusCharacter_eq_inv`, `phiPlusCharacter_mul_phiMinusCharacter`, `phiPlusNormalizedEval`, `phiPlusNormalizedEval_covariant`, `phiPlusNormalizedEval_exists_openSubgroup`, `phiPlusNormalizedEval_injective`, `phiPlusNormalizedEval_isCompact_quotientSupport`, `phiPlusNormalizedMk`, `psiPlus`, `psiPlusCharacter {_proof_1}`, `psiPlusCharacter_eq_inv`, `psiPlusCharacter_mul_psiMinusCharacter`; in `Langlands.Derivative.Mirabolic.phiMinusCharacter`: `eq_1`; in `Langlands.Derivative.Mirabolic.phiPlusHaarHalf`: `_proof_1`, `_proof_6`; in `Langlands.Derivative.Mirabolic.psiMinusCharacter`: `eq_1`; in `Langlands.Derivative.Mirabolic.psiPlusHaarHalf`: `_proof_6`
- `Langlands.Representation.Induction.Definitions` (45) in `Langlands.Induction`: `CompactFunctions`, `EquivariantFunctions {_proof_1}`, `LeftQuotient`, `SmoothFunctions`, `SmoothRep`, `compactFunctionOf`, `compactFunctions {_proof_1, _proof_2, _proof_3, _proof_4, _proof_5, _proof_6, _simp_1, _simp_2}`, `compactFunctionsAddCommGroup`, `compactInduced`, `compactInducedMap {_proof_1, _proof_2}`, `compactInduced_smooth`, `compactInductionFunctor {_proof_1, _proof_2, _proof_3}`, `compactSubrepresentation {_proof_1}`, `equivariantAction`, `eval`, `quotientMap`, `quotientRight {_proof_1}`, `quotientSupport`, `smoothFunctionOf {_proof_1}`, `smoothFunctionsAddCommGroup`, `smoothInduced`, `smoothInducedMap`, `smoothInduced_smooth`, `private compact_map_mem`, `private continuous_quotientRight`, `private eval_locallyConstant`, `private preimage_quotientSupport`, `private quotientSupport_closed`
- `Langlands.Representation.Jacquet.CharacterAveraging` (19) in `Langlands.Jacquet.Localization`: `apply_characterAverage`, `apply_eq_zero_of_mem_relations`, `apply_orbitMean`, `characterAverage`, `characterAverage_eq_orbitMean`, `characterAverage_eq_quotient_sum`, `characterAverage_relation`, `eventually_characterAverage_eq_zero`, `finite_orbit_twistedRestriction`, `isSmooth_twistedRestriction {_simp_1_1, _simp_1_2, _simp_1_3}`, `orbitMean_eq_quotient_sum`, `orbitMean_eq_smul_sum`, `sub_orbitMean_mem`, `twistedRestriction {_proof_1}`, `twistedRestriction_apply`
- `Langlands.Representation.Jacquet.Coinvariants` (2) in `Langlands.Jacquet`: `relations {_proof_1}`
- `Langlands.Representation.Jacquet.Localization` (39) in `Langlands.Jacquet.Localization`: `Coinvariants`, `IsInvariant`, `action`, `conjugate {_proof_1}`, `hom_ext`, `isInvariant_one`, `isSmooth_action`, `ker_mk`, `lift {_proof_1}`, `map {_proof_1}`, `mapLinear {_proof_1}`, `map_comp`, `map_id`, `mk`, `mk_apply_subgroup`, `mk_eq_iff`, `mk_eq_zero`, `mk_surjective`, `quotientMap {_proof_1, _proof_2}`, `relations {_proof_1}`, `relations_le_ker_iff {_simp_1_1, _simp_1_2}`, `relations_one`, `relations_stable`, `smoothFunctor {_proof_1, _proof_2}`, `smoothObject {_proof_1}`, `sub_mem_relations`; in `Langlands.Jacquet.Localization.relations`: `eq_1`
- `Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof` (11) in `Langlands.RankinSelberg.EqualRankFrobenius`: `exists_lastRow_eq`, `isOpenMap_lastRow`, `isOpen_orbitSet`, `lastRow_lift`, `lastRow_mem_orbitSet`, `lastRow_mirabolic_mul`, `lift`, `mem_orbitSet`, `mul_inv_mem_mirabolic_of_lastRow_eq`, `orbitSet`; in `Langlands.RankinSelberg.EqualRankFrobenius.orbitSet`: `eq_1`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof` (12) in `Langlands.RankinSelberg`: `continuous_lastRow`, `isEmbedding_generalLinear_val`, `isOpenEmbedding_generalLinear_val {_simp_1_1, _simp_1_2, _simp_1_3, _simp_1_4}`, `lastRow_image_mem_nhds`, `lastRow_mem_image_iff`, `lastRow_ne_zero`, `mem_mirabolic_iff_lastRow {_simp_1_2}`
- `Langlands.Representation.RankinSelberg.QuotientIntegrals` (2) in `Langlands.RankinSelberg`: `lastRow`, `lastRow_mul_eq_vecMul`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` (1) in `Langlands.PadicField.TopologicalData`: `mem_additiveLattice_of_forall_mul_eq_one`
- `Langlands.Representation.Smooth.Definitions` (3) in `Langlands`: `IsSmooth`, `IsSmoothVector`, `fixedVectors`
- `Langlands.Representation.Smooth.SmoothPart.BasicProof` (1) in `Langlands`: `isSmoothVector_zero`
- `Langlands.Representation.Smooth.SmoothPart.Definitions` (15) in `Langlands`: `smoothInclusion {_proof_1, _proof_2}`, `smoothLift {_proof_1, _proof_2}`, `smoothMap {_proof_1}`, `smoothPart`, `smoothSubrepresentation {_proof_1}`, `smoothVectors {_proof_1, _proof_2, _proof_3}`
- `Langlands.Representation.Smooth.Transfer.PullbackProof` (2) in `Langlands`: `isSmoothVector_comp`, `isSmooth_comp`
- `Langlands.Representation.Smooth.Transfer.SubquotientProof` (4) in `Langlands`: `isSmoothVector_map`, `isSmoothVector_of_injective`, `isSmooth_of_injective`, `isSmooth_of_surjective`
- `Langlands.Representation.Twist.ContinuousCharacterProof` (2) in `Langlands`: `complex_eq_one_of_forall_norm_pow_sub_one_lt`, `isOpen_ker_of_continuous_complex_character`
- `Langlands.Representation.Twist.Definitions` (7) in `Langlands`: `twist {_proof_1, _proof_2, _proof_3}`, `twistIntertwining {_proof_1, _proof_2}`
- `Langlands.Representation.Twist.RealPower` (5) in `Langlands`: `isOpen_ker_realPowerCharacter`, `ker_le_realPowerCharacter_ker`, `positiveUnitsToComplex`, `realPowerCharacter`, `realPowerCharacter_neg`
- `Langlands.Representation.Twist.SmoothProof` (2) in `Langlands`: `isSmoothVector_twist_iff`, `isSmooth_twist_iff`
- `Langlands.Topology.Nonarchimedean.Subgroup` (1) in `Langlands`: `subgroupNonarchimedean`

### Additional closure of the `Normalization` section

- `Langlands.Group.GL.NormalizedCharacter` (1) in `Langlands.PadicField.TopologicalData`: `normalizedAbsUnits_coe`
- `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof` (14) in `Langlands.HarmonicAnalysis`: `haarMeasure_map_in_coordinates`, `haarMeasure_map_matrix`, `haarMeasure_map_rectangular`, `padicRectangularHaarScaling`, `productMeasure_map_diagonal`, `productMeasure_map_matrix`, `productMeasure_preserving_transvection {_simp_1_1, _simp_1_2}`, `rectangularCoordinates {_proof_1, _proof_2, _proof_3}`, `rectangularCoordinates_mul`
- `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof` (10) in `Langlands.HarmonicAnalysis`: `padicScalarHaarScaling`; in `Langlands.PadicField.TopologicalData`: `haarMeasure_regular`, `pseudoMetrizableSpace`, `secondCountableTopology`, `sigmaCompactSpace`, `private distribHaarChar_eq_normalizedAbsUnits`, `private residueCardinality_mul_measure_maximalIdeal`, `private smul_integers_eq`, `private uniformizer_ne_zero`, `private uniformizer_smul_integers`
- `Langlands.LocalField.Definitions` (6) in `Langlands.PadicField.TopologicalData`: `moduleTopology`; in `Langlands.PadicField`: `canonicalNormedAlgebra`, `canonicalNormedField {_proof_1}`, `canonicalTopology`, `finiteDimensional`
- `Langlands.LocalField.Normalization.Proof` (4) in `Langlands.PadicField.TopologicalData`: `normalizedAbs_le_one_iff_mem_integers`, `ord_zero`, `topology_eq_canonicalModule`, `topology_eq_canonicalNormTopology`
- `Langlands.Representation.Derivative.MirabolicHighestLayerLift` (6) in `Langlands.Derivative.Mirabolic.HighestLayer`: `levi_inv_conj_column`, `map_inv_mul_haar`, `map_inv_mul_haar_iff {_proof_1_1}`, `phiMinusCharacter_eq_modulus`, `psiMinusCharacter_eq_modulus`

## Authorship

- Worker 805 wrote the three new modules `MirabolicHighestLayerLift`,
  `MirabolicHighestLayerPlus` and `MirabolicHighestLayerProof` and their Markdown: the
  construction (`liftStep`, `imageStep`), the element-level left exactness, the
  lattice comparison, the base step, the orbit isomorphism `R(B) ≅ Φ⁺(Φ⁻ B)`, the plus
  model, the induction, the homogeneity criterion and the normalization section.
- Worker 806 is a coauthor. `exists_levi_translates_mem` (in
  `MirabolicHighestLayerLift`) adapts the averaging argument of Worker 806's published
  `eq_bot_or_eq_top_of_radicalQuotient` (module
  `Langlands.Representation.Derivative.MirabolicMinusIrreducibleProof`, which is not
  imported). The adaptation extracts the averaging construction of that proof as a
  standalone lemma. It drops the irreducibility and surjectivity hypotheses, keeps the
  averaged vector inside a given invariant subspace `S`, and normalizes it so that
  `q(x'') = q(x)`. It returns the averaged vector instead of the dichotomy
  `σ = ⊥ ∨ σ = ⊤`. Worker 806 also wrote the imported `MirabolicLatticeBox` helper.
- Worker 1185 is a coauthor. Worker 1185 wrote the imported helper
  `MirabolicHighestLayerPlusMaps` (published artifact
  `a88fbb0e-6c1c-4f3a-9151-b45d9b90f868`, coauthored with Worker 805, who designed its
  interfaces). It supplies `phiPlusPost` and `psiPlusBaseEmbedding`, under a split of
  this task's work agreed with Worker 805. Worker 1185 also audited the normalization
  comparison against BZ77 §1.8.
- Worker 440 authored the statement draft and contract, and Worker 658 completed the
  statement companion, source verification and this proof task's arrangement. Workers
  864/700 supplied parent planning. Imports of other published modules (authors listed
  in the dependency audit, including Workers 723, 984, 749, 710 and 15) confer no
  coauthorship.
