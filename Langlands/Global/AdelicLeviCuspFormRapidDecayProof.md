# Rapid decay of Levi cusp forms on norm-one representatives: proof

Module `Langlands.Global.AdelicLeviCuspFormRapidDecayProof` proves the Library proposition
`Langlands.Global.LeviCuspFormRapidDecayStatement` (module
`Langlands.Global.AdelicLeviCuspFormRapidDecayStatement`):

```lean
theorem Langlands.Global.leviCuspFormRapidDecay : LeviCuspFormRapidDecayStatement.{u}
```

for number fields `F : Type u` in every universe `u`. Lean reports the axioms `propext`,
`Classical.choice` and `Quot.sound`.

| Declaration | Kind | Source |
| --- | --- | --- |
| `plotSmoothEnvelopingAction_directionalWord_slice` | theorem | derived (comparison of two derivative conventions) |
| `leviCuspFormRapidDecay` | theorem | Mœglin–Waldspurger I.2.12 (Corollary) and I.2.18 for a standard Levi |

## The statement proved

For a compatible standard parabolic family `fam` of a group `G` over a number field `F`, a
subgroup `K ≤ G(𝔸)` whose inverse image in every standard Levi `M_J(𝔸)` is maximal compact, a
matrix representation `rho : G → GL_N` with `N > 0`, a standard index `J`, a cusp form `ψ` on
`M_J(F) \ M_J(𝔸)` (`fam.IsLeviCuspForm Kinf rho J ψ`, with `Kinf = K.comap (ofInfinite F G)`)
and a real `e ≥ 0`, there is `B ≥ 0` such that every class of `M_J(F) \ M_J(𝔸)^1` has a
representative `m ∈ M_J(𝔸)^1` with `H(ι m)^e · |ψ(m)| ≤ B`. Here `H = adelicHeight F G rho` and
`ι = map F (fam.M J) G (fam.l J ≫ fam.p J)` is the Levi inclusion.

## The slice lemma

`plotSmoothEnvelopingAction_directionalWord_slice` compares the two ways the Library
differentiates a function `φ : G(𝔸) → ℂ` along a word `s = [X₁, …, X_k]` of real archimedean
tangent directions, for an affine group `G` with a chosen smooth atlas `hG`:

- `adelicIteratedDirectionalValue hG s φ` (module `Langlands.Global.AdelicMaximalUnipotentDecay`)
  applies the right-orbit derivatives `adelicDirectionalValue hG Xᵢ` to `φ` on `G(𝔸)`, the
  last letter first;
- `plotSmoothEnvelopingAction F G hG hcalc` (module
  `Langlands.Automorphic.GroupSchemeEnvelopingAction`) is the action of the complex enveloping
  algebra on plot-smooth functions on `G(F_∞)`, and `adelicDirectionalWordEnveloping hG s`
  (module `Langlands.Global.AdelicUniformDirectionalGrowth`) is the ordered product of the
  generators `ι(1 ⊗ Xᵢ)`.

If the archimedean slice `x ↦ φ(x, b)` at a finite adelic point `b` is plot-smooth, then for every
`a ∈ G(F_∞)`

`adelicIteratedDirectionalValue hG s φ (pair a b) =
  (plotSmoothEnvelopingAction (adelicDirectionalWordEnveloping hG s) (slice of φ at b)) a`.

The proof is induction on `s`. The empty word is the unit of the enveloping algebra, which acts
as the identity, and both sides are `φ(pair a b)`. For `X :: s`, the enveloping action is an
algebra homomorphism, the generator `ι(1 ⊗ X)` acts as `plotSmoothDifferential X`
(`plotSmoothEnvelopingAction_real_generator`), which is `groupDirectionalValue X` on the
underlying function, and `adelicDirectionalValue_pair` writes the adelic derivative at
`pair a b` as `groupDirectionalValue X` of the slice at `b` of `adelicIteratedDirectionalValue hG s φ`.
By the induction hypothesis, applied at every point, that slice is the function on the right
for `s`. This is the slice-wise form of `evaluate_adelicDirectionalWordEnveloping`, which treats
the carrier of rational finite plot-smooth functions.

## Proof of `leviCuspFormRapidDecay`

Write `M = fam.M J`, `ρ_M = fam.l J ≫ fam.p J ≫ rho` (a matrix representation of `M`) and
`H_M = adelicHeight F M ρ_M`.

1. **Unpacking the cusp form.** `fam.IsLeviCuspForm Kinf rho J ψ` is the conjunction of
   `IsAutomorphicFunctionOn` for `M`, its atlas `fam.leviSmooth J`, the commutator witness
   `adelicDifferentialCommutator_of_smooth`, the subgroup `rationalSubgroup F M`, the compact
   group `fam.leviInfiniteCompact Kinf J` and `ρ_M`, together with `fam.IsLeviCuspidal J ψ`. The
   first gives left `M(F)`-invariance, `IsAdelicSmoothFunction`, finiteness under
   `fam.leviInfiniteCompact Kinf J`, finiteness under the centre of the enveloping algebra and
   moderate growth for the source norm of `ρ_M`. The second is, by definition, the predicate
   `HasZeroProperParabolicConstantTerms ψ` for the group `M`: the constant terms along all proper
   parabolic subgroups of `M` vanish.
2. **The Levi.** `M` is connected reductive, because the family's compatibility data at `J`
   records the rational Levi subgroup `fam.l J` (`(fam.isCompatible J).levi.isConnectedReductive`).
   The hypothesis that `K.comap ι` is maximal compact in `M(𝔸)` gives, by
   `StandardParabolicFamily.leviInfiniteCompact_isMaximal` (module
   `Langlands.Global.AdelicStandardLeviInfiniteCompact`), that `fam.leviInfiniteCompact Kinf J` is
   a maximal compact subgroup of `M(F_∞)`.
3. **One exponent for all derivatives.** `exists_uniformGrowth_functionInfiniteSlices` (module
   `Langlands.Automorphic.GroupSchemeInvariantFunctionGrowth`), applied to `M`, `ρ_M`, `N > 0`,
   the maximal compact subgroup of step 2 and the finiteness and growth conditions of step 1,
   gives a real `R ≥ 0` such that every element `a` of the enveloping algebra of `M(F_∞)` has a
   constant `C_a ≥ 0` with `|(a · slice of ψ at b)(x)| ≤ C_a H_M(pair x b)^R` for all `b` and `x`.
   For a word `s`, take `a = adelicDirectionalWordEnveloping (fam.leviSmooth J) s`. Writing an
   adelic point as `pair` of its two projections (`pair_projections`) and using the slice lemma
   gives `|adelicIteratedDirectionalValue (fam.leviSmooth J) s ψ (x)| ≤ C_s H_M(x)^R` at every
   `x ∈ M(𝔸)`, with the same `R` for all words.
4. **Decay on a norm-one cover.** `AdelicGroupPoints.adelicNormOneCuspidalRapidDecay` (module
   `Langlands.Global.AdelicNormOneCuspidalRapidDecay`), applied to `M`, its atlas and `ρ_M`, with
   `M` connected reductive and `N > 0`, gives a set `S ⊆ M(𝔸)^1` such that every norm-one point
   `y` has a rational point `q ∈ M(F)` with `q y ∈ S`. Its decay clause, applied to `ψ` with the
   smoothness, rational invariance and cuspidality of step 1, the exponent `R` and the derivative
   bounds of step 3, and to the integer `n = ⌈e⌉₊`, gives `C ≥ 0` with `|ψ(z)| H_M(z)^n ≤ C` for
   every `z ∈ S`. Take `B = C`.
5. **Representatives.** A class of `M(F) \ M(𝔸)^1` is the class of some `y ∈ M(𝔸)^1`
   (`LeftCosetSpace.mk_surjective`). Choose `q` with `z = q y ∈ S`; then `z` is norm one. The
   rational point `q` is a norm-one point (`rationalNormOne`), so it lies in
   `rationalNormOneSubgroup F M`, and `z` represents the class of `y`
   (`LeftCosetSpace.mk_subgroup_mul`).
6. **Heights.** The adelic points of a composite morphism are the composite of the adelic point
   maps (`AdelicGroupPoints.map_comp_apply_of_hom`), so `H_M(z) = H(ι z)`. The height is at least
   one (`one_le_adelicHeight`, using `N > 0`) and `e ≤ ⌈e⌉₊`, so
   `H(ι z)^e |ψ(z)| ≤ H(ι z)^{⌈e⌉₊} |ψ(z)| = |ψ(z)| H_M(z)^{⌈e⌉₊} ≤ C`.

The hypotheses that `K` itself is maximal compact in `G(𝔸)`, that `P₀(𝔸) K = G(𝔸)`, that `rho`
is a closed embedding and that `e ≥ 0` are not used. The maximality of the inverse image of `K`
is used only at the given index `J`.

## Sources and correspondence

C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
registered as `moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.2_pp_18_40_Automorphic_forms_growth_constant_terms.pdf`:

- I.2.17, printed pp. 37–39: the Lemma on p. 38 (a reproducing function for finitely many spaces
  of automorphic forms) and the following sentence on p. 39, with I.2.5: an automorphic form and
  its derivatives have uniformly moderate growth. Step 3 obtains this uniformity on `M` from the
  Library's theorem `exists_uniformGrowth_functionInfiniteSlices`, whose Markdown describes its
  route through an elliptic interior estimate and an adapted Casimir element instead of a
  reproducing function.
- I.2.12, printed pp. 34–35: rapidly decreasing functions on a Siegel domain and the Corollary
  that `sφ` is rapidly decreasing for smooth `K`-finite `φ` whose derivatives have uniformly
  moderate growth.
- I.2.18, printed p. 39: for a cuspidal automorphic form all proper constant terms vanish, so it
  is rapidly decreasing by Corollary I.2.12.

These are applied, as in the Markdown of the statement, to the reductive group `M_J` in place of
`G`. The Lean proof differs from the outline there in one respect. It does not compare the height
with the Siegel coordinate `m_{P₀}(m)^{λ₀}` (MW I.2.2 (vi)): the decay theorem
`adelicNormOneCuspidalRapidDecay` already bounds `|ψ|` against every power of the height
`H_M` on its norm-one cover, and `H_M` is the ambient height along `ι` by step 6.
