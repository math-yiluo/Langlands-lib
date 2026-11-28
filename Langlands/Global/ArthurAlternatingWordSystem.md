# The system of derivatives of an alternating constant term

Let `G` be a connected reductive group over a number field `F`, with maximal split torus `i`,
generic cocharacter `ν` and simple roots `Δ₀`, and let `R ⊆ S ⊆ Δ₀`. For a continuous function `f`
on `G(𝔸_F)` invariant under left translation by `G(F)`, Arthur's alternating constant term
`alternatingConstantTerm R S f = ∑_{R ⊆ P ⊆ S} (−1)^{|Δ₀| − |P|} f_P` is the sum appearing in
Arthur, *An introduction to the trace formula* (2005), (13.7), printed p. 71; each `f_P` is the
normalized constant term along the unipotent radical of the standard parabolic subgroup `P`.

Let `At` be an embedded Lie atlas on `G(F∞)¹` and `φ` a function on `G(𝔸_F)¹` satisfying
`IsNormOneCr At r K₀` for an open compact subgroup `K₀` of `G(𝔸_f)`. The module
`Langlands.Global.ArthurAlternatingWordSystem` defines, for `n ≤ r`,

`alternatingWordSystem hG hi At R S n φ w = alternatingConstantTerm R S (normOneExtension hG (D_w φ))`

for words `w` of length at most `n` (with `D_w φ = normOneWordDerivative At w φ`), and `0` for longer
words, and proves for it the hypotheses of `normOneFamilyDecayModulo`. All declarations are in
`Langlands.Global.ArthurTruncation`.

- `normOneWordDerivative_props`: for `|w| ≤ r`, `D_w φ` is continuous, left invariant under the
  rational norm-one points and right invariant under `K₀` (`isNormOneCr_normOneWordDerivative`).
- `alternatingWordSystem_eq`: for `|w| ≤ n` the system is the alternating constant term of the
  element `normOneExtensionCRF` of `ContinuousRationalFunctions F G`. Hence the results of
  `Langlands.Global.ArthurAlternatingConstantTerm` for continuous left `G(F)`-invariant inputs
  apply.
- `continuous_alternatingWordSystem`, `measurable_alternatingWordSystem`: continuity, and joint
  measurability for a jointly measurable family `φ o`
  (`measurable_constantTerm_normOneExtension_family`, `measurable_normOneWordDerivative`).
- `alternatingWordSystem_mul_ofFinite`: right invariance under `K₀`
  (`constantTerm_mul_right_of_invariant`: constant terms of right-invariant functions are right
  invariant).
- `alternatingWordSystem_isRationalInvariant`: invariance under the rational points of every
  standard unipotent radical (`alternatingConstantTerm_isRationalInvariant`).
- `alternatingWordSystem_radical_mul`: left invariance under the adelic points of the radical of
  `S` (`alternatingConstantTerm_radical_mul`).
- `constantTerm_alternatingWordSystem_eq_zero`: for `α ∈ S \ R`, the constant term along the
  radical of the maximal standard parabolic subgroup `Δ₀ \ {α}` vanishes
  (`constantTerm_alternatingConstantTerm_eq_zero`).
- `isNormOnePathDerivative_alternatingWordSystem`: for `|w| < n`,
  `IsNormOnePathDerivative At (system at w) (fun l => system at l :: w)`. The extension of `D_w φ`
  satisfies the identity with derivatives the extensions of `D_{l :: w} φ`
  (`isNormOnePathDerivative_comp_retraction`); the constant terms preserve it
  (`isNormOnePathDerivative_constantTerm_normOneExtension`) and so does the finite signed sum
  (`isNormOnePathDerivative_sum`).
- `exists_lintegral_alternatingWordSystem_le`: there is `Cg ≥ 0`, depending on `R`, `S`, the
  height `H = adelicHeight F G rho` and `n₀`, such that for every family over an arbitrary measure
  space, every word `w` and every `M`: if `∫_Ω ‖D_w (φ o) y‖ dm ≤ H(y)^{n₀} M` for all
  `y ∈ G(𝔸_F)¹`, then `∫_Ω ‖system at w (x)‖ dm ≤ Cg H(x)^{n₀} M` for all `x ∈ G(𝔸_F)¹`. Each
  constant term is bounded by `exists_lintegral_constantTerm_normOneExtension_le`, and
  `H(h x) ≤ H(h) H(x)` (`adelicHeight_mul_le`) with `H` bounded on the compact sets of radical
  points.
