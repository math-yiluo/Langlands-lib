# Word derivatives on the norm-one adelic group

Let `A` be an embedded Lie atlas on `G(F∞)¹` with tangent space `Fin e → ℝ` at the identity. The
module `Langlands.Automorphic.GroupSchemeNormOneWords` iterates the coordinate derivatives
`normOneDirectional A (Pi.single l 1)` of `Langlands.Automorphic.GroupSchemeNormOneDirectional`
along words and relates them to the differential operators `normOneDifferential A` of
`Langlands.Automorphic.GroupSchemeNormOneSmooth`. All declarations are in
`Langlands.Automorphic.GroupSchemeFunctions`.

- `normOneWordDerivative A w f`: for the empty word `f`; for `l :: w` the derivative along the
  coordinate direction `l` of `normOneWordDerivative A w f`. So the last letter is applied first.
- `normOneWord w`, the word `w` as an element of `NormOneDifferentialWord e` with coefficient `1`;
  it has order at most the length of `w` (`normOneWord_orderLE`).
- `normOneWordsUpTo e r`, the finite set of words of length at most `r`
  (`mem_normOneWordsUpTo`).
- `normOneInfiniteSlice_normOneWordDerivative` and `normOneDifferential_normOneWord`: the slices of
  a word derivative are the Lie word derivatives of the slices, and
  `normOneDifferential A (normOneWord w) f = normOneWordDerivative A w f`.
- `isNormOneCr_normOneWordDerivative`: if `f` satisfies `IsNormOneCr A n K₀` and `|w| ≤ n`, then
  `normOneWordDerivative A w f` satisfies `IsNormOneCr A (n − |w|) K₀`
  (`isNormOneCr_normOneDirectional` letter by letter).
- `mdifferentiable_slice_normOneWordDerivative`: for `|w| < n` its slices are differentiable.
- `measurable_normOneWordDerivative`: for a jointly measurable family of inputs of class `Cⁿ` and
  `|w| ≤ n`, `(o, y) ↦ normOneWordDerivative A w (φ o) y` is jointly measurable
  (`measurable_normOneDirectional` letter by letter).
- `continuous_infiniteNormOneInclusion`: the inclusion `G(F∞)¹ → G(𝔸)¹` is continuous.
- `isNormOnePathDerivative_comp_retraction`: let `r : G(𝔸) → G(𝔸)¹` fix the norm-one points and let
  `ψ` on `G(𝔸)¹` have differentiable slices and continuous coordinate derivatives. Then
  `IsNormOnePathDerivative A (ψ ∘ r) (fun l => D_l ψ ∘ r)`. At a norm-one point `y` the path
  `y c(t)` stays in `G(𝔸)¹`, where `r` is the identity; `hasDerivAt_normOne_path` and the
  fundamental theorem of calculus give the identity.
