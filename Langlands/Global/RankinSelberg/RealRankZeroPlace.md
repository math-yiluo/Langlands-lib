# Rank-one automorphic realizations at a real place

Helper module for the rank-one (`r = 0`) case of
`Langlands.Global.RankinSelbergGlobal.RealEqualFunctionalEquationStatement`.
Every declaration is proved; there are no hypotheses beyond those stated in
each declaration and no axioms are added.

All declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealRankZero`. `F` is a field; the sections after
the Lie-algebra lemmas assume `[NumberField F]`. `S : OperatorRealization F 1` is a Library
automorphic operator realization for `GL₁`, with representation space `S.Space`. The
sections that work with `S.Space` declare local `AddCommGroup` instances for the
Library's submodule types; these are the instances `Submodule.addCommGroup` that the
Library uses.

## `GL₁` is commutative

- `matrix_fin_one_mul_comm`, `gl_fin_one_mul_comm`: `1 × 1` matrices over a commutative
  (semi)ring commute, and so do invertible ones.
- `realLieConjugation_rankOne`, `complexLieConjugation_rankOne`: the adjoint action of
  `GL₁` of the infinite adeles on the real Lie algebra `RealLieAlgebra F 1` and on its
  complexification is trivial. The first is `g X g⁻¹ = X` for `1 × 1` matrices; the second
  follows on pure tensors.
- `envelopingConjugation_rankOne`: the induced action on the enveloping algebra is
  trivial. Both sides are algebra maps out of the universal enveloping algebra that agree
  on generators (`UniversalEnvelopingAlgebra.hom_ext`).
- `realLieAlgebra_lie_rankOne`, `complexLieAlgebra_lie_rankOne`: the Lie brackets vanish.
- `envelopingAlgebra_mul_comm_rankOne`: the enveloping algebra `EnvelopingAlgebra F 1`
  is commutative. Every generator commutes with every other generator (their commutator is
  the image of a vanishing bracket), so each generator lies in the centre, because the
  generators generate the algebra (the Library's
  `LieCasimir.enveloping_adjoin_range`). Hence the whole algebra lies in its centre.

## Schur scalars

Section `Schur` (with `[NumberField F]`).

- `compactRepresentation_commute_rankOne`: compact translations commute with each other.
- `compactRepresentation_envelopingAction_rankOne`: compact translations commute with the
  enveloping action, because the Library's compatibility
  `compactRepresentation_envelopingAction` involves `envelopingConjugation`, which is
  trivial here.
- `envelopingAction_commute_rankOne`: enveloping operators commute with each other.
- `exists_compactRepresentation_eq_smul`: if `S` is irreducible, every compact
  translation `S.compactRepresentation k` is multiplication by a scalar `c ∈ ℂ`.
- `exists_envelopingAction_eq_smul`: if `S` is irreducible, every enveloping operator
  `S.envelopingAction a` is multiplication by a scalar.

Both use the Library's Schur lemma `OperatorRealization.exists_eq_smul_of_commute` and
`commute_representation_of_commute`: the operator commutes with the finite-adelic
translations (Library compatibilities), with all compact translations and with the whole
enveloping action (the three lemmas above).

## The rank-one Whittaker coefficient

Section `Whittaker`. The scheme `Scheme F n` of `GL_n` is given local `IsAffine` and
`Smooth` instances from the Library's `GeneralLinear.isAffine_groupScheme` and
`GeneralLinear.smoothStatement`.

- `upperUnipotent_one_adelicPoints_eq_one`: every adelic point of the upper unitriangular
  subgroup functor of `GL₁` is `1`. A `1 × 1` upper unitriangular matrix has diagonal
  entry `1` (`GeneralLinear.mem_blockUnipotent`), and points are determined by their
  matrices (`GeneralLinear.pointsEquiv`).
- `cuspWhittaker_rankZero`: for `T : CuspidalOperatorRealization F 0` (that is, `GL₁`),
  every additive character `ψ` of the adeles and `x ∈ T.Space`, the Library's global
  Whittaker coefficient `cuspWhittaker F T ψ x` equals the cusp function
  `cuspFunction F T x`. The quotient `N₁(F) \ N₁(𝔸)` is a single point, its normalized
  Haar measure is a probability measure, and the generic character is the empty sum, so
  the defining integral is the value of the form at `g`.

## Coordinates at a real place

Section `Coordinates`. `RP` and `CP` are the real and complex infinite places of `F`.

- `archimedeanGL_ext`: an element of `ArchimedeanGL F n` is determined by its matrices
  `realMatrix` at the real places and `complexMatrix` at the complex places.
- `realMatrix_realPlaceGL`, `complexMatrix_realPlaceGL`: the Library embedding
  `realPlaceGL F n v` puts `g` at the real place `v` and `1` everywhere else.
- `realPlaceCompactInclusion_val`: the Library's inclusion of `k ∈ O(n)` at `v` into the
  standard compact subgroup is the inverse of the archimedean coordinate map applied to
  `realPlaceGL F n v k`.
- `scalarUnit : ℝˣ →* GL₁(ℝ)` sends `t` to the `1 × 1` matrix `(t)`; `scalarUnit_val`
  is its matrix. `scalarUnit_entry`: every `g ∈ GL₁(ℝ)` is `scalarUnit` of its entry.
- `oneParameter_realPlaceLieInclusion_one`: the Library's one-parameter subgroup
  `u ↦ exp(u X)` for `X = realPlaceLieInclusion F 1 v 1` (the element `1 ∈ 𝔤𝔩₁(ℝ)` at
  the place `v`) is `realPlaceGL F 1 v (scalarUnit (exp u))`. At each place the
  coordinate projection is a continuous algebra map, so it commutes with the exponential
  (`NormedSpace.map_exp_of_mem_ball`); at `v` the projection of `X` is `1` and
  `exp(u · 1) = (eᵘ)`; at the other places it is `0` and `exp 0 = 1`.

## A linear differential equation

- `eq_exp_mul_of_hasDerivAt`: if `h : ℝ → ℂ` satisfies `h'(u) = m h(u)` for all `u`, then
  `h(u) = exp(m u) h(0)`. The function `exp(-m u) h(u)` has derivative `0`, so it is
  constant.

## The character of a rank-one realization at a real place

Section `Place`.

- `minusOneOrthogonal`: the element `-1` of `O(1)` (Mathlib's
  `Matrix.unitaryGroup (Fin 1) ℝ`); `toUnits_minusOneOrthogonal`: as an invertible
  matrix it is `scalarUnit (-1)`.
- `determinant_scalarUnit`: `det (scalarUnit t) = t`.
- `realPlaceAdelic F v : GL₁(ℝ) →* AdelicGL F 1`: the adelic point `ι_v(g)` with
  archimedean component `g` at `v` and `1` at all other places and at the finite places.
- `evaluate_smul`: the evaluation of a realized vector is linear in scalars.
- `evaluate_mul_realPlaceAdelic`: let `c : RealCharacterData` with character `χ_c`.
  Assume that `-1 ∈ O(1)` acts on `S.Space` at `v` by `χ_c(-1)` (`hε`) and that the Lie
  operator of `1 ∈ 𝔤𝔩₁(ℝ)` at `v` acts by `c.exponent` (`hμ`). Then for every
  `g ∈ GL₁(ℝ)`, every `f ∈ S.Space` and every adelic `y`,
  `φ_f(y · ι_v(g)) = χ_c(det g) · φ_f(y)`, where `φ_f` is the continuous function that
  `S` attaches to `f`.

  Proof: the property is closed under products. It holds for `g = -1` by `hε` and the
  Library's `evaluate_realPlaceCompactRepresentation`. For `g = (eᵘ)` the function
  `h(u) = φ_f(y · ι_v(eᵘ))` satisfies `h' = c.exponent · h` by the Library's
  `hasDerivAt_evaluate_oneParameter` and `hμ`, so `h(u) = exp(c.exponent · u) h(0)`, which
  is `χ_c(eᵘ) φ_f(y)` by `RealCharacterData.character_eq`. Every positive `t` is
  `e^{log t}`, every negative `t` is `(-1) · (-t)`, and every `g` is `scalarUnit` of its
  entry.

## Provenance

These are standard facts about characters of `GL₁(ℝ) = ℝˣ`: Schur's lemma for a
commutative operator algebra, and the determination of a continuous character of `ℝˣ` by
its value at `-1` and its derivative at `1`. The formalization against the Library's
operator-realization interface is internal to this project.
