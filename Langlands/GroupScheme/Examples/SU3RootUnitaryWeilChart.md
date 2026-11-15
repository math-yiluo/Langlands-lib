# Basis coordinates on the Weil restriction of the unitary parameter group

Module `Langlands.GroupScheme.Examples.SU3RootUnitaryWeilChart`, namespace
`Langlands.GroupScheme.SU3Root.WeilChart`.

## Setting

`K` is a field, `E / K` a finite extension with a `K`-basis `b : Module.Basis (Fin n) K E`,
and `L / E` a separable quadratic extension. `U_{L/E}` is the published unitary parameter
group `SU3Root.unitaryParameterGroup E L`, whose points over an `E`-algebra `S` are the
pairs `(u, v)` with `v + σ v = u σ u` (`tensorParameters E L S`). Its canonical chart
`chartData E L` (`canonicalCoordinateData`) writes these parameters in bilinear coordinates
`(x, z)` with `x : ULift (Fin 2) → S` and `z : S`, with group law
`(x, z)(x', z') = (x + x', z + z' + form c x x')` for the chart cocycle coefficients `c`.
`W = R_{E/K} U_{L/E}` is the published affine Weil restriction
`AffineWeil.groupScheme K E (unitaryParameterGroup E L)` (abbreviation `weilGroup K E L`).

## Definitions

These are internal (derived) definitions. They write the published Weil-restriction
point identification in coordinates, for the proof of `UnitaryChartUpgradeStatement` in
`Langlands.GroupScheme.Examples.SU3RootUnitaryChartUpgrade`.

- `basisVec`, `vecComponents`: expansion of a vector in `(E ⊗[K] A)^I` in the basis `b`,
  `v_i = ∑ⱼ bⱼ ⊗ a(i, j)`, using `AffineWeil.tensorCoordinateEquiv`.
- `weilForm b c A a a'`: the chart cocycle `form c` over `E ⊗[K] A`, read in basis
  components.
- `components b c A`: the bijection from bilinear coordinates over `E ⊗[K] A` to basis
  components `(a, z) ∈ A^{I × Fin n} × A^n`.
- `sections K T`: the relative global sections of a test scheme `T` over `Spec K`, as a
  `K`-algebra.
- `weilPointsEquiv`, `unitaryAffinePointsEquiv`, `parametersEquiv`, `coordinates`: the
  multiplicative identifications of `T`-points of `W` with points of `U_{L/E}` over
  `E ⊗[K] Γ(T)`, with the parameters `tensorParameters E L (E ⊗[K] Γ(T))`, and with the
  bilinear chart coordinates. They compose `Corepresented.pointsEquiv` of the published
  corepresentation of `W`, `unitaryPointsEquiv` and `Corepresented.affineSectionsAlgEquiv`.
- `pointComponents L b T x`, `componentPoint L b T (a, z)`: the basis components of a
  `T`-point of `W`, and the point with given components (mutually inverse).
- `baseTest K`: the identity test scheme `Over.mk (𝟙 (Spec K))`.
- `rationalPoint L p`: the rational point of `W` attached to a field parameter
  `p ∈ rationalParameters E L`, through `AffineWeil.sectionsEquiv` and
  `unitaryRationalPointsEquiv`.
- `rationalCoordinates L p`, `rationalComponents L b p`: the chart coordinates of `p` over
  `E`, and their basis components in `K`.

## Results

- `components_mul_fst`, `components_mul_snd`, `components_one`: in basis components the group
  law is `(a, z)(a', z') = (a + a', z + z' + weilForm a a')`.
- `weilForm_map`, `components_map`: naturality along `K`-algebra maps `A → A'`
  (via `AffineWeil.lTensor_tensorCoordinateEquiv` and
  `AffineWeil.tensorCoordinateEquiv_symm_lTensor`).
- `weilForm_add_left/right`, `weilForm_smul_left/right`: `weilForm` is `A`-bilinear.
- `tensorCoordinateEquiv_symm_algebraMap`: the basis components of `e ⊗ 1` are the
  coordinates `b.repr e` mapped into `A`.
- `unitaryAffinePointsEquiv_naturality`, `parametersEquiv_naturality`,
  `coordinates_naturality`: naturality in the test scheme; pulling back along `f : T' ⟶ T`
  applies `E ⊗ f.left.appTop` to parameters and coordinates. The proofs combine
  `Corepresented.pointsEquiv_naturality`, `unitaryPointsEquiv_naturality` and
  `Corepresented.affineSectionsIso_inv_naturality`.
- `pointComponents_componentPoint`, `componentPoint_pointComponents`,
  `pointComponents_mul_fst`, `pointComponents_mul_snd`, `pointComponents_one`,
  `pointComponents_naturality`: the same facts for basis components of `T`-points of `W`.
- `weilPointsEquiv_rational`: over the identity test scheme, the Weil point of a rational
  point `x` of `W` factors through the rational point `AffineWeil.sectionsEquiv x` of
  `U_{L/E}`. The proof unfolds `AffineWeil.sectionsEquiv` and uses naturality of
  `Corepresented.pointsEquiv` and `pointsEquiv_eq_affinePointsEquiv`. The auxiliary category
  lemma `comp_eq_comp_iso` inserts an isomorphism and its inverse.
- `parametersEquiv_rational`, `coordinates_rational`: the parameters and chart coordinates of
  a rational point of `W` are those of the corresponding field parameter, extended along
  `E → E ⊗[K] Γ(Spec K)`.
- `pointComponents_rationalPoint`: the basis components of `rationalPoint L p` are the images
  in `Γ(Spec K)` of `rationalComponents L b p`.
- `lid_tensorVec_rationalCoordinates`, `first_eq_rationalCoordinates`,
  `second_eq_rationalCoordinates`: a field parameter `(u, v)` has
  `u = ∑ᵢ xᵢ eᵢ` and `v = z f + t u σ(u)` in its chart coordinates `(x, z)`, for the chart
  basis `e`, center `f` and trace-one element `t` of `chartData E L`
  (`second_toParameters`, `rationalTensor_bar`, `fieldInvolution_bar`).
