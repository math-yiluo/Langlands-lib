# The exterior-square morphism from the Hermitian model group to a quaternionic isometry group

Module `Langlands.GroupScheme.Quaternionic.KneserThreeModelHom`, namespace
`Langlands.GroupScheme.KneserThree`. This is internal support for the explicit A₃ = D₃
comparison used to prove `KneserThreeSpinSubgroupStatement` (Kneser's argument as summarized in
Tits, Bourbaki 505, 1977, no. 1.1.6). It makes no literature claim beyond what is proved here.
It turns the exterior-square map of `KneserThreeCore` and `KneserThreeUnits` into a morphism of
group schemes over `Spec K`:

`QuatData.modelHom : HermitianRoot.SchemeModel.groupScheme K L H w' hw' ⟶ σ.isometryGroup q₃`.

The source is the Library's special unitary group scheme of the Hermitian form
"hyperbolic plane ⊕ diag(1, -δ)" over the quadratic extension `L = field Q.c` of `K`. The target
is the isometry group of a `σ`-quadratic form `q₃` on `D³` in Tits's sense.

## Setting

* `Q : QuatData K D` (module `KneserThreeSplitting`), `L = field Q.c`.
* `H : DiagonalForm (SU3Root.fieldInvolution K L) (Fin 2)` with unit witnesses `w'`, `hw'`, and
  `hH : H.weight = ![-1, algebraMap K L Q.δ]`. The Library's `HermitianRoot.gram H` has
  `1` at the (top, bottom) and (bottom, top) entries and `-diag(H.weight)` on the middle block,
  which by `hH` is `diag(1, -δ)`. In the order `(top, m₀, m₁, bot)` this is the matrix
  `Presentation.gram` of `KneserThreeCore` for `Q.presentation R`. In the Lean source the model
  group is written `𝕄` (a local notation).
* For a test scheme `T` over `Spec K`, `R = BinaryScheme.coefficients T` is its ring of global
  sections. The Library's tensor coefficient ring `SpecialLinear.WeilRoot.tensorAlgebra K L T`
  is definitionally `L ⊗[K] R`.

## Model points as `4 × 4` matrices (section `Model`; `D` only needs to be a ring here)

* `indexEquiv : Fin 4 ≃ Index (Fin 2)` sends `0, 1, 2, 3` to top, `m₀`, `m₁`, bottom.
* `coeffEquiv Q T : tensorAlgebra K L T ≃+* L ⊗[K] R` is the identity (`RingEquiv.refl`). It
  only changes the displayed type.
* `pointsMatrix H w' hw' T` composes the Library's `HermitianRoot.SchemeModel.pointsEquiv` with
  the inclusion of `specialUnitarySubgroup`. `pointsMatrix_val` records its value.
* `reindexHom Q T` maps a matrix `M` indexed by `Index (Fin 2)` to
  `(M.map coeffEquiv).submatrix indexEquiv indexEquiv` (`reindexHom_apply`).
* `modelMatrix H w' hw' T : (T ⟶ 𝕄.X) →* (Matrix (Fin 4) (Fin 4) (L ⊗[K] R))ˣ` is
  `Units.map (reindexHom Q T)` after `pointsMatrix`. `modelMatrix_val` gives its matrix.
* `tensorForm_weight`: the weights of the Library's `tensorForm` are `const (H.weight i)`.
* `isSpecialUnitary_modelMatrix hH T x`: `modelMatrix x` is special unitary for
  `Q.presentation R`. The proof reindexes the Library's `PreservesForm` equation with
  `Matrix.submatrix_mul_equiv`, compares the Gram matrices entrywise using `hH`, and reindexes
  the determinant with `Matrix.det_submatrix_equiv_self`.
* `tensorMap_eq`: the Library's coefficient map `SpecialLinear.WeilRoot.tensorMap K L a` for
  `a : T' ⟶ T` agrees with `Q.mapA φ = id ⊗ φ`, where `φ` is the induced map on global sections.
  `modelMatrix_naturality` says `modelMatrix T' (a ≫ x) = (modelMatrix T x).map (mapA φ)`. It
  follows from the Library's `pointsEquiv_naturality`.

## The morphism (section `Hom`; `D` a finite-dimensional division algebra)

Fix `θ l₁ l₂ w : L` with `hθ : θ̄ = -θ` and
`hw : w · (θ · (l₁ l̄₁ - δ l₂ l̄₂)) = 1`, where `ā = SU3Root.conjugation K L a` and `δ` stands for
`algebraMap K L Q.δ`.

* `cmapPoints w' hw' hθ hw hH T : (T ⟶ 𝕄.X) →* (Matrix (Fin 3) (Fin 3) (R ⊗[K] D))ˣ` is
  `Presentation.cmapUnits` of `KneserThreeUnits` for `Q.presentation R` at the constant
  parameters `const θ, const l₁, const l₂, const w`, applied to `modelMatrix`. By
  `cmapPoints_val` its matrix is `(Q.presentation R).cmap … (modelMatrix T x)`.
* `cmapPoints_naturality`: `cmapPoints T' (a ≫ x)` is `cmapPoints T x` mapped by `φ ⊗ id`. It
  follows from `Presentation.cmap_map` with `φA = mapA φ`, `φB = mapB φ` and the naturality lemmas
  of `KneserThreeSplitting`, together with `mapA_const` and `modelMatrix_naturality`.
* `unitPoints` composes `cmapPoints` with the inverse of the Library's
  `HyperbolicScheme.matrixPointsEquiv (Fin 3) T`. That map identifies the points of the unit
  group scheme `FiniteAlgebraUnits.groupScheme` of `M₃(D)` with `(M₃(R ⊗[K] D))ˣ`.
  `unitPoints_naturality` is natural in `T`.
* `unitHom w' hw' hθ hw hH : 𝕄 ⟶ FiniteAlgebraUnits.groupScheme (Module.finBasis K M₃(D))` is
  `homOfPoints unitPoints`. `unitHom_points` says that on every test point its matrix is
  `cmapPoints`.

## Landing in the isometry group

Let `σ` be an involution of the first kind of `D` and `q₃ : σ.QuadraticForms (Fin 3)`. Assume:

* `h2 : (2 : K) ≠ 0`;
* `hl : l̄₁ = -l₁`;
* `hℓ : Q.elem l₁ l₂ · ℓinv = 1`;
* `hσ : ∀ d, σ d = Q.elem l₁ l₂ · Q.bar d · ℓinv`, so `σ` is `ℓ`-conjugate to the conjugation
  `Q.bar` of `KneserThreeUnits`;
* `hq : σ.polar q₃ = polarMatrix (-(ι θ · Q.elem l₁ l₂))`, that is,
  `[[0, 1, 0], [1, 0, 0], [0, 0, μ]]` with `μ = -(ι θ · ℓ)`.

Then:

* `unitHom_range_le`: `SubgroupFunctor.range (unitHom …) ≤ SubgroupFunctor.range
  (σ.isometryGroupι q₃)`. The proof follows the Library's
  `HyperbolicScheme.isometryUnitHom_range_le`. It applies `mem_range_isometryGroupι_iff` with the
  representative `Quotient.out q₃` and reduces to the condition that the defect
  `X Q τ X - Q` is alternating, where `X = cmapPoints x`, `Q = 1 ⊗ Quotient.out q₃` and
  `τ = (σ.baseChange R).matrix (Fin 3)`. Then it applies `defect_mem_of_polar` with
  `h = algebraMap K R 2⁻¹`. The polar matrix `Q + τ Q` is `polarMatrix (1 ⊗ μ)` by `hq`, and
  `QuatData.cmap_mul_polarMatrix_mul_matrix` gives `X · polarMatrix (1 ⊗ μ) · τ X =
  polarMatrix (1 ⊗ μ)`.
* `isometryGroupι_represents σ q₃`: the inclusion `σ.isometryGroupι q₃` represents its range
  (it is a closed immersion, hence a monomorphism).
* `modelHom w' hw' hθ hw hH h2 hl hℓ hσ hq : 𝕄 ⟶ σ.isometryGroup q₃` is the factorization
  `IsRepresentedBy.factorHom` of `unitHom` through the isometry group.
  `modelHom_comp`: `modelHom ≫ σ.isometryGroupι q₃ = unitHom`.
* `modelHom_points`: on a test point `x`, the matrix (via `HyperbolicScheme.matrixPointsEquiv`)
  of `x ≫ modelHom ≫ isometryGroupι` is `cmapPoints x`.

`set_option maxRecDepth 8192` is used because unfolding the model's point equivalence exceeds
the default recursion depth.
