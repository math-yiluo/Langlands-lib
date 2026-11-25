import Langlands.Theta.DualPair.Unitary.LerayScalar
import Langlands.Theta.Metaplectic.WeylElement

/-!
# The Leray splitting of `U(ν, ν)` through the standard Weil operator

GKT Proposition 12.27 (1) (p. 372) with Proposition 12.29 (p. 375) in Case `3₊`, `W` split,
expressed through the standard Weil operator `r` of GKT §2.3 (Definition 2.9, Lemma 2.16, (2.24)):
the Library's Weil representation `lerayWeil c ν ψ χ Q` of `U(ν, ν)` is
`g ↦ β(g) · r(g ⊗ 1)` on the Siegel parabolic and at the Weyl element. This decides two points of
the comparison with the book:

* **`χ` against `χ⁻¹`.** `lerayWeil_eq_inv_smul_standardOperator_of_mem_siegelParabolic`: for `p`
  in the Siegel parabolic, `lerayWeil p = χ(x(p))⁻¹ · r(p)`, where `x(p) = det_E(p|_X)` is the
  determinant of the action of `p` on the Lagrangian `X = {(0, v)}` of `W = E^{2ν}`
  (`siegelParabolicRaoValue`, the book's Rao function on `P(X)`, Corollary 4.36). So the book's
  character in `β(m(a)) = χ^{book}(det a)` is `χ^{book} = χ⁻¹`: the Library's `χ(det A)` is
  `χ^{book}(c(det A))` (`siegelParabolicRaoValue_eq`: `x(p) = c(det A)`).
* **The Weyl element and the kernel.** `toTraceIsometry_weylElement`: the Library's
  `weylElement c ν = [[0, 1], [-1, 0]]` acts on `𝕎 = 𝕏^* × 𝕏` as the Weyl element `w_J` of the
  general theory with `J = -1` (the book's `w_{n/2}` in the standard basis `e_i = (0, ε_i)`,
  `e^*_i = -(ε_i, 0)`); `standardOperator_weylElement`: from the general definition,
  `r(w)` is `φ ↦ ∫ ψ(⟪x, y⟫) φ(y) dy` for the self-dual measure — the kernel is `ψ(+⟪x, y⟫)`;
  `lerayWeil_weylElement_eq_smul_standardOperator`: `lerayWeil w = β(w) · r(w)` with
  `β(w) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}`.
-/

noncomputable section

open MeasureTheory Matrix
open scoped NNReal

namespace Langlands.Theta

open Langlands.UnitaryGroup Langlands.HarmonicAnalysis Langlands.HeisenbergGroup
open Langlands.LinearMap.BilinForm (isometryGroup)
open Unitary.Internal (mat mat_inv)

section Matrices

variable {E : Type*} [CommRing E] {α ν : Type*} [Fintype ν]

/-- The first column block of `fromCols x y * M`. -/
theorem toCols₁_fromCols_mul (x y : Matrix α ν E) (M : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :
    (fromCols x y * M).toCols₁ = x * M.toBlocks₁₁ + y * M.toBlocks₂₁ := by
  ext i j
  simp [Matrix.mul_apply, toCols₁, toBlocks₁₁, toBlocks₂₁, Fintype.sum_sum_type]

/-- The second column block of `fromCols x y * M`. -/
theorem toCols₂_fromCols_mul (x y : Matrix α ν E) (M : Matrix (ν ⊕ ν) (ν ⊕ ν) E) :
    (fromCols x y * M).toCols₂ = x * M.toBlocks₁₂ + y * M.toBlocks₂₂ := by
  ext i j
  simp [Matrix.mul_apply, toCols₂, toBlocks₁₂, toBlocks₂₂, Fintype.sum_sum_type]

end Matrices

section Algebra

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E] {c : E →ₐ[F] E}
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν] {Q : Matrix α α E}

theorem toTraceIsometry_apply_eq (hc : Function.Involutive c) (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν E)) (x y : Matrix α ν E) :
    (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g :
        (Matrix α ν E × Matrix α ν E) ≃ₗ[F] (Matrix α ν E × Matrix α ν E)) (x, y) =
      (x * (mat c g⁻¹).toBlocks₁₁ + y * (mat c g⁻¹).toBlocks₂₁,
        x * (mat c g⁻¹).toBlocks₁₂ + y * (mat c g⁻¹).toBlocks₂₂) := by
  rw [UnitaryGroup.toTraceIsometry_apply, UnitaryGroup.rightMulInvEquiv_apply,
    toCols₁_fromCols_mul, toCols₂_fromCols_mul]

theorem isometryInv_toTraceIsometry (hc : Function.Involutive c) (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν E)) (x y : Matrix α ν E) :
    isometryInv (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g) (x, y) =
      (x * (mat c g).toBlocks₁₁ + y * (mat c g).toBlocks₂₁,
        x * (mat c g).toBlocks₁₂ + y * (mat c g).toBlocks₂₂) := by
  rw [isometryInv, ← map_inv, toTraceIsometry_apply_eq, inv_inv]

/-- **The Siegel parabolic of `U(ν, ν)` goes into the Siegel parabolic of `𝕏 = 0 × M_{α×ν}(E)`**
(the book's `P(X) ⊗ 1 ⊆ P(𝕏)`). -/
theorem toTraceIsometry_mem_siegelParabolicGroup (hc : Function.Involutive c)
    (hQ : Matrix.IsHermitianFor c Q) {p : ofForm c (hyperbolicForm ν E)}
    (hp : p ∈ siegelParabolic c ν) :
    UnitaryGroup.toTraceIsometry (ν := ν) hc hQ p ∈
      siegelParabolicGroup (hermitianTracePairing (ν := ν) c Q) := by
  have hp' : (mat c p⁻¹).toBlocks₂₁ = 0 := (siegelParabolic c ν).inv_mem hp
  have hp1 : (mat c p).toBlocks₂₁ = 0 := hp
  intro y
  refine ⟨?_, ?_⟩
  · rw [toTraceIsometry_apply_eq, hp']; simp
  · rw [isometryInv_toTraceIsometry, hp1]; simp

/-- The blocks of `ι(p)⁻¹` on `𝕏^* = M_{α×ν}(E)`: `d x = x A`, `b x = x B` for
`mat p = [[A, B], [0, D]]`. -/
theorem standardD_toTraceIsometry (hc : Function.Involutive c) (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν E)) (x : Matrix α ν E) :
    standardD (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g) x = x * (mat c g).toBlocks₁₁ := by
  change (isometryInv (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g)
    (x, (0 : Matrix α ν E))).1 = _
  rw [isometryInv_toTraceIsometry]; simp

theorem standardB_toTraceIsometry (hc : Function.Involutive c) (hQ : Matrix.IsHermitianFor c Q)
    (g : ofForm c (hyperbolicForm ν E)) (x : Matrix α ν E) :
    standardB (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g) x = x * (mat c g).toBlocks₁₂ := by
  change (isometryInv (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ g)
    (x, (0 : Matrix α ν E))).2 = _
  rw [isometryInv_toTraceIsometry]; simp

/-- For `p` in the Siegel parabolic of `U(ν, ν)`, the lower right block of `p⁻¹` is `c(A)ᵀ`, where
`A` is the upper left block of `p` (from `p⁻¹ = -H c(p)ᵀ H`, `H = hyperbolicForm`). -/
theorem toBlocks₂₂_mat_inv_of_mem {p : ofForm c (hyperbolicForm ν E)}
    (hp : p ∈ siegelParabolic c ν) :
    (mat c p⁻¹).toBlocks₂₂ = ((mat c p).toBlocks₁₁.map c)ᵀ := by
  have hp1 : (mat c p).toBlocks₂₁ = 0 := hp
  have hM : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0
      (mat c p).toBlocks₂₂ := by
    rw [← hp1, fromBlocks_toBlocks]
  rw [mat_inv, hM, hyperbolicForm_eq_fromBlocks, fromBlocks_map, fromBlocks_transpose,
    fromBlocks_multiply, fromBlocks_multiply, fromBlocks_neg, toBlocks_fromBlocks₂₂]
  simp

theorem det_toBlocks₁₁_ne_zero {p : ofForm c (hyperbolicForm ν E)}
    (hp : p ∈ siegelParabolic c ν) : (mat c p).toBlocks₁₁.det ≠ 0 := by
  have hp1 : (mat c p).toBlocks₂₁ = 0 := hp
  have hM : mat c p = fromBlocks (mat c p).toBlocks₁₁ (mat c p).toBlocks₁₂ 0
      (mat c p).toBlocks₂₂ := by
    rw [← hp1, fromBlocks_toBlocks]
  have hu : (mat c p).det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _) |>.ne_zero
  rw [hM, det_fromBlocks_zero₂₁] at hu
  exact left_ne_zero_of_mul hu

/-- **The Rao value on the Siegel parabolic** (GKT Corollary 4.36, Definition 4.37 on `P(X)`):
`x(p) = det_E(p|_X)`, the determinant of the action `v ↦ v · (p⁻¹)₂₂` of `p` on the Lagrangian
`X = {(0, v)}` of `W = E^{2ν}` (row vectors, `g` acting by `w ↦ w g⁻¹`). -/
def siegelParabolicRaoValue {p : ofForm c (hyperbolicForm ν E)} (hp : p ∈ siegelParabolic c ν) :
    Eˣ :=
  Units.mk0 (mat c p⁻¹).toBlocks₂₂.det (by
    rw [toBlocks₂₂_mat_inv_of_mem hp, det_transpose, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
    exact fun h => det_toBlocks₁₁_ne_zero hp ((map_eq_zero_iff c c.injective).1 h))

/-- `x(p) = c(det A)` for `mat p = [[A, B], [0, D]]`. -/
theorem siegelParabolicRaoValue_eq {p : ofForm c (hyperbolicForm ν E)}
    (hp : p ∈ siegelParabolic c ν) :
    (siegelParabolicRaoValue hp : E) = c (mat c p).toBlocks₁₁.det := by
  rw [siegelParabolicRaoValue, Units.val_mk0, toBlocks₂₂_mat_inv_of_mem hp, det_transpose,
    ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]

/-- **The Library's Weyl element is the Weyl element `w_J` of the general theory with `J = -1`**:
`weylElement c ν = [[0, 1], [-1, 0]]` acts on `𝕏^* × 𝕏` by `(x, y) ↦ (y, -x)`. -/
theorem toTraceIsometry_weylElement (hc : Function.Involutive c) (hQ : Matrix.IsHermitianFor c Q)
    (hJ : ∀ y y' : Matrix α ν E, hermitianTracePairing c Q ((LinearEquiv.neg F) y) y' =
      hermitianTracePairing c Q ((LinearEquiv.neg F) y') y) :
    UnitaryGroup.toTraceIsometry (ν := ν) hc hQ (weylElement c ν) =
      weylIsometry (hermitianTracePairing (ν := ν) c Q) (LinearEquiv.neg F) hJ := by
  refine Subtype.ext (LinearEquiv.ext fun w => ?_)
  obtain ⟨x, y⟩ := w
  change (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ (weylElement c ν) :
    (Matrix α ν E × Matrix α ν E) ≃ₗ[F] (Matrix α ν E × Matrix α ν E)) (x, y) = (-(-y), -x)
  have h : mat c (weylElement c ν)⁻¹ = -hyperbolicForm ν E := rfl
  rw [toTraceIsometry_apply_eq, h, hyperbolicForm_eq_fromBlocks, fromBlocks_neg]
  simp

end Algebra

section Leray

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Invertible (2 : F)] {E : Type} [Field E] [Algebra F E]
  [TopologicalSpace E] [IsModuleTopology F E] [Algebra.IsQuadraticExtension F E]
  {c : E →ₐ[F] E} {δ : E} {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]
  {Q : Matrix α α E} {χ : Eˣ →* Circle} {ψ : UnitaryAdditiveCharacter F}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Invertible (2 : F)]
  [TopologicalSpace E] [IsModuleTopology F E] in
/-- The book's pairing `⟪,⟫ = hermitianTracePairing c Q` of `𝕏^*` and `𝕏` is perfect. -/
theorem isPerfPair_hermitianTracePairing (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) :
    (hermitianTracePairing (ν := ν) c Q).IsPerfPair := by
  have hnd : ∀ y : Matrix α ν E, (∀ x, hermitianTracePairing c Q x y = 0) → y = 0 := by
    intro y hy
    obtain ⟨β, hβ, -, hnd, -, -⟩ := Unitary.Internal.pr_alg F E c δ hE α ν Q ⟨hQ, hQu⟩
    refine hnd y fun x => ?_
    have := hy x
    rw [hermitianTracePairing_eq_mul, hermitianPairing_eq_hermitianSymplecticForm,
      mul_eq_zero] at this
    rw [hβ]
    exact this.resolve_left two_ne_zero
  refine LinearMap.IsPerfPair.of_injective (fun x x' hxx => ?_) (fun y y' hyy => ?_)
  · have h0 : ∀ y, hermitianTracePairing c Q y (x - x') = 0 := fun y => by
      rw [hermitianTracePairing_symm hE hQ hQu, map_sub, LinearMap.sub_apply, hxx, sub_self]
    exact sub_eq_zero.1 (hnd _ h0)
  · have h0 : ∀ x, hermitianTracePairing c Q x (y - y') = 0 := fun x => by
      have := LinearMap.congr_fun hyy x
      simp only [LinearMap.flip_apply] at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.1 (hnd _ h0)

variable [IsModuleTopology F (Matrix α ν E)] [IsTopologicalAddGroup (Matrix α ν E)]
  [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)]
  [(hermitianTracePairing (ν := ν) c Q).IsPerfPair]

omit [IsModuleTopology F E] in
/-- **Lemma 2.16 for the unitary pair**: for `p` in the Siegel parabolic of `U(ν, ν)` with
`mat p = [[A, B], [0, D]]`, `r(p ⊗ 1) φ(x) = |N det A|^{|α|/2} ψ(½ ⟪x A, x B⟫) φ(x A)` (GKT
Proposition 12.27 (1), first two formulas, without the factor `β(p)`). -/
theorem standardOperator_toTraceIsometry_of_mem_siegelParabolic (hc : Function.Involutive c)
    (hQ : Matrix.IsHermitianFor c Q) {p : ofForm c (hyperbolicForm ν E)}
    (hp : p ∈ siegelParabolic c ν) (φ : SchwartzBruhat (Matrix α ν E)) (x : Matrix α ν E) :
    (standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hc hQ p) φ : Matrix α ν E → ℂ) x =
      (((distribHaarChar F (Units.map (Algebra.norm F : E →* F)
          (Units.mk0 _ (det_toBlocks₁₁_ne_zero hp))) : ℝ) ^ ((Fintype.card α : ℝ) / 2) : ℝ) : ℂ) *
        ((ψ (⅟2 * hermitianTracePairing c Q (x * (mat c p).toBlocks₁₁)
          (x * (mat c p).toBlocks₁₂)) : ℂ) *
          (φ : Matrix α ν E → ℂ) (x * (mat c p).toBlocks₁₁)) := by
  have hι := toTraceIsometry_mem_siegelParabolicGroup (F := F) hc hQ hp
  set u := Units.mk0 _ (det_toBlocks₁₁_ne_zero hp)
  have hdet : LinearEquiv.det (siegelD hι) = (Units.map (Algebra.norm F : E →* F) u) ^
      Fintype.card α := by
    refine Units.ext ?_
    rw [LinearEquiv.coe_det, Units.val_pow_eq_pow_val, Units.coe_map,
      det_restrictScalars_mul_mul 1 (mat c p).toBlocks₁₁ _ fun y => ?_]
    · simp [u]
    · change standardD _ y = 1 * y * _
      rw [standardD_toTraceIsometry, Matrix.one_mul]
  rw [standardOperator_of_mem_siegelParabolicGroup _ _ hι, standardD_toTraceIsometry,
    standardB_toTraceIsometry, hdet, map_pow, NNReal.coe_pow, ← Real.rpow_natCast,
    ← Real.rpow_mul (NNReal.coe_nonneg _), UnitaryAdditiveCharacter.complex_apply]
  congr 4
  ring

/-- **The Leray splitting on the Siegel parabolic through `r`** (GKT Proposition 12.27 (1) with
Proposition 12.29): `lerayWeil p = χ(det A) · r(p ⊗ 1)` for `mat p = [[A, B], [0, D]]`. -/
theorem lerayWeil_eq_smul_standardOperator_of_mem_siegelParabolic (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {p : ofForm c (hyperbolicForm ν E)} (hp : p ∈ siegelParabolic c ν) :
    lerayWeil c ν ψ χ Q p = (χ (Units.mk0 _ (det_toBlocks₁₁_ne_zero hp)) : ℂ) •
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ p) := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
  rw [lerayWeil_apply_of_mem_siegelParabolic hE hQ hQu hχ hres hp, LinearMap.smul_apply,
    SetLike.val_smul, Pi.smul_apply,
    standardOperator_toTraceIsometry_of_mem_siegelParabolic _ _ hp, splittingScalar,
    dite_eq_right (det_toBlocks₁₁_ne_zero hp), smul_eq_mul]
  ring

/-- **`χ` against `χ⁻¹`**: on the Siegel parabolic,
`lerayWeil p = χ(x(p))⁻¹ · r(p ⊗ 1)` where `x(p) = det_E(p|_X)` is the book's Rao value
(`siegelParabolicRaoValue`). So the Leray splitting `lerayWeil c ν ψ χ Q` is the book's splitting
with the character `χ^{book} = χ⁻¹` in `β(m(a)) = χ^{book}(det a)` (Proposition 12.29); the
Library's `χ(det A)` is `χ^{book}(c(det A))`, `c(det A) = x(p)`. -/
theorem lerayWeil_eq_inv_smul_standardOperator_of_mem_siegelParabolic
    (hE : IsQuadraticInvolution c δ) (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det)
    (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α)
    {p : ofForm c (hyperbolicForm ν E)} (hp : p ∈ siegelParabolic c ν) :
    lerayWeil c ν ψ χ Q p = (((χ (siegelParabolicRaoValue hp))⁻¹ : Circle) : ℂ) •
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ p) := by
  have hnorm : ∀ z : Eˣ, χ (Units.map (algebraMap F E : F →* E)
      (Units.map (Algebra.norm F : E →* F) z)) = 1 := fun z => by
    have h := hres (Units.map (Algebra.norm F : E →* F) z)
    rw [LocalClassField.normResidueSign_norm, Units.val_one, Int.cast_one, one_pow] at h
    exact Circle.coe_eq_one.1 h
  have hx : siegelParabolicRaoValue hp =
      Units.map (c : E →* E) (Units.mk0 _ (det_toBlocks₁₁_ne_zero hp)) :=
    Units.ext (by rw [siegelParabolicRaoValue_eq]; rfl)
  rw [lerayWeil_eq_smul_standardOperator_of_mem_siegelParabolic hE hQ hQu hχ hres hp, hx,
    hE.map_map_eq_inv hnorm, inv_inv]

omit [Invertible (2 : F)] [TopologicalSpace E] [IsModuleTopology F E]
  [Algebra.IsQuadraticExtension F E] [IsModuleTopology F (Matrix α ν E)]
  [IsTopologicalAddGroup (Matrix α ν E)] [MeasurableSpace (Matrix α ν E)]
  [BorelSpace (Matrix α ν E)] [(hermitianTracePairing (ν := ν) c Q).IsPerfPair]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [DecidableEq ν] in
/-- `β(J y, y') = β(J y', y)` for `J = -1` (the symmetry of `⟪,⟫`). -/
theorem hermitianTracePairing_neg_symm (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (y y' : Matrix α ν E) :
    hermitianTracePairing c Q ((LinearEquiv.neg F) y) y' =
      hermitianTracePairing c Q ((LinearEquiv.neg F) y') y := by
  simp only [LinearEquiv.coe_neg, Pi.neg_apply, id_eq, map_neg, LinearMap.neg_apply]
  rw [hermitianTracePairing_symm hE hQ hQu]

omit [IsModuleTopology F E] in
/-- **The Weyl element and its kernel**: from the general
definition, `r(w ⊗ 1)` for the Library's `weylElement` is `φ ↦ ∫ ψ(⟪x, y⟫) φ(y) dy` for the
self-dual measure of `ψ ∘ ⟪,⟫` — the kernel `ψ(+⟪x, y⟫)`, because `weylElement` is the Weyl element
`w_J` with `J = -1` (`toTraceIsometry_weylElement`, GKT (2.24) with `I = J⁻¹ = -1`). -/
theorem standardOperator_weylElement (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (φ : SchwartzBruhat (Matrix α ν E))
    (x : Matrix α ν E) :
    (standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ (weylElement c ν)) φ :
        Matrix α ν E → ℂ) x =
      ∫ y, (ψ (hermitianTracePairing c Q x y) : ℂ) * (φ : Matrix α ν E → ℂ) y
        ∂(selfDualMeasure fun x y : Matrix α ν E => ψ.complex (hermitianTracePairing c Q x y)) := by
  have hJ := hermitianTracePairing_neg_symm (F := F) (ν := ν) hE hQ hQu
  have hw : weylBicharacter ψ.complex (hermitianTracePairing (ν := ν) c Q) (LinearEquiv.neg F) =
      fun x y : Matrix α ν E => ψ.complex (hermitianTracePairing c Q x y) := by
    funext x y
    simp [weylBicharacter, weylForm_apply]
  rw [toTraceIsometry_weylElement hE.involutive hQ hJ, standardOperator_weylIsometry, hw]
  simp only [UnitaryAdditiveCharacter.complex_apply]

/-- **The Leray splitting at the Weyl element through `r`** (GKT Proposition 12.27 (1), third
formula, with Proposition 12.29 in Case `3₊`): `lerayWeil w = β(w) · r(w ⊗ 1)` with
`β(w) = γ(ψ_{1/2} ∘ Res_{E/F} V)^{|ν|}` (`lerayScalar_selfDualMeasure`). -/
theorem lerayWeil_weylElement_eq_smul_standardOperator (hE : IsQuadraticInvolution c δ)
    (hQ : Matrix.IsHermitianFor c Q) (hQu : IsUnit Q.det) (hχ : Continuous χ)
    (hres : ∀ a : Fˣ, (χ (Units.map (algebraMap F E : F →* E) a) : ℂ) =
      ((LocalClassField.normResidueSign F E a : ℤ) : ℂ) ^ Fintype.card α) :
    lerayWeil c ν ψ χ Q (weylElement c ν) =
      (weilIndex (fun v : α → E => (ψ.scale (twoUnit F)⁻¹).complex (hermitianTraceForm c Q v v)) ^
        Fintype.card ν) •
      standardOperator ψ.continuous_complex ψ.complex_ne_one
        (UnitaryGroup.toTraceIsometry (ν := ν) hE.involutive hQ (weylElement c ν)) := by
  refine LinearMap.ext fun φ => Subtype.ext (funext fun x => ?_)
  rw [lerayWeil_weylElement_apply_selfDualMeasure hE hQ hQu hχ hres, LinearMap.smul_apply,
    SetLike.val_smul, Pi.smul_apply, standardOperator_weylElement hE hQ hQu, smul_eq_mul]

end Leray

end Langlands.Theta
