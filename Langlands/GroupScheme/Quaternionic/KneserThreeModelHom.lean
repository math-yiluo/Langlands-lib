import Langlands.GroupScheme.Quaternionic.KneserThreeUnits
import Langlands.GroupScheme.Quaternionic.HyperbolicGroupSchemeExtension
import Langlands.GroupScheme.Examples.HermitianRootGroupScheme
import Langlands.GroupScheme.Rational.LeviFactorization

/-!
# The exterior-square morphism from a Hermitian model group to a quaternionic isometry group

Let `Q : QuatData K D` and `L = K(√c)`. Let `H` be the diagonal Hermitian form with weights
`(-1, δ)`, so the Library's model group `HermitianRoot.SchemeModel.groupScheme K L H w' hw'` is the
special unitary group of "hyperbolic plane ⊕ diag(1, -δ)". On test points, `modelMatrix` writes
its points as `4 × 4` special unitary matrices over `L ⊗[K] R` for `Q.presentation R`. The
exterior-square map then gives a morphism `unitHom` to the units of `M₃(D)`. When `σ` is
`ℓ`-conjugate to `Q.bar`, the polar matrix of `q₃` is `[[0, 1, 0], [1, 0, 0], [0, 0, -(ι θ ℓ)]]`
and `2 ≠ 0`, this morphism factors through the isometry group of `q₃` (`modelHom`).
-/

noncomputable section

set_option maxRecDepth 8192

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.KneserThree

open Quaternionic HermitianRoot QuadField

/-- The coordinate order `(top, m₀, m₁, bot)` of `Index (Fin 2)`. -/
def indexEquiv : Fin 4 ≃ Index (Fin 2) where
  toFun := ![Sum.inl (), Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 1), Sum.inr (Sum.inr ())]
  invFun
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl i) => i.succ.castSucc
    | Sum.inr (Sum.inr _) => 3
  left_inv i := by fin_cases i <;> rfl
  right_inv
    | Sum.inl () => rfl
    | Sum.inr (Sum.inl i) => by fin_cases i <;> rfl
    | Sum.inr (Sum.inr ()) => rfl

namespace QuatData

section Model

variable {K D : Type u} [Field K] [Ring D] [Algebra K D] {Q : QuatData K D}
  {H : DiagonalForm (SU3Root.fieldInvolution K (field Q.c)) (Fin 2)}
  {w' : Fin 2 → (field Q.c)ˣ} {hw' : ∀ i, (w' i : field Q.c) = H.weight i}

/-- The Hermitian model group `SU(H)` over `L = K(√c)`. -/
local notation "𝕄" => HermitianRoot.SchemeModel.groupScheme K (field Q.c) H w' hw'

variable (Q) in
/-- The model's coefficient ring `L ⊗[K] R`, identified with itself. -/
def coeffEquiv (T : Over (Spec (CommRingCat.of K))) :
    SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T ≃+*
      field Q.c ⊗[K] BinaryScheme.coefficients T :=
  RingEquiv.refl _

variable (H w' hw') in
/-- Model points as determinant-one unit matrices over the tensor coefficient ring. -/
def pointsMatrix (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (𝕄).X) →*
      Matrix.GeneralLinearGroup (Index (Fin 2)) (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T) :=
  (specialUnitarySubgroup (HermitianRoot.SchemeModel.tensorForm K (field Q.c) H T)).subtype.comp
    (HermitianRoot.SchemeModel.pointsEquiv K (field Q.c) H w' hw' T).toMonoidHom

theorem pointsMatrix_val (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕄).X) :
    pointsMatrix H w' hw' T x = (HermitianRoot.SchemeModel.pointsEquiv K (field Q.c) H w' hw' T x).1 := by
  simp only [pointsMatrix, MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    MulEquiv.coe_toMonoidHom]

variable (Q) in
/-- Reindexing to `(top, m₀, m₁, bot)` and identifying the coefficients with `L ⊗[K] R`. -/
def reindexHom (T : Over (Spec (CommRingCat.of K))) :
    Matrix (Index (Fin 2)) (Index (Fin 2)) (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T) →*
      Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T) :=
  ((coeffEquiv Q T).mapMatrix.trans (Matrix.reindexRingEquiv _ indexEquiv.symm)).toMonoidHom

theorem reindexHom_apply (T : Over (Spec (CommRingCat.of K)))
    (M : Matrix (Index (Fin 2)) (Index (Fin 2)) (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T)) :
    reindexHom Q T M = (M.map (coeffEquiv Q T)).submatrix indexEquiv indexEquiv :=
  rfl

variable (H w' hw') in
/-- Model points as `4 × 4` unit matrices over `L ⊗[K] R` in the order `(top, m₀, m₁, bot)`. -/
def modelMatrix (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (𝕄).X) →* (Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T))ˣ :=
  (Units.map (reindexHom Q T)).comp (pointsMatrix H w' hw' T)

theorem modelMatrix_val (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕄).X) :
    (modelMatrix H w' hw' T x : Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T)) =
      (((HermitianRoot.SchemeModel.pointsEquiv K (field Q.c) H w' hw' T x).1 :
        Matrix (Index (Fin 2)) (Index (Fin 2))
          (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T)).map
            (coeffEquiv Q T)).submatrix indexEquiv indexEquiv := by
  rw [← pointsMatrix_val, ← reindexHom_apply]
  rfl

theorem tensorForm_weight (T : Over (Spec (CommRingCat.of K))) (i : Fin 2) :
    coeffEquiv Q T ((HermitianRoot.SchemeModel.tensorForm K (field Q.c) H T).weight i) =
      Q.const (BinaryScheme.coefficients T) (H.weight i) :=
  rfl

/-- Model points are special unitary for the presentation's Gram matrix. -/
theorem isSpecialUnitary_modelMatrix (hH : H.weight = ![-1, algebraMap K (field Q.c) Q.δ])
    (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕄).X) :
    (Q.presentation (BinaryScheme.coefficients T)).IsSpecialUnitary
      (modelMatrix H w' hw' T x :
        Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T)) := by
  obtain ⟨hpres, hdet⟩ := (HermitianRoot.SchemeModel.pointsEquiv K (field Q.c) H w' hw' T x).2
  set g : Matrix (Index (Fin 2)) (Index (Fin 2))
      (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T) :=
    (HermitianRoot.SchemeModel.pointsEquiv K (field Q.c) H w' hw' T x).1.1 with hg
  rw [modelMatrix_val]
  refine ⟨?_, ?_⟩
  · have hgram : (Q.presentation (BinaryScheme.coefficients T)).gram =
        ((gram (HermitianRoot.SchemeModel.tensorForm K (field Q.c) H T)).map
          (coeffEquiv Q T)).submatrix indexEquiv indexEquiv := by
      ext i k
      fin_cases i <;> fin_cases k <;>
        simp [Presentation.gram, gram, indexEquiv, Matrix.fromBlocks, tensorForm_weight, hH,
          presentation_δ, TensorProduct.neg_tmul, ← Algebra.TensorProduct.one_def]
    have hconj : (Q.presentation (BinaryScheme.coefficients T)).conjT
        ((g.map (coeffEquiv Q T)).submatrix indexEquiv indexEquiv) =
        ((conjugateTranspose (SU3Root.SchemeModel.coefficientInvolution K (field Q.c) T)
          g).map (coeffEquiv Q T)).submatrix indexEquiv indexEquiv :=
      rfl
    rw [hconj, hgram, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M => Matrix.submatrix (M.map (coeffEquiv Q T)) indexEquiv
      indexEquiv) hpres
  · rw [Matrix.det_submatrix_equiv_self]
    exact congrArg Units.val hdet

/-- The test-scheme coefficient map of the model is `id ⊗ φ`. -/
theorem tensorMap_eq {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (y : SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T) :
    SpecialLinear.WeilRoot.tensorMap K (field Q.c) a y =
      Q.mapA ((algΓ (CommRingCat.of K)).map a).unop.hom y := by
  induction y using TensorProduct.inductionOn with
  | tmul e r => rfl
  | add y z hy hz =>
    exact ((map_add (SpecialLinear.WeilRoot.tensorMap K (field Q.c) a) y z).trans
      (congrArg₂ (· + ·) hy hz)).trans (map_add _ y z).symm

theorem modelMatrix_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (𝕄).X) :
    (modelMatrix H w' hw' T' (a ≫ x) :
        Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T')) =
      (modelMatrix H w' hw' T x :
        Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T)).map
          (Q.mapA ((algΓ (CommRingCat.of K)).map a).unop.hom) := by
  rw [modelMatrix_val, modelMatrix_val, HermitianRoot.SchemeModel.pointsEquiv_naturality]
  ext i k
  exact tensorMap_eq a _

end Model

section Hom

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  {Q : QuatData K D}
  {H : DiagonalForm (SU3Root.fieldInvolution K (field Q.c)) (Fin 2)}
  {w' : Fin 2 → (field Q.c)ˣ} {hw' : ∀ i, (w' i : field Q.c) = H.weight i}
  {θ l₁ l₂ w : field Q.c}
  (hθ : SU3Root.conjugation K (field Q.c) θ = -θ)
  (hw : w * (θ * (l₁ * SU3Root.conjugation K (field Q.c) l₁ -
      algebraMap K (field Q.c) Q.δ * l₂ * SU3Root.conjugation K (field Q.c) l₂)) = 1)
  (hH : H.weight = ![-1, algebraMap K (field Q.c) Q.δ])

local notation "𝕄" => HermitianRoot.SchemeModel.groupScheme K (field Q.c) H w' hw'

variable (w' hw') in
/-- The exterior-square map on model points, as `3 × 3` unit matrices over `R ⊗[K] D`. -/
def cmapPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (𝕄).X) →* (Matrix (Fin 3) (Fin 3) (BinaryScheme.coefficients T ⊗[K] D))ˣ :=
  (Q.presentation (BinaryScheme.coefficients T)).cmapUnits
    (Q.presentation_bar_const_neg _ hθ) (Q.presentation_unit_const _ hw) (modelMatrix H w' hw' T)
    (isSpecialUnitary_modelMatrix (w' := w') (hw' := hw') hH T)

omit [FiniteDimensional K D] in
theorem cmapPoints_val (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕄).X) :
    (cmapPoints w' hw' hθ hw hH T x :
        Matrix (Fin 3) (Fin 3) (BinaryScheme.coefficients T ⊗[K] D)) =
      (Q.presentation (BinaryScheme.coefficients T)).cmap (Q.const _ θ) (Q.const _ l₁)
        (Q.const _ l₂) (Q.const _ w) (modelMatrix H w' hw' T x) :=
  rfl

variable (w' hw') in
/-- Model points mapped to points of the unit group of `M₃(D)`. -/
def unitPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (𝕄).X) →*
      (T ⟶ (FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix (Fin 3) (Fin 3) D))).X) :=
  (HyperbolicScheme.matrixPointsEquiv (D := D) (Fin 3) T).symm.toMonoidHom.comp
    (cmapPoints w' hw' hθ hw hH T)

theorem unitPoints_matrix (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕄).X) :
    HyperbolicScheme.matrixPointsEquiv (D := D) (Fin 3) T (unitPoints w' hw' hθ hw hH T x) =
      cmapPoints w' hw' hθ hw hH T x :=
  (HyperbolicScheme.matrixPointsEquiv (D := D) (Fin 3) T).apply_symm_apply _

omit [FiniteDimensional K D] in
theorem cmapPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (𝕄).X) :
    (cmapPoints w' hw' hθ hw hH T' (a ≫ x) :
        Matrix (Fin 3) (Fin 3) (BinaryScheme.coefficients T' ⊗[K] D)) =
      (cmapPoints w' hw' hθ hw hH T x :
        Matrix (Fin 3) (Fin 3) (BinaryScheme.coefficients T ⊗[K] D)).map
          (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
            (AlgHom.id K D)) := by
  set φ := ((algΓ (CommRingCat.of K)).map a).unop.hom
  have h := Presentation.cmap_map (Q.presentation (BinaryScheme.coefficients T))
    (Q.presentation (BinaryScheme.coefficients T'))
    (φA := (Q.mapA φ).toRingHom) (φB := (mapB (D := D) φ).toRingHom) (Q.mapA_bar φ)
    (Q.mapA_δR φ) (Q.mapB_ιR φ) (Q.mapB_jR φ) (Q.const _ θ) (Q.const _ l₁) (Q.const _ l₂)
    (Q.const _ w) (modelMatrix H w' hw' T x : Matrix (Fin 4) (Fin 4) _)
  have e : ∀ c : field Q.c,
      (Q.mapA φ).toRingHom (Q.const (BinaryScheme.coefficients T) c) =
        Q.const (BinaryScheme.coefficients T') c :=
    fun c => Q.mapA_const _ φ c
  have hm : (modelMatrix H w' hw' T x :
        Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T)).map
        (Q.mapA φ).toRingHom =
      (modelMatrix H w' hw' T' (a ≫ x) :
        Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T')) :=
    (modelMatrix_naturality a x).symm
  rw [hm, e, e, e, e] at h
  exact ((cmapPoints_val hθ hw hH T' (a ≫ x)).trans h.symm).trans
    (congrArg (fun M => Matrix.map M (mapB (D := D) φ)) (cmapPoints_val hθ hw hH T x).symm)

theorem unitPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (𝕄).X) :
    unitPoints w' hw' hθ hw hH T' (a ≫ x) = a ≫ unitPoints w' hw' hθ hw hH T x := by
  apply (HyperbolicScheme.matrixPointsEquiv (D := D) (Fin 3) T').injective
  apply Units.ext
  rw [unitPoints_matrix, HyperbolicScheme.matrixPointsEquiv_naturality, unitPoints_matrix]
  exact cmapPoints_naturality hθ hw hH a x

variable (w' hw') in
/-- The exterior-square morphism into the unit group of `M₃(D)`. -/
def unitHom : 𝕄 ⟶
    FiniteAlgebraUnits.groupScheme (Module.finBasis K (Matrix (Fin 3) (Fin 3) D)) :=
  homOfPoints (unitPoints w' hw' hθ hw hH) (unitPoints_naturality hθ hw hH)

@[simp] theorem unitHom_points (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕄).X) :
    HyperbolicScheme.matrixPointsEquiv (D := D) (Fin 3) T
        (x ≫ (unitHom w' hw' hθ hw hH).hom.hom) =
      cmapPoints w' hw' hθ hw hH T x := by
  rw [unitHom, comp_homOfPoints, unitPoints_matrix]

variable (σ : FirstKindInvolution K D) (q₃ : σ.QuadraticForms (Fin 3))

set_option maxHeartbeats 1600000 in
/-- **The exterior-square morphism lands in the isometry group.** If `σ d = ℓ · bar d · ℓ⁻¹`
with `ℓ = ι l₁ + j ι l₂`, `l̄₁ = -l₁`, and the polar matrix of `q₃` is
`[[0, 1, 0], [1, 0, 0], [0, 0, -(ι θ · ℓ)]]`, then every model point maps into the isometry
group of `q₃` (when `2 ≠ 0` in `K`). -/
theorem unitHom_range_le (h2 : (2 : K) ≠ 0)
    (hl : SU3Root.conjugation K (field Q.c) l₁ = -l₁) {ℓinv : D}
    (hℓ : Q.elem l₁ l₂ * ℓinv = 1) (hσ : ∀ d, σ d = Q.elem l₁ l₂ * Q.bar d * ℓinv)
    (hq : σ.polar q₃ = Presentation.polarMatrix (-(Q.ι θ * Q.elem l₁ l₂))) :
    SubgroupFunctor.range (unitHom w' hw' hθ hw hH) ≤
      SubgroupFunctor.range (σ.isometryGroupι q₃) := by
  intro T z hz
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hz
  rw [σ.mem_range_isometryGroupι_iff q₃ (Quotient.out q₃) (Submodule.Quotient.mk_out q₃)]
  change IsometryCut.defect (σ.matrix (Fin 3)) _ _ ∈
    (σ.matrix (Fin 3)).alternatingSubspace.baseChange (BinaryScheme.coefficients T)
  rw [IsometryCut.alternatingSubspace_baseChange, Submodule.restrictScalars_mem,
    TensorMatrix.mem_alternating_iff, IsometryCut.defect, _root_.map_sub, _root_.map_mul,
    _root_.map_mul, TensorMatrix.adjoint]
  have hu := congrArg
    (fun v : (Matrix (Fin 3) (Fin 3) (BinaryScheme.coefficients T ⊗[K] D))ˣ =>
      (v : Matrix (Fin 3) (Fin 3) (BinaryScheme.coefficients T ⊗[K] D)))
    (unitHom_points hθ hw hH T x)
  change TensorMatrix.equiv (BinaryScheme.coefficients T) (Fin 3)
    (FiniteAlgebraUnits.pointsEquiv _ T (x ≫ (unitHom w' hw' hθ hw hH).hom.hom) :
      BinaryScheme.coefficients T ⊗[K] Matrix (Fin 3) (Fin 3) D) = _ at hu
  rw [hu]
  set R := BinaryScheme.coefficients T
  have hP : Quotient.out q₃ + σ.matrix (Fin 3) (Quotient.out q₃) =
      Presentation.polarMatrix (-(Q.ι θ * Q.elem l₁ l₂)) := by
    rw [← σ.polar_mk, Submodule.Quotient.mk_out, hq]
  have hpol : TensorMatrix.equiv R (Fin 3) ((1 : R) ⊗ₜ[K] Quotient.out q₃) +
      (σ.baseChange R).matrix (Fin 3)
        (TensorMatrix.equiv R (Fin 3) ((1 : R) ⊗ₜ[K] Quotient.out q₃)) =
      Presentation.polarMatrix ((1 : R) ⊗ₜ[K] (-(Q.ι θ * Q.elem l₁ l₂))) := by
    rw [← TensorMatrix.adjoint, FirstKindInvolution.baseChange_tmul, ← map_add,
      ← TensorProduct.tmul_add, hP, TensorMatrix.equiv_tmul]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Presentation.polarMatrix, Algebra.TensorProduct.one_def]
  have h2R : (2 : R) * algebraMap K R 2⁻¹ = 1 := by
    rw [show (2 : R) = algebraMap K R 2 by rw [map_ofNat], ← map_mul, mul_inv_cancel₀ h2,
      map_one]
  apply defect_mem_of_polar ((σ.baseChange R).matrix (Fin 3)) h2R
  rw [hpol]
  exact Q.cmap_mul_polarMatrix_mul_matrix σ hθ hl hw hℓ hσ
    (isSpecialUnitary_modelMatrix (w' := w') (hw' := hw') hH T x)

/-- The isometry group is represented by its inclusion. -/
theorem isometryGroupι_represents :
    (SubgroupFunctor.range (σ.isometryGroupι q₃)).IsRepresentedBy (σ.isometryGroupι q₃) :=
  ⟨(σ.isClosedSubgroup_isometryGroupι q₃).mono_overHom, rfl⟩

variable {σ q₃}

variable (w' hw') in
/-- **The exterior-square morphism** from the Hermitian model group to the isometry group
of `q₃`. -/
def modelHom (h2 : (2 : K) ≠ 0)
    (hl : SU3Root.conjugation K (field Q.c) l₁ = -l₁) {ℓinv : D}
    (hℓ : Q.elem l₁ l₂ * ℓinv = 1) (hσ : ∀ d, σ d = Q.elem l₁ l₂ * Q.bar d * ℓinv)
    (hq : σ.polar q₃ = Presentation.polarMatrix (-(Q.ι θ * Q.elem l₁ l₂))) :
    𝕄 ⟶ σ.isometryGroup q₃ :=
  (isometryGroupι_represents σ q₃).factorHom (unitHom w' hw' hθ hw hH)
    (unitHom_range_le hθ hw hH σ q₃ h2 hl hℓ hσ hq)

@[reassoc] theorem modelHom_comp (h2 : (2 : K) ≠ 0)
    (hl : SU3Root.conjugation K (field Q.c) l₁ = -l₁) {ℓinv : D}
    (hℓ : Q.elem l₁ l₂ * ℓinv = 1) (hσ : ∀ d, σ d = Q.elem l₁ l₂ * Q.bar d * ℓinv)
    (hq : σ.polar q₃ = Presentation.polarMatrix (-(Q.ι θ * Q.elem l₁ l₂))) :
    modelHom w' hw' hθ hw hH h2 hl hℓ hσ hq ≫ σ.isometryGroupι q₃ =
      unitHom w' hw' hθ hw hH :=
  (isometryGroupι_represents σ q₃).factorHom_comp _ _

/-- On every test scheme, `modelHom` followed by the inclusion is the exterior-square map. -/
theorem modelHom_points (h2 : (2 : K) ≠ 0)
    (hl : SU3Root.conjugation K (field Q.c) l₁ = -l₁) {ℓinv : D}
    (hℓ : Q.elem l₁ l₂ * ℓinv = 1) (hσ : ∀ d, σ d = Q.elem l₁ l₂ * Q.bar d * ℓinv)
    (hq : σ.polar q₃ = Presentation.polarMatrix (-(Q.ι θ * Q.elem l₁ l₂)))
    (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ (𝕄).X) :
    HyperbolicScheme.matrixPointsEquiv (D := D) (Fin 3) T
        ((x ≫ (modelHom w' hw' hθ hw hH h2 hl hℓ hσ hq).hom.hom) ≫
          (σ.isometryGroupι q₃).hom.hom) =
      cmapPoints w' hw' hθ hw hH T x := by
  rw [Category.assoc, ← Grp.comp_hom_hom, modelHom_comp, unitHom_points]

end Hom

end QuatData

end Langlands.GroupScheme.KneserThree
