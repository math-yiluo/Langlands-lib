import Langlands.GroupScheme.Quaternionic.KneserThreeCore
import Langlands.GroupScheme.Quaternionic.KneserThreeSplitting
import Langlands.GroupScheme.Quaternionic.BinaryQuaternionGroupScheme
import Langlands.GroupScheme.Examples.HermitianRootGroupScheme
import Langlands.Algebra.ReducedNormFiniteChart
import Langlands.Algebra.CentralSimpleScalarExtension

/-!
# The binary group `SL₂ × SL₁(D)` inside the Hermitian model `SU₄`
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree

open QuadField

namespace Presentation

variable {A B : Type*} [CommRing A] [Ring B] (P : Presentation A B)

/-- The norm `a ā - δ a' ā'` of `ι a + j ι a'`. -/
def norm (b : B) : A := P.fst b * P.c.bar (P.fst b) - P.δ * P.snd b * P.c.bar (P.snd b)

theorem det_rep (b : B) : (P.rep b).det = P.norm b := by
  rw [rep, Matrix.det_fin_two_of, norm]
  ring

variable {θ θinv : A}

theorem bar_inv (hθ : P.c.bar θ = -θ) (hθinv : θ * θinv = 1) : P.c.bar θinv = -θinv := by
  have h : P.c.bar θ * P.c.bar θinv = 1 := by
    rw [← map_mul, hθinv, map_one]
  rw [hθ] at h
  linear_combination (-θinv) * h - P.c.bar θinv * hθinv

theorem binary_one : P.binary θ θinv 1 1 = 1 := by
  ext i k
  fin_cases i <;> fin_cases k <;> simp [binary]

theorem binary_mul (hθinv : θ * θinv = 1) (g g' : Matrix (Fin 2) (Fin 2) A) (b b' : B) :
    P.binary θ θinv (g * g') (b * b') = P.binary θ θinv g b * P.binary θ θinv g' b' := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [binary, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_two, P.bar_δ] <;>
    first
    | ring1
    | linear_combination (-(g 0 1 * g' 1 0)) * hθinv
    | linear_combination (-(g 1 0 * g' 0 1)) * hθinv

theorem conjT_binary_mul_gram_mul_binary (hθ : P.c.bar θ = -θ) (hθinv : θ * θinv = 1)
    {g : Matrix (Fin 2) (Fin 2) A} (hg : ∀ i k, P.c.bar (g i k) = g i k) (hdet : g.det = 1)
    {b : B} (hb : P.norm b = 1) :
    P.conjT (P.binary θ θinv g b) * P.gram * P.binary θ θinv g b = P.gram := by
  have hi := P.bar_inv hθ hθinv
  rw [Matrix.det_fin_two] at hdet
  rw [norm] at hb
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [conjT, gram, binary, Matrix.mul_apply, Fin.sum_univ_four, hg, hθ, hi, P.bar_δ] <;>
    first
    | ring1
    | linear_combination hdet - (g 0 1 * g 1 0) * hθinv
    | linear_combination hdet + (g 0 1 * g 1 0) * hθinv
    | linear_combination hb
    | linear_combination -P.δ * hb

theorem det_binary (hθinv : θ * θinv = 1) (g : Matrix (Fin 2) (Fin 2) A) (b : B) :
    (P.binary θ θinv g b).det = g.det * P.norm b := by
  rw [Matrix.det_fin_two, norm]
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := rfl
  simp [binary, Matrix.det_succ_row_zero, Fin.sum_univ_succ, h32]
  linear_combination (-(g 0 1 * g 1 0 * (P.fst b * P.c.bar (P.fst b) -
    P.δ * P.snd b * P.c.bar (P.snd b)))) * hθinv

theorem isSpecialUnitary_binary (hθ : P.c.bar θ = -θ) (hθinv : θ * θinv = 1)
    {g : Matrix (Fin 2) (Fin 2) A} (hg : ∀ i k, P.c.bar (g i k) = g i k) (hdet : g.det = 1)
    {b : B} (hb : P.norm b = 1) : P.IsSpecialUnitary (P.binary θ θinv g b) :=
  ⟨P.conjT_binary_mul_gram_mul_binary hθ hθinv hg hdet hb,
    by rw [P.det_binary hθinv, hdet, hb, one_mul]⟩

end Presentation

namespace QuatData

section FieldPresentation

variable {K D : Type u} [Field K] [Ring D] [Algebra K D] (Q : QuatData K D)

/-- `D = ι(L) ⊕ j ι(L)` as a presentation over the quadratic field `L` itself. -/
def fieldPresentation : Presentation (field Q.c) D where
  c := SU3Root.fieldInvolution K (field Q.c)
  ι := Q.ι.toRingHom
  j := Q.j
  δ := algebraMap K (field Q.c) Q.δ
  bar_δ := by
    rw [SU3Root.fieldInvolution_bar, AlgEquiv.commutes]
  j_mul a := Q.j_mul_ι a
  j_mul_self := by
    rw [Q.j_mul_j]
    exact (Q.ι.commutes Q.δ).symm
  fst := Q.fst.toAddMonoidHom
  snd := Q.snd.toAddMonoidHom
  decompose := Q.decompose
  fst_mk := Q.fst_mk
  snd_mk := Q.snd_mk

@[simp] theorem fieldPresentation_fst (d : D) : Q.fieldPresentation.fst d = Q.fst d := rfl

@[simp] theorem fieldPresentation_snd (d : D) : Q.fieldPresentation.snd d = Q.snd d := rfl

@[simp] theorem fieldPresentation_δ :
    Q.fieldPresentation.δ = algebraMap K (field Q.c) Q.δ := rfl

@[simp] theorem fieldPresentation_bar (a : field Q.c) :
    Q.fieldPresentation.c.bar a = SU3Root.conjugation K (field Q.c) a := rfl

/-- The matrix representation `D → M₂(L)` as a `K`-algebra homomorphism. -/
def repAlgHom : D →ₐ[K] Matrix (Fin 2) (Fin 2) (field Q.c) where
  toFun := Q.fieldPresentation.rep
  map_one' := Q.fieldPresentation.rep_one
  map_mul' := Q.fieldPresentation.rep_mul
  map_zero' := Q.fieldPresentation.rep_zero
  map_add' := Q.fieldPresentation.rep_add
  commutes' k := by
    have h : algebraMap K D k = Q.fieldPresentation.ι (algebraMap K (field Q.c) k) :=
      (Q.ι.commutes k).symm
    rw [h]
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [Presentation.rep, Matrix.algebraMap_matrix_apply]
    exact (SU3Root.conjugation K (field Q.c)).commutes k

@[simp] theorem repAlgHom_apply (d : D) : Q.repAlgHom d = Q.fieldPresentation.rep d := rfl

/-- The `L`-algebra map `L ⊗[K] D → M₂(L)`, `l ⊗ d ↦ l · rep d`. -/
def chartHom : field Q.c ⊗[K] D →ₐ[field Q.c] Matrix (Fin 2) (Fin 2) (field Q.c) :=
  Algebra.TensorProduct.lift (Algebra.ofId (field Q.c) _) Q.repAlgHom
    (fun l d => by
      rw [Algebra.ofId_apply]
      exact Algebra.commute_algebraMap_left l _)

theorem chartHom_one_tmul (d : D) :
    Q.chartHom (1 ⊗ₜ[K] d) = Q.fieldPresentation.rep d := by
  rw [chartHom, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rfl

end FieldPresentation

section Chart

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (Q : QuatData K D)

theorem chartHom_bijective : Function.Bijective Q.chartHom := by
  have : IsSimpleRing (field Q.c ⊗[K] D) := CentralSimple.isSimpleRing_baseChange K D (field Q.c)
  have hinj : Function.Injective Q.chartHom := Q.chartHom.toRingHom.injective
  refine ⟨hinj, ?_⟩
  have hrank : Module.finrank (field Q.c) (field Q.c ⊗[K] D) =
      Module.finrank (field Q.c) (Matrix (Fin 2) (Fin 2) (field Q.c)) := by
    rw [Module.finrank_baseChange, Module.finrank_eq_card_basis Q.basis, Module.finrank_matrix,
      Module.finrank_self]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := Q.chartHom.toLinearMap)).mp hinj

/-- The splitting chart `L ⊗[K] D ≃ M₂(L)`. -/
def chart : field Q.c ⊗[K] D ≃ₐ[field Q.c] Matrix (Fin 2) (Fin 2) (field Q.c) :=
  AlgEquiv.ofBijective Q.chartHom Q.chartHom_bijective

theorem chart_one_tmul (d : D) : Q.chart (1 ⊗ₜ[K] d) = Q.fieldPresentation.rep d :=
  Q.chartHom_one_tmul d

variable (R : Type u) [CommRing R] [Algebra K R]

theorem splittingMap_map_includeRight (b : R ⊗[K] D) :
    ReducedNorm.splittingMap Q.chart (field Q.c ⊗[K] R)
        (Algebra.TensorProduct.map Algebra.TensorProduct.includeRight (AlgHom.id K D) b) =
      (Q.presentation R).rep b := by
  induction b using TensorProduct.inductionOn with
  | tmul r d =>
    rw [Algebra.TensorProduct.map_tmul, ReducedNorm.splittingMap_tmul, chart_one_tmul]
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [Presentation.rep, QuatData.presentation, Algebra.TensorProduct.tmul_mul_tmul,
        QuatData.δR, Algebra.TensorProduct.algebraMap_apply, QuatData.tensorInvolution_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, Presentation.rep_add]

/-- **Reduced norm in the presentation.** The reduced norm of `b ∈ R ⊗[K] D`, viewed in
`L ⊗[K] R`, is the norm `a ā - δ a' ā'` of the presentation. -/
theorem includeRight_reducedNorm (b : R ⊗[K] D) :
    (Algebra.TensorProduct.includeRight : R →ₐ[K] field Q.c ⊗[K] R)
        (CentralSimple.reducedNorm K D R b) = (Q.presentation R).norm b := by
  rw [← CentralSimple.reducedNorm_naturality,
    CentralSimple.reducedNorm_eq_det_fintype K D Q.chart, splittingMap_map_includeRight,
    Presentation.det_rep]

theorem presentation_norm_eq_one {b : R ⊗[K] D}
    (hb : CentralSimple.reducedNorm K D R b = 1) : (Q.presentation R).norm b = 1 := by
  rw [← includeRight_reducedNorm, hb, map_one]

end Chart

section BinaryMatrix

variable {K D : Type u} [Field K] [Ring D] [Algebra K D] (Q : QuatData K D)

theorem presentation_fst_eq (R : Type u) [CommRing R] [Algebra K R] (b : R ⊗[K] D) :
    (Q.presentation R).fst b = Q.fstR R b := rfl

theorem presentation_snd_eq (R : Type u) [CommRing R] [Algebra K R] (b : R ⊗[K] D) :
    (Q.presentation R).snd b = Q.sndR R b := rfl

theorem presentation_δ_eq (R : Type u) [CommRing R] [Algebra K R] :
    (Q.presentation R).δ = Q.δR R := rfl

theorem fstR_mapB {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    (φ : R →ₐ[K] R') (b : R ⊗[K] D) : Q.fstR R' (mapB φ b) = Q.mapA φ (Q.fstR R b) := by
  induction b using TensorProduct.inductionOn with
  | tmul r d => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem sndR_mapB {R R' : Type u} [CommRing R] [Algebra K R] [CommRing R'] [Algebra K R']
    (φ : R →ₐ[K] R') (b : R ⊗[K] D) : Q.sndR R' (mapB φ b) = Q.mapA φ (Q.sndR R b) := by
  induction b using TensorProduct.inductionOn with
  | tmul r d => simp
  | add x y hx hy => simp only [map_add, hx, hy]

variable (R : Type u) [CommRing R] [Algebra K R] (θ θinv : field Q.c)

/-- The binary matrix of `(g, b)` over `L ⊗[K] R`: `g` on `top, bot` twisted by `diag(1, θ)`,
and `rep b` on `m₀, m₁`. -/
def binaryMatrix (g : Matrix (Fin 2) (Fin 2) R) (b : R ⊗[K] D) :
    Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] R) :=
  (Q.presentation R).binary (θ ⊗ₜ[K] (1 : R)) (θinv ⊗ₜ[K] (1 : R))
    (g.map (Algebra.TensorProduct.includeRight : R →ₐ[K] field Q.c ⊗[K] R)) b

variable {R θ θinv}

theorem tmul_one_mul_tmul_one (hθinv : θ * θinv = 1) :
    θ ⊗ₜ[K] (1 : R) * θinv ⊗ₜ[K] (1 : R) = 1 := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, hθinv, one_mul]
  rfl

theorem bar_tmul_one (hθ : SU3Root.conjugation K (field Q.c) θ = -θ) :
    (Q.presentation R).c.bar (θ ⊗ₜ[K] (1 : R)) = -(θ ⊗ₜ[K] (1 : R)) := by
  rw [presentation_c, tensorInvolution_tmul, hθ, TensorProduct.neg_tmul]

theorem bar_includeRight (r : R) :
    (Q.presentation R).c.bar
        ((Algebra.TensorProduct.includeRight : R →ₐ[K] field Q.c ⊗[K] R) r) =
      (Algebra.TensorProduct.includeRight : R →ₐ[K] field Q.c ⊗[K] R) r := by
  rw [Algebra.TensorProduct.includeRight_apply, presentation_c, tensorInvolution_tmul, map_one]

theorem isSpecialUnitary_binaryMatrix (hθ : SU3Root.conjugation K (field Q.c) θ = -θ)
    (hθinv : θ * θinv = 1) {g : Matrix (Fin 2) (Fin 2) R} (hg : g.det = 1)
    {b : R ⊗[K] D} (hb : (Q.presentation R).norm b = 1) :
    (Q.presentation R).IsSpecialUnitary (Q.binaryMatrix R θ θinv g b) := by
  refine (Q.presentation R).isSpecialUnitary_binary (Q.bar_tmul_one hθ)
    (Q.tmul_one_mul_tmul_one hθinv) (fun i k => Q.bar_includeRight (g i k)) ?_ hb
  have h := (RingHom.map_det
    (Algebra.TensorProduct.includeRight : R →ₐ[K] field Q.c ⊗[K] R).toRingHom g).symm
  rw [hg, map_one] at h
  exact h

theorem binaryMatrix_one : Q.binaryMatrix R θ θinv 1 1 = 1 := by
  rw [binaryMatrix, Matrix.map_one _ (map_zero _) (map_one _)]
  exact (Q.presentation R).binary_one

theorem binaryMatrix_mul (hθinv : θ * θinv = 1) (g g' : Matrix (Fin 2) (Fin 2) R)
    (b b' : R ⊗[K] D) :
    Q.binaryMatrix R θ θinv (g * g') (b * b') =
      Q.binaryMatrix R θ θinv g b * Q.binaryMatrix R θ θinv g' b' := by
  rw [binaryMatrix, Matrix.map_mul]
  exact (Q.presentation R).binary_mul (Q.tmul_one_mul_tmul_one hθinv) _ _ _ _

/-- Naturality of the binary matrix in the coefficient algebra. -/
theorem binaryMatrix_map {R' : Type u} [CommRing R'] [Algebra K R'] (φ : R →ₐ[K] R')
    (g : Matrix (Fin 2) (Fin 2) R) (b : R ⊗[K] D) :
    Q.binaryMatrix R' θ θinv (g.map φ) (mapB φ b) =
      (Q.binaryMatrix R θ θinv g b).map (Q.mapA φ) := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [binaryMatrix, Presentation.binary, presentation_fst_eq, presentation_snd_eq,
      presentation_δ_eq, fstR_mapB, sndR_mapB, mapA_bar, mapA_δR]

end BinaryMatrix

end QuatData

/-- The coordinate order `(top, m₀, m₁, bot)` of `HermitianRoot.Index (Fin 2)`. -/
def fourIndexEquiv : Fin 4 ≃ HermitianRoot.Index (Fin 2) where
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

section Scheme

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite HermitianRoot Quaternionic
open scoped _root_.CategoryTheory.MonObj

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (Q : QuatData K D)
  (H : DiagonalForm (SU3Root.fieldInvolution K (field Q.c)) (Fin 2))
  {θ θinv : field Q.c}

variable (T : Over (Spec (CommRingCat.of K)))

/-- The model's coefficient ring `SpecialLinear.WeilRoot.tensorAlgebra K L T` is
`L ⊗[K] R` for `R = BinaryScheme.coefficients T`, definitionally. -/
def coefficientEquiv :
    field Q.c ⊗[K] BinaryScheme.coefficients T ≃+*
      SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T :=
  RingEquiv.refl _

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
@[simp] theorem coefficientEquiv_apply (a : field Q.c ⊗[K] BinaryScheme.coefficients T) :
    Q.coefficientEquiv T a = a := rfl

/-- Reindex `(top, m₀, m₁, bot)` to `Index (Fin 2)` over the model's coefficient ring. -/
def modelReindex :
    Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T) ≃+*
      Matrix (Index (Fin 2)) (Index (Fin 2))
        (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T) :=
  (Q.coefficientEquiv T).mapMatrix.trans (Matrix.reindexRingEquiv _ fourIndexEquiv)

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
theorem modelReindex_apply (M : Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T)) :
    Q.modelReindex T M =
      (M.map (Q.coefficientEquiv T)).submatrix fourIndexEquiv.symm fourIndexEquiv.symm :=
  rfl

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
theorem gram_tensorForm (hH : H.weight = ![-1, algebraMap K (field Q.c) Q.δ]) :
    gram (SchemeModel.tensorForm K (field Q.c) H T) =
      Q.modelReindex T (Q.presentation (BinaryScheme.coefficients T)).gram := by
  have hw0 : (SchemeModel.tensorForm K (field Q.c) H T).weight 0 = -1 := by
    change algebraMap (field Q.c) _ (H.weight 0) = -1
    rw [hH]
    simp
  have hw1 : (SchemeModel.tensorForm K (field Q.c) H T).weight 1 =
      (Q.presentation (BinaryScheme.coefficients T)).δ := by
    change algebraMap (field Q.c) _ (H.weight 1) = _
    rw [hH]
    rfl
  have h : (Q.presentation (BinaryScheme.coefficients T)).gram.map (Q.coefficientEquiv T) =
      (gram (SchemeModel.tensorForm K (field Q.c) H T)).submatrix fourIndexEquiv fourIndexEquiv := by
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Presentation.gram, gram, fourIndexEquiv, Matrix.fromBlocks, hw0, hw1]
  rw [modelReindex_apply, h, Matrix.submatrix_submatrix]
  simp

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
theorem conjugateTranspose_modelReindex
    (M : Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T)) :
    conjugateTranspose (SU3Root.SchemeModel.coefficientInvolution K (field Q.c) T)
        (Q.modelReindex T M) =
      Q.modelReindex T ((Q.presentation (BinaryScheme.coefficients T)).conjT M) :=
  rfl

variable (hH : H.weight = ![-1, algebraMap K (field Q.c) Q.δ])
  (hθ : SU3Root.conjugation K (field Q.c) θ = -θ) (hθinv : θ * θinv = 1)

/-- The binary matrices as a monoid homomorphism on the concrete binary group. -/
def binaryMatrixHom (R : Type u) [CommRing R] [Algebra K R] :
    Matrix.SpecialLinearGroup (Fin 2) R × CentralSimple.reducedNormOne K D R →*
      Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] R) where
  toFun x := Q.binaryMatrix R θ θinv (x.1 : Matrix (Fin 2) (Fin 2) R)
    ((x.2 : (R ⊗[K] D)ˣ) : R ⊗[K] D)
  map_one' := Q.binaryMatrix_one
  map_mul' x y := by
    rw [Prod.fst_mul, Prod.snd_mul, Matrix.SpecialLinearGroup.coe_mul, Subgroup.coe_mul,
      Units.val_mul]
    exact Q.binaryMatrix_mul hθinv _ _ _ _

/-- The reindexed binary matrices as units over the model's coefficient ring. -/
def modelMatrixHom :
    Matrix.SpecialLinearGroup (Fin 2) (BinaryScheme.coefficients T) ×
      CentralSimple.reducedNormOne K D (BinaryScheme.coefficients T) →*
        Matrix.GeneralLinearGroup (Index (Fin 2))
          (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T) :=
  (Units.map (Q.modelReindex T).toMonoidHom).comp
    (Q.binaryMatrixHom hθinv (BinaryScheme.coefficients T)).toHomUnits

theorem modelMatrixHom_val
    (x : Matrix.SpecialLinearGroup (Fin 2) (BinaryScheme.coefficients T) ×
      CentralSimple.reducedNormOne K D (BinaryScheme.coefficients T)) :
    ((Q.modelMatrixHom T hθinv x : Matrix.GeneralLinearGroup (Index (Fin 2))
        (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T)) :
          Matrix (Index (Fin 2)) (Index (Fin 2))
            (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T)) =
      Q.modelReindex T (Q.binaryMatrix (BinaryScheme.coefficients T) θ θinv
        (x.1 : Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T))
        ((x.2 : (BinaryScheme.coefficients T ⊗[K] D)ˣ) : BinaryScheme.coefficients T ⊗[K] D)) :=
  rfl

include hH hθ in
theorem modelMatrixHom_mem
    (x : Matrix.SpecialLinearGroup (Fin 2) (BinaryScheme.coefficients T) ×
      CentralSimple.reducedNormOne K D (BinaryScheme.coefficients T)) :
    Q.modelMatrixHom T hθinv x ∈ specialUnitarySubgroup (SchemeModel.tensorForm K (field Q.c) H T) := by
  have hU := Q.isSpecialUnitary_binaryMatrix hθ hθinv x.1.2
    (Q.presentation_norm_eq_one _ ((CentralSimple.mem_reducedNormOne K D _ _).mp x.2.2))
  refine ⟨?_, ?_⟩
  · change conjugateTranspose _ _ * gram _ * _ = gram _
    rw [modelMatrixHom_val, Q.gram_tensorForm H T hH, conjugateTranspose_modelReindex,
      ← map_mul, ← map_mul, hU.1]
  · apply Units.ext
    change Matrix.det _ = 1
    rw [modelMatrixHom_val, modelReindex_apply, Matrix.det_submatrix_equiv_self]
    exact hU.2

include hH hθ in
/-- The binary group's concrete points in the special unitary group of the tensor form. -/
def modelPointsHom :
    Matrix.SpecialLinearGroup (Fin 2) (BinaryScheme.coefficients T) ×
      CentralSimple.reducedNormOne K D (BinaryScheme.coefficients T) →*
        specialUnitarySubgroup (SchemeModel.tensorForm K (field Q.c) H T) :=
  MonoidHom.codRestrict (Q.modelMatrixHom T hθinv) _ (Q.modelMatrixHom_mem H T hH hθ hθinv)

theorem modelPointsHom_val
    (x : Matrix.SpecialLinearGroup (Fin 2) (BinaryScheme.coefficients T) ×
      CentralSimple.reducedNormOne K D (BinaryScheme.coefficients T)) :
    (((Q.modelPointsHom H T hH hθ hθinv x).1 : Matrix.GeneralLinearGroup (Index (Fin 2))
        (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T)) :
          Matrix (Index (Fin 2)) (Index (Fin 2))
            (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T)) =
      Q.modelReindex T (Q.binaryMatrix (BinaryScheme.coefficients T) θ θinv
        (x.1 : Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T))
        ((x.2 : (BinaryScheme.coefficients T ⊗[K] D)ˣ) : BinaryScheme.coefficients T ⊗[K] D)) :=
  rfl

end Scheme

section Hom


open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite HermitianRoot Quaternionic
open scoped _root_.CategoryTheory.MonObj

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  [Algebra.IsCentral K D] (Q : QuatData K D)

set_option backward.isDefEq.respectTransparency false in
omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
/-- The model's coefficient map along `a : T' ⟶ T` is `id_L ⊗ φ`. -/
theorem tensorMap_eq_mapA {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (y : SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T) :
    SpecialLinear.WeilRoot.tensorMap K (field Q.c) a y =
      Q.mapA ((algΓ (CommRingCat.of K)).map a).unop.hom y := by
  induction y using TensorProduct.inductionOn with
  | tmul e r => rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]

set_option backward.isDefEq.respectTransparency false in
omit Q in
theorem binaryPointsEquiv_fst_comp {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    ((BinaryScheme.pointsEquiv T' (a ≫ x)).1 :
        Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T')) =
      ((BinaryScheme.pointsEquiv T x).1 :
        Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T)).map
          ((algΓ (CommRingCat.of K)).map a).unop.hom := by
  have h1 : (BinaryScheme.pointsEquiv T' (a ≫ x)).1 =
      Matrix.SpecialLinearGroup.map ((algΓ (CommRingCat.of K)).map a).unop.hom.toRingHom
        (BinaryScheme.pointsEquiv T x).1 := by
    change SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) T'
      ((a ≫ x) ≫ CartesianMonoidalCategory.fst _ _) = _
    rw [Category.assoc, SpecialLinear.pointsEquiv_naturality]
    rfl
  rw [h1]
  rfl

set_option backward.isDefEq.respectTransparency false in
omit Q in
theorem binaryPointsEquiv_snd_comp {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    ((BinaryScheme.pointsEquiv T' (a ≫ x)).2 : (BinaryScheme.coefficients T' ⊗[K] D)ˣ) =
      Units.map (Algebra.TensorProduct.map ((algΓ (CommRingCat.of K)).map a).unop.hom
        (AlgHom.id K D)).toMonoidHom
          ((BinaryScheme.pointsEquiv T x).2 : (BinaryScheme.coefficients T ⊗[K] D)ˣ) := by
  change FiniteAlgebraUnits.pointsEquiv (Module.finBasis K D) T'
    (((a ≫ x) ≫ CartesianMonoidalCategory.snd _ _) ≫
      (CentralSimpleUnits.normOneι K D).hom.hom) = _
  rw [Category.assoc, Category.assoc, FiniteAlgebraUnits.pointsEquiv_naturality]
  rfl

variable (H : DiagonalForm (SU3Root.fieldInvolution K (field Q.c)) (Fin 2))
  (hH : H.weight = ![-1, algebraMap K (field Q.c) Q.δ])
  (w : Fin 2 → (field Q.c)ˣ) (hw : ∀ i, (w i : field Q.c) = H.weight i)
  {θ θinv : field Q.c} (hθ : SU3Root.conjugation K (field Q.c) θ = -θ) (hθinv : θ * θinv = 1)

/-- The binary morphism on the points of a test scheme. -/
def binaryPoints (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) →*
      (T ⟶ (SchemeModel.groupScheme K (field Q.c) H w hw).X) :=
  (SchemeModel.pointsEquiv K (field Q.c) H w hw T).symm.toMonoidHom.comp
    ((Q.modelPointsHom H T hH hθ hθinv).comp (BinaryScheme.pointsEquiv T).toMonoidHom)

theorem pointsEquiv_binaryPoints (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    SchemeModel.pointsEquiv K (field Q.c) H w hw T (Q.binaryPoints H hH w hw hθ hθinv T x) =
      Q.modelPointsHom H T hH hθ hθinv (BinaryScheme.pointsEquiv T x) := by
  rw [binaryPoints, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem binaryPoints_naturality {T T' : Over (Spec (CommRingCat.of K))} (a : T' ⟶ T)
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    Q.binaryPoints H hH w hw hθ hθinv T' (a ≫ x) =
      a ≫ Q.binaryPoints H hH w hw hθ hθinv T x := by
  apply (SchemeModel.pointsEquiv K (field Q.c) H w hw T').injective
  rw [SchemeModel.pointsEquiv_map, pointsEquiv_binaryPoints, pointsEquiv_binaryPoints]
  apply Subtype.ext
  apply Units.ext
  rw [specialUnitaryMap_val, modelPointsHom_val, modelPointsHom_val,
    binaryPointsEquiv_fst_comp, binaryPointsEquiv_snd_comp]
  have key := Q.binaryMatrix_map (θ := θ) (θinv := θinv)
    ((algΓ (CommRingCat.of K)).map a).unop.hom
    ((BinaryScheme.pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T))
    (((BinaryScheme.pointsEquiv T x).2 : (BinaryScheme.coefficients T ⊗[K] D)ˣ) :
      BinaryScheme.coefficients T ⊗[K] D)
  ext i k
  rw [modelReindex_apply, modelReindex_apply]
  simp only [Matrix.submatrix_apply, Matrix.map_apply, coefficientEquiv_apply]
  exact congrFun (congrFun key _) _

/-- **The binary morphism** `SL₂ × SL₁(D) → SU(H)`. On points, `(g, b)` goes to the matrix
`binaryMatrix g b` over `L ⊗[K] R`, read in the coordinates `(top, m₀, m₁, bot)`. -/
def binaryHom :
    BinaryScheme.groupScheme (K := K) (D := D) ⟶ SchemeModel.groupScheme K (field Q.c) H w hw :=
  homOfPoints (Q.binaryPoints H hH w hw hθ hθinv)
    (fun a x => Q.binaryPoints_naturality H hH w hw hθ hθinv a x)

/-- The points of `binaryHom`, as `Index (Fin 2)`-matrices over the model's coefficient ring. -/
theorem binaryHom_points (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    ((SchemeModel.pointsEquiv K (field Q.c) H w hw T
        (x ≫ (Q.binaryHom H hH w hw hθ hθinv).hom.hom)).1 :
          Matrix (Index (Fin 2)) (Index (Fin 2))
            (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T)) =
      Q.modelReindex T (Q.binaryMatrix (BinaryScheme.coefficients T) θ θinv
        ((BinaryScheme.pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T))
        (((BinaryScheme.pointsEquiv T x).2 : (BinaryScheme.coefficients T ⊗[K] D)ˣ) :
          BinaryScheme.coefficients T ⊗[K] D)) := by
  rw [binaryHom, comp_homOfPoints, pointsEquiv_binaryPoints]
  exact Q.modelPointsHom_val H T hH hθ hθinv _

/-- The points of `binaryHom` in the coordinates `(top, m₀, m₁, bot)` over `L ⊗[K] R`. -/
theorem binaryHom_points_reindex (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    (((SchemeModel.pointsEquiv K (field Q.c) H w hw T
        (x ≫ (Q.binaryHom H hH w hw hθ hθinv).hom.hom)).1 :
          Matrix (Index (Fin 2)) (Index (Fin 2))
            (SpecialLinear.WeilRoot.tensorAlgebra K (field Q.c) T)).submatrix
              fourIndexEquiv fourIndexEquiv).map (Q.coefficientEquiv T).symm =
      Q.binaryMatrix (BinaryScheme.coefficients T) θ θinv
        ((BinaryScheme.pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T))
        (((BinaryScheme.pointsEquiv T x).2 : (BinaryScheme.coefficients T ⊗[K] D)ˣ) :
          BinaryScheme.coefficients T ⊗[K] D) := by
  rw [binaryHom_points, modelReindex_apply]
  ext i k
  simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rfl

end Hom

end QuatData

end Langlands.GroupScheme.KneserThree
