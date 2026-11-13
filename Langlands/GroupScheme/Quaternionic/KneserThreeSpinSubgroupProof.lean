import Langlands.GroupScheme.Quaternionic.KneserThreeBinary
import Langlands.GroupScheme.Quaternionic.KneserThreeModelHom
import Langlands.GroupScheme.Quaternionic.AmbientBinaryQuaternion
import Langlands.GroupScheme.Quaternionic.KneserThreeQuaternion
import Langlands.GroupScheme.Quaternionic.KneserThreeSpinSubgroupStatement
import Langlands.GroupScheme.Quaternionic.SubspaceIsometryExtension
import Langlands.GroupScheme.Quaternionic.WittIndexOneInputs
import Langlands.GroupScheme.Examples.HermitianRootSimplyConnected
import Langlands.GroupScheme.Examples.HermitianRootReductiveGeneration
import Langlands.GroupScheme.Quaternionic.SpinKernelElementaryReduction
import Langlands.GroupScheme.Quaternionic.DegreeTwoNormOneSimplyConnectedProof

/-!
# Proof of Kneser's `A₃ = D₃` subgroup statement

For a hyperbolic pair `(e, f)` of a quaternionic quadratic form `q` of Witt index one, pick `v`
orthogonal to `e, f` with `μ = h(v, v) ≠ 0` (`exists_ortho_polar_ne_zero`). The rows `e, f, v`
span a form with polar matrix `[[0, 1, 0], [1, 0, 0], [0, 0, μ]]` (`polar_pullback`). From `σ` and
`μ` the module `KneserThreeQuaternion` builds quaternion data `Q` and the anisotropic Hermitian
form `H` with weights `(-1, δ)`. The simply connected group is the Hermitian model `SU(H)`. It
maps to the isometry group of `q` by `QuatData.modelHom` followed by the row-space extension
`SubspaceScheme.isometryHom`, and the binary group maps to it by `QuatData.binaryHom`.
`binaryHom_comp_modelHom` identifies the composite with the Library's binary action, and the
Library's generation theorem makes every rational point of `SU(H)` elementary. Together this
proves `KneserThreeSpinSubgroupStatement` (`kneserThreeSpinSubgroup`). With the reduction
`SpinKernelElementaryReduction` and the published `degreeTwoNormOneSimplyConnected` it gives
`SpinKernelElementaryLiftStatement` (`spinKernelElementaryLift`).
-/

noncomputable section

set_option maxRecDepth 8192

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.KneserThree.Quaternion

open Langlands.GroupScheme.Quaternionic QuadField

section Vector

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] {σ : FirstKindInvolution K D}
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n}

/-- A vector orthogonal to a hyperbolic pair with nonzero polar value, in Witt index one. -/
theorem exists_ortho_polar_ne_zero (h2 : (2 : K) ≠ 0) {e f : n → D}
    (h : σ.IsHyperbolicPair q e f) (hw : σ.quadraticWittIndex q ≤ 1)
    (hn : 3 ≤ Fintype.card n) :
    ∃ v : n → D, σ.sesqForm (σ.polar q) v e = 0 ∧ σ.sesqForm (σ.polar q) v f = 0 ∧
      σ.sesqForm (σ.polar q) v v ≠ 0 := by
  obtain ⟨v, hv0, hve, hvf⟩ :=
    FirstKindInvolution.Eichler.exists_ne_zero_ortho (σ := σ) (q := q) e f hn
  refine ⟨v, hve, hvf, fun hvv => hv0 ?_⟩
  apply FirstKindInvolution.Eichler.eq_zero_of_ortho_of_quadraticWittIndex_le_one
    ⟨h.1, h.2.1, h.2.2⟩ hw hve hvf
  obtain ⟨Q, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [FirstKindInvolution.quadraticValue_mk, Submodule.Quotient.mk_eq_zero]
  rw [FirstKindInvolution.sesqForm_polar_mk] at hvv
  exact mem_alternatingSubspace_of_neg σ (h := (2 : K)⁻¹) (mul_inv_cancel₀ h2)
    (eq_neg_of_add_eq_zero_right hvv)

omit [Fintype n] [DecidableEq n] in
theorem entry_eq_sesqForm {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m D) (i k : m) :
    M i k = σ.sesqForm M (Pi.single i 1) (Pi.single k 1) := by
  simp [FirstKindInvolution.sesqForm, Pi.single_apply, apply_ite σ]

/-- The polar matrix of the restriction to the rows `e, f, v`. -/
theorem polar_pullback {e f v : n → D} (h : σ.IsHyperbolicPair q e f)
    (hve : σ.sesqForm (σ.polar q) v e = 0) (hvf : σ.sesqForm (σ.polar q) v f = 0) :
    σ.polar (σ.quadraticPullback (Matrix.of ![e, f, v] : Matrix (Fin 3) n D) q) =
      Presentation.polarMatrix (σ.sesqForm (σ.polar q) v v) := by
  have hentry : ∀ i k : Fin 3,
      σ.polar (σ.quadraticPullback (Matrix.of ![e, f, v] : Matrix (Fin 3) n D) q) i k =
        σ.sesqForm (σ.polar q) (![e, f, v] i) (![e, f, v] k) := by
    intro i k
    refine (entry_eq_sesqForm (σ := σ) _ i k).trans ?_
    rw [σ.polar_quadraticPullback, σ.sesqForm_gramPullback, SubspaceScheme.single_one_vecMul_eq,
      SubspaceScheme.single_one_vecMul_eq]
    rfl
  have hee := σ.sesqForm_polar_self_eq_zero q e h.1
  have hff := σ.sesqForm_polar_self_eq_zero q f h.2.1
  have hef := h.2.2
  have hfe : σ.sesqForm (σ.polar q) f e = 1 := by
    rw [← σ.sesqForm_polar_swap, hef, FirstKindInvolution.map_one]
  have hev : σ.sesqForm (σ.polar q) e v = 0 := by
    rw [← σ.sesqForm_polar_swap, hve, FirstKindInvolution.map_zero]
  have hfv : σ.sesqForm (σ.polar q) f v = 0 := by
    rw [← σ.sesqForm_polar_swap, hvf, FirstKindInvolution.map_zero]
  ext i k
  rw [hentry]
  fin_cases i <;> fin_cases k <;> simp [Presentation.polarMatrix, hee, hff, hef, hfe, hev, hfv,
    hve, hvf]

/-- `polarMatrix s` is invertible when `s ≠ 0`. -/
theorem isUnit_polarMatrix {s : D} (hs : s ≠ 0) : IsUnit (Presentation.polarMatrix s) := by
  refine ⟨⟨Presentation.polarMatrix s, Presentation.polarMatrix s⁻¹, ?_, ?_⟩, rfl⟩ <;>
  · ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Presentation.polarMatrix, Matrix.mul_apply, Fin.sum_univ_three, hs]

end Vector


section BinaryCompat

open HermitianRoot

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]

theorem presentation_ι_includeRight (Q : QuatData K D) (R : Type u) [CommRing R]
    [Algebra K R] (r : R) :
    (Q.presentation R).ι ((Algebra.TensorProduct.includeRight : R →ₐ[K] field Q.c ⊗[K] R) r) =
      algebraMap R (R ⊗[K] D) r := by
  change Q.ιR R (1 ⊗ₜ[K] r) = _
  rw [QuatData.ιR_tmul, map_one, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem product_includeRight (Q : QuatData K D) (R : Type u) [CommRing R]
    [Algebra K R] (g : Matrix (Fin 2) (Fin 2) R) (b : R ⊗[K] D) :
    (Q.presentation R).product
        (g.map (Algebra.TensorProduct.includeRight : R →ₐ[K] field Q.c ⊗[K] R)) b =
      !![algebraMap R (R ⊗[K] D) (g 0 0) * b, algebraMap R (R ⊗[K] D) (g 0 1) * b, 0;
        algebraMap R (R ⊗[K] D) (g 1 0) * b, algebraMap R (R ⊗[K] D) (g 1 1) * b, 0;
        0, 0, 1] := by
  simp only [Presentation.product, Matrix.map_apply, presentation_ι_includeRight]

variable {σ : FirstKindInvolution K D} {q₃ : σ.QuadraticForms (Fin 3)} (R : Type u) [CommRing R]
  [Algebra K R]

/-- The polar coordinates of the plane of the first two standard rows. -/
theorem retraction_eq {s : D} (hq : σ.polar q₃ = Presentation.polarMatrix s) :
    HyperbolicScheme.retraction (Fin 3) σ q₃ (Pi.single 0 1) (Pi.single 1 1) R =
      !![1, 0; 0, 1; 0, 0] := by
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [HyperbolicScheme.retraction, HyperbolicScheme.scalarMatrix,
      FirstKindInvolution.planeRetraction, hq, Presentation.polarMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Pi.single_apply, Algebra.TensorProduct.one_def]

theorem inclusion_eq :
    HyperbolicScheme.inclusion (K := K) (Fin 3) (Pi.single 0 (1 : D)) (Pi.single 1 1) R =
      !![1, 0, 0; 0, 1, 0] := by
  ext i k
  rw [HyperbolicScheme.inclusion, HyperbolicScheme.scalarMatrix, Matrix.map_apply]
  fin_cases i <;> fin_cases k <;>
    simp [FirstKindInvolution.planeInclusion, Algebra.TensorProduct.one_def]

/-- Extending from the plane of the first two standard rows is `[[G, 0], [0, 1]]`. -/
theorem extendUnits_single {s : D} (hq : σ.polar q₃ = Presentation.polarMatrix s)
    (h₃ : σ.IsHyperbolicPair q₃ (Pi.single 0 1) (Pi.single 1 1))
    (G : (Matrix (Fin 2) (Fin 2) (R ⊗[K] D))ˣ) :
    (HyperbolicScheme.extendUnits h₃ R G : Matrix (Fin 3) (Fin 3) (R ⊗[K] D)) =
      !![(G : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 0 0, (G : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 0 1,
        0; (G : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 1 0,
        (G : Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 1 1, 0; 0, 0, 1] := by
  simp only [HyperbolicScheme.extendUnits, SplitMatrixExtension.unitsHom_val,
    SplitMatrixExtension.value]
  rw [retraction_eq R hq, inclusion_eq R]
  ext i k
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply]
  fin_cases i <;> fin_cases k <;> simp

end BinaryCompat

section BinaryMain

open HermitianRoot

variable {K D : Type u} [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] {Q : QuatData K D}
  {H : DiagonalForm (SU3Root.fieldInvolution K (field Q.c)) (Fin 2)}
  {w' : Fin 2 → (field Q.c)ˣ} {hw' : ∀ i, (w' i : field Q.c) = H.weight i}
  {σ : FirstKindInvolution K D} {hdim : Module.finrank K D = 4}
  {hsym : Module.finrank K σ.symmetricSubspace = 3}
  {θ θinv l₁ l₂ w : field Q.c} (hθ : SU3Root.conjugation K (field Q.c) θ = -θ)
  (hθinv : θ * θinv = 1)
  (hw : w * (θ * (l₁ * SU3Root.conjugation K (field Q.c) l₁ -
      algebraMap K (field Q.c) Q.δ * l₂ * SU3Root.conjugation K (field Q.c) l₂)) = 1)
  (hH : H.weight = ![-1, algebraMap K (field Q.c) Q.δ])
  {q₃ : σ.QuadraticForms (Fin 3)}

omit [Infinite K] [Algebra.IsCentral K D] in
theorem tensorAlternatingUnit_inv_val (R : Type u) [CommRing R] [Algebra K R] :
    ((BinaryAction.tensorAlternatingUnit σ hdim hsym R)⁻¹ : (R ⊗[K] D)ˣ) =
      (1 : R) ⊗ₜ[K] (((σ.quaternionAlternatingUnit hdim hsym)⁻¹ : Dˣ) : D) :=
  rfl

omit [Infinite K] [Algebra.IsCentral K D] in
theorem elem_mul_inv (hℓ : Q.elem l₁ l₂ = (σ.quaternionAlternatingUnit hdim hsym : D)) :
    Q.elem l₁ l₂ * (((σ.quaternionAlternatingUnit hdim hsym)⁻¹ : Dˣ) : D) = 1 := by
  rw [hℓ, Units.mul_inv]

omit [Infinite K] [Algebra.IsCentral K D] in
/-- The conjugated product matrix is the binary action, extended by `1`. -/
theorem twistInv_mul_product_mul_twist (R : Type u) [CommRing R] [Algebra K R]
    (hℓ : Q.elem l₁ l₂ = (σ.quaternionAlternatingUnit hdim hsym : D))
    (g : Matrix.SpecialLinearGroup (Fin 2) R) (b : (R ⊗[K] D)ˣ) :
    Presentation.twistInv ((1 : R) ⊗ₜ[K] (((σ.quaternionAlternatingUnit hdim hsym)⁻¹ : Dˣ) : D)) *
        !![algebraMap R (R ⊗[K] D) (g 0 0) * b, algebraMap R (R ⊗[K] D) (g 0 1) * b, 0;
          algebraMap R (R ⊗[K] D) (g 1 0) * b, algebraMap R (R ⊗[K] D) (g 1 1) * b, 0;
          0, 0, 1] *
        (Q.presentation R).twist (l₁ ⊗ₜ[K] (1 : R)) (l₂ ⊗ₜ[K] (1 : R)) =
      !![(BinaryAction.action (BinaryAction.tensorAlternatingUnit σ hdim hsym R) (g, b) :
          Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 0 0,
        (BinaryAction.action (BinaryAction.tensorAlternatingUnit σ hdim hsym R) (g, b) :
          Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 0 1, 0;
        (BinaryAction.action (BinaryAction.tensorAlternatingUnit σ hdim hsym R) (g, b) :
          Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 1 0,
        (BinaryAction.action (BinaryAction.tensorAlternatingUnit σ hdim hsym R) (g, b) :
          Matrix (Fin 2) (Fin 2) (R ⊗[K] D)) 1 1, 0; 0, 0, 1] := by
  have htw : (Q.presentation R).twist (l₁ ⊗ₜ[K] (1 : R)) (l₂ ⊗ₜ[K] (1 : R)) =
      !![1, 0, 0; 0, (1 : R) ⊗ₜ[K] (σ.quaternionAlternatingUnit hdim hsym : D), 0; 0, 0, 1] := by
    rw [Presentation.twist, ← hℓ]
    exact congrArg (fun z => !![1, 0, 0; 0, z, 0; 0, 0, 1]) (Q.presentation_elem_const R l₁ l₂)
  rw [htw]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Presentation.twistInv, Matrix.mul_apply, Fin.sum_univ_three, mul_assoc]

omit [Infinite K] in
/-- The model matrix of a point of `binaryHom` is the binary matrix. -/
theorem modelMatrix_binaryHom (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    (QuatData.modelMatrix H w' hw' T (x ≫ (Q.binaryHom H hH w' hw' hθ hθinv).hom.hom) :
        Matrix (Fin 4) (Fin 4) (field Q.c ⊗[K] BinaryScheme.coefficients T)) =
      Q.binaryMatrix (BinaryScheme.coefficients T) θ θinv
        ((BinaryScheme.pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) (BinaryScheme.coefficients T))
        (((BinaryScheme.pointsEquiv T x).2 : (BinaryScheme.coefficients T ⊗[K] D)ˣ) :
          BinaryScheme.coefficients T ⊗[K] D) := by
  rw [QuatData.modelMatrix_val, Q.binaryHom_points, Q.modelReindex_apply]
  ext i k
  fin_cases i <;> fin_cases k <;> rfl

include hθ hθinv hw hH in
/-- **The binary group through the model.** -/
theorem binaryHom_comp_modelHom (h2 : (2 : K) ≠ 0)
    (hl : SU3Root.conjugation K (field Q.c) l₁ = -l₁)
    (hℓ : Q.elem l₁ l₂ = (σ.quaternionAlternatingUnit hdim hsym : D))
    (hσ : ∀ d, σ d = Q.elem l₁ l₂ * Q.bar d *
      (((σ.quaternionAlternatingUnit hdim hsym)⁻¹ : Dˣ) : D))
    (hq : σ.polar q₃ = Presentation.polarMatrix (-(Q.ι θ * Q.elem l₁ l₂)))
    (h₃ : σ.IsHyperbolicPair q₃ (Pi.single 0 1) (Pi.single 1 1)) :
    Q.binaryHom H hH w' hw' hθ hθinv ≫
        QuatData.modelHom w' hw' hθ hw hH h2 hl (elem_mul_inv hℓ) hσ hq =
      AmbientBinaryScheme.isometryHom σ hdim hsym h₃ := by
  apply hom_ext_points
  intro T x
  apply (QuatData.isometryGroupι_represents σ q₃).1.right_cancellation
  apply (HyperbolicScheme.matrixPointsEquiv (D := D) (Fin 3) T).injective
  rw [Grp.comp_hom_hom, ← Category.assoc, QuatData.modelHom_points,
    AmbientBinaryScheme.isometryHom_points]
  apply Units.ext
  rw [QuatData.cmapPoints_val, modelMatrix_binaryHom hθ hθinv hH, extendUnits_single _ hq h₃]
  have hlinv : (Q.presentation (BinaryScheme.coefficients T)).elem
      (Q.const (BinaryScheme.coefficients T) l₁) (Q.const (BinaryScheme.coefficients T) l₂) *
      ((1 : BinaryScheme.coefficients T) ⊗ₜ[K]
        (((σ.quaternionAlternatingUnit hdim hsym)⁻¹ : Dˣ) : D)) = 1 := by
    rw [QuatData.presentation_elem_const, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      elem_mul_inv hℓ, Algebra.TensorProduct.one_def]
  have hdet : (((BinaryScheme.pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) _).map
      (Algebra.TensorProduct.includeRight :
        BinaryScheme.coefficients T →ₐ[K] field Q.c ⊗[K] BinaryScheme.coefficients T)).det = 1 := by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det, (BinaryScheme.pointsEquiv T x).1.2, map_one]
  have hreal : ∀ i k, (Q.presentation (BinaryScheme.coefficients T)).c.bar
      ((((BinaryScheme.pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) _).map
        (Algebra.TensorProduct.includeRight :
          BinaryScheme.coefficients T →ₐ[K] field Q.c ⊗[K] BinaryScheme.coefficients T)) i k) =
        (((BinaryScheme.pointsEquiv T x).1 : Matrix (Fin 2) (Fin 2) _).map
          (Algebra.TensorProduct.includeRight :
            BinaryScheme.coefficients T →ₐ[K] field Q.c ⊗[K] BinaryScheme.coefficients T)) i k :=
    fun i k => Q.bar_includeRight _
  have hb := Q.presentation_norm_eq_one _
    ((Langlands.CentralSimple.mem_reducedNormOne K D _ (BinaryScheme.pointsEquiv T x).2.val).mp
      (BinaryScheme.pointsEquiv T x).2.property)
  have hc := Presentation.cmap_binary (Q.presentation (BinaryScheme.coefficients T))
    (Q.presentation_unit_const _ hw) (Q.tmul_one_mul_tmul_one hθinv) hreal hdet hb hlinv
  rw [QuatData.binaryMatrix]
  refine hc.trans ?_
  rw [product_includeRight]
  exact twistInv_mul_product_mul_twist _ hℓ (BinaryScheme.pointsEquiv T x).1
    (BinaryScheme.pointsEquiv T x).2.val

end BinaryMain

section Main

variable {K D : Type u} [Field K] [Infinite K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- **The `A₃ = D₃` subgroup through a hyperbolic pair**, given a vector `v` orthogonal to the
pair with nonzero polar value `μ = h(v, v)`. -/
theorem exists_spin_subgroup (h2 : (2 : K) ≠ 0) (σ : FirstKindInvolution K D)
    (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
    {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n} {e f v : n → D}
    (h : σ.IsHyperbolicPair q e f) (hve : σ.sesqForm (σ.polar q) v e = 0)
    (hvf : σ.sesqForm (σ.polar q) v f = 0) (hμ0 : σ.sesqForm (σ.polar q) v v ≠ 0) :
    ∃ (C : GroupScheme (Spec (CommRingCat.of K))) (c : C ⟶ σ.isometryGroup q)
      (j : BinaryScheme.groupScheme (K := K) (D := D) ⟶ C),
      IsSimplyConnected C ∧ j ≫ c = AmbientBinaryScheme.isometryHom σ hdim hsym h ∧
        parabolicElementarySubgroup C = ⊤ := by
  have hμ : σ (σ.sesqForm (σ.polar q) v v) = σ.sesqForm (σ.polar q) v v :=
    σ.sesqForm_polar_swap q v v
  let Q := quatData σ hdim hsym h2 hμ hμ0
  have hδ : Q.δ ≠ 0 := quatData_δ_ne_zero σ hdim hsym h2 hμ hμ0
  have hθ : SU3Root.conjugation K (field Q.c) QuadField.root = -QuadField.root :=
    QuadField.conjugation_root
  have hθinv : (QuadField.root : field Q.c) * QuadField.root⁻¹ = 1 :=
    mul_inv_cancel₀ (root_ne_zero σ hdim hsym h2 hμ hμ0)
  have hw : ((QuadField.root : field Q.c) * (lOne σ hdim hsym h2 hμ hμ0 *
        SU3Root.conjugation K (field Q.c) (lOne σ hdim hsym h2 hμ hμ0) -
      algebraMap K (field Q.c) Q.δ * lTwo σ hdim hsym h2 hμ hμ0 *
        SU3Root.conjugation K (field Q.c) (lTwo σ hdim hsym h2 hμ hμ0)))⁻¹ *
      (QuadField.root * (lOne σ hdim hsym h2 hμ hμ0 *
        SU3Root.conjugation K (field Q.c) (lOne σ hdim hsym h2 hμ hμ0) -
      algebraMap K (field Q.c) Q.δ * lTwo σ hdim hsym h2 hμ hμ0 *
        SU3Root.conjugation K (field Q.c) (lTwo σ hdim hsym h2 hμ hμ0))) = 1 :=
    inv_mul_cancel₀ (mul_ne_zero (root_ne_zero σ hdim hsym h2 hμ hμ0)
      (norm_lOne_lTwo_ne_zero σ hdim hsym h2 hμ hμ0))
  have hH : (Q.diagForm).weight = ![-1, algebraMap K (field Q.c) Q.δ] := rfl
  have hl := conjugation_lOne σ hdim hsym h2 hμ hμ0
  have hℓ : Q.elem (lOne σ hdim hsym h2 hμ hμ0) (lTwo σ hdim hsym h2 hμ hμ0) =
      (σ.quaternionAlternatingUnit hdim hsym : D) := elem_lOne_lTwo σ hdim hsym h2 hμ hμ0
  have hσ := sigma_eq_bar σ hdim hsym h2 hμ hμ0
  have hq₃ := polar_pullback h hve hvf
  have hq : σ.polar (σ.quadraticPullback (Matrix.of ![e, f, v] : Matrix (Fin 3) n D) q) =
      Presentation.polarMatrix (-(Q.ι QuadField.root *
        Q.elem (lOne σ hdim hsym h2 hμ hμ0) (lTwo σ hdim hsym h2 hμ hμ0))) := by
    rw [hq₃, neg_ι_root_mul_elem]
  have hE : IsUnit ((Matrix.of ![e, f, v] : Matrix (Fin 3) n D) * σ.polar q *
      σ.rectangularAdjoint (Matrix.of ![e, f, v] : Matrix (Fin 3) n D)) := by
    rw [← FirstKindInvolution.gramPullback_apply, ← σ.polar_quadraticPullback, hq₃]
    exact isUnit_polarMatrix hμ0
  have he : (Matrix.of ![e, f, v] : Matrix (Fin 3) n D) 0 = e := rfl
  have hf : (Matrix.of ![e, f, v] : Matrix (Fin 3) n D) 1 = f := rfl
  have h₃ := SubspaceScheme.isHyperbolicPair_single he hf h
  refine ⟨HermitianRoot.SchemeModel.groupScheme K (field Q.c) Q.diagForm (Q.diagUnits hδ)
      (Q.diagUnits_val hδ),
    QuatData.modelHom (Q.diagUnits hδ) (Q.diagUnits_val hδ) hθ hw hH h2 hl
      (elem_mul_inv hℓ) hσ hq ≫ SubspaceScheme.isometryHom hE,
    Q.binaryHom Q.diagForm hH (Q.diagUnits hδ) (Q.diagUnits_val hδ) hθ hθinv,
    HermitianRoot.SchemeModel.isSimplyConnected K (field Q.c) Q.diagForm (Q.diagUnits hδ)
      (Q.diagUnits_val hδ), ?_,
    HermitianRoot.SchemeModel.parabolicElementarySubgroup_eq_top K (field Q.c) Q.diagForm
      (Q.diagUnits hδ) (Q.diagUnits_val hδ) (Q.diagForm_isAnisotropic hδ)⟩
  rw [← Category.assoc, binaryHom_comp_modelHom hθ hθinv hw hH h2 hl hℓ hσ hq h₃,
    AmbientBinaryScheme.isometryHom, AmbientBinaryScheme.isometryHom, Category.assoc,
    SubspaceScheme.hyperbolic_isometryHom_comp hE he hf h]

end Main

/-- **Proof of `KneserThreeSpinSubgroupStatement`.** -/
theorem kneserThreeSpinSubgroup : SpinKernel.KneserThreeSpinSubgroupStatement.{u} := by
  intro K _ _ _ _ _ h2 D _ _ _ _ hD σ hsym m hm q _ hw1 e f h
  have hn : 3 ≤ Fintype.card (Fin m) := by rcases hm with rfl | rfl <;> simp
  obtain ⟨v, hve, hvf, hμ0⟩ := exists_ortho_polar_ne_zero h2 h hw1.le hn
  obtain ⟨C, c, j, hC, hjc, htop⟩ := exists_spin_subgroup h2 σ hD hsym h hve hvf hμ0
  refine ⟨C, c, j, hC, hjc, ?_⟩
  rw [htop]
  exact Subgroup.mem_top _

end Langlands.GroupScheme.KneserThree.Quaternion

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

/-- **`SpinKernelElementaryLiftStatement` holds**: the reduction
`spinKernelElementaryLift_of_kneserThreeSpinSubgroup` applied to the published
`degreeTwoNormOneSimplyConnected` and to `kneserThreeSpinSubgroup`. -/
theorem spinKernelElementaryLift : SpinKernelElementaryLiftStatement.{u} :=
  spinKernelElementaryLift_of_kneserThreeSpinSubgroup
    CentralSimpleUnits.degreeTwoNormOneSimplyConnected
    Langlands.GroupScheme.KneserThree.Quaternion.kneserThreeSpinSubgroup

/-- **The Kneser–Tits property, given the kernel generator statement.** With the Levi lifts
from `spinLeviLift_of_degreeTwoNormOneSimplyConnected` and `spinKernelElementaryLift`, only
`SpinKernelGeneratorStatement` remains. -/
theorem localSpinKneserTits_of_spinKernelGenerator (h : SpinKernelGeneratorStatement.{u}) :
    LocalSpinKneserTitsStatement.{u} :=
  localSpinKneserTits_of_spinKernel
    (spinLeviLift_of_degreeTwoNormOneSimplyConnected
      CentralSimpleUnits.degreeTwoNormOneSimplyConnected) h spinKernelElementaryLift

end Langlands.GroupScheme.Quaternionic.SpinKernel
