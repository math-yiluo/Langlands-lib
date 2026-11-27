import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtension
import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedSubmodules
import Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalTensorComparisonProof
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The ordinary relative tensor product of a finite Banach map under ground field extension -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open scoped TensorProduct

section Coefficients

variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] {n : ℕ} (b : Fin n → B)

local notation "T" => C ⊗[A] B
local notation "inl" => Algebra.TensorProduct.includeLeftRingHom (R := A) (A := C) (B := B)
local notation "inr" => Algebra.TensorProduct.includeRight (R := A) (A := C) (B := B)

private def coefficients : (Fin n → C) →ₗ[C] T where
  toFun w := ∑ i, inl (w i) * inr (b i)
  map_add' w w' := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]
    change ∑ i, inl (c * w i) * inr (b i) = inl c * ∑ i, inl (w i) * inr (b i)
    simp only [map_mul, Finset.mul_sum, mul_assoc]

private theorem coefficients_apply (w : Fin n → C) :
    coefficients (C := C) b w = ∑ i, inl (w i) * inr (b i) := rfl

private theorem coefficients_base (a : Fin n → A) :
    coefficients (C := C) b (fun i => algebraMap A C (a i)) =
      inr (∑ i, algebraMap A B (a i) * b i) := by
  rw [coefficients_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  exact congrArg (· * inr (b i)) (RingHom.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := A) (A := C) (B := B)) (a i))

private theorem coefficients_surjective
    (hb : ∀ x : B, ∃ a : Fin n → A, ∑ i, algebraMap A B (a i) * b i = x) :
    Function.Surjective (coefficients (A := A) (C := C) b) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul c x =>
    obtain ⟨a, ha⟩ := hb x
    use c • (fun i => algebraMap A C (a i))
    rw [map_smul, coefficients_base, ha, Algebra.smul_def]
    change (c ⊗ₜ[A] (1 : B)) * ((1 : C) ⊗ₜ[A] x) = c ⊗ₜ[A] x
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  | add x y hx hy =>
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨w, rfl⟩ := hy
    exact ⟨u + w, map_add _ _ _⟩

private abbrev CoefficientQuotient := (Fin n → C) ⧸ (coefficients (A := A) (C := C) b).ker

private def coefficientClass (h : Function.Surjective (coefficients (A := A) (C := C) b)) :
    T ≃ₗ[C] CoefficientQuotient (A := A) (C := C) b :=
  ((coefficients (A := A) (C := C) b).quotKerEquivOfSurjective h).symm

private theorem coefficientClass_coefficients
    (h : Function.Surjective (coefficients (A := A) (C := C) b)) (w : Fin n → C) :
    coefficientClass b h (coefficients b w) = Submodule.Quotient.mk w := by
  apply (coefficientClass b h).symm.injective
  simp [coefficientClass]

private theorem coefficients_mul (s : Fin n → Fin n → Fin n → C)
    (hs : ∀ i j, coefficients b (s i j) = inr (b i) * inr (b j))
    (x y : Fin n → C) :
    coefficients (A := A) b x * coefficients b y =
      coefficients b (∑ i, ∑ j, (x i * y j) • s i j) := by
  simp only [map_sum, map_smul, hs]
  rw [coefficients_apply, coefficients_apply, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change (inl (x i) * inr (b i)) * (inl (y j) * inr (b j)) = _
  rw [Algebra.smul_def]
  change _ = inl (x i * y j) * (inr (b i) * inr (b j))
  rw [map_mul]
  ring

end Coefficients

section ScalarExtension

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B)

local notation "Aₗ" => algebra K L A
local notation "D" => algebra K L B

/-- The ordinary relative tensor product of the finite-map target with the
scalar-extended base, using the actual two ring maps out of `A`. -/
def relativeTensor : Type (max u v) :=
  letI := (iota K L A).toAlgHom.toRingHom.toAlgebra
  letI := f.toAlgHom.toRingHom.toAlgebra
  Aₗ ⊗[A] B

instance : CommRing (relativeTensor L f) := by
  letI := (iota K L A).toAlgHom.toRingHom.toAlgebra
  letI := f.toAlgHom.toRingHom.toAlgebra
  change CommRing (Aₗ ⊗[A] B)
  infer_instance

/-- Inclusion of the scalar-extended base in the ordinary relative tensor product. -/
def relativeTensorLeft : Aₗ →+* relativeTensor L f := by
  letI := (iota K L A).toAlgHom.toRingHom.toAlgebra
  letI := f.toAlgHom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeLeftRingHom

/-- Inclusion of the original finite algebra in the ordinary relative tensor product. -/
def relativeTensorRight : B →+* relativeTensor L f := by
  letI := (iota K L A).toAlgHom.toRingHom.toAlgebra
  letI := f.toAlgHom.toRingHom.toAlgebra
  exact Algebra.TensorProduct.includeRight.toRingHom

omit [CompleteSpace L] in
private theorem relativeTensorRight_base (a : A) :
    relativeTensorRight L f (f a) = relativeTensorLeft L f (iota K L A a) := by
  let := (iota K L A).toAlgHom.toRingHom.toAlgebra
  let := f.toAlgHom.toRingHom.toAlgebra
  exact (RingHom.congr_fun Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap a).symm

/-- The canonical algebraic comparison to the presented scalar extension.
It is induced by the extended map on the left and the original structural
inclusion on the right. -/
def relativeTensorComparison : relativeTensor L f →+* D := by
  letI := (iota K L A).toAlgHom.toRingHom.toAlgebra
  letI := f.toAlgHom.toRingHom.toAlgebra
  letI := ((iota K L B).comp f).toAlgHom.toRingHom.toAlgebra
  let left : Aₗ →ₐ[A] D := { (map K L f).toAlgHom.toRingHom with
    commutes' := map_iota (K := K) (L := L) f }
  let right : B →ₐ[A] D := { (iota K L B).toAlgHom.toRingHom with commutes' := fun _ => rfl }
  exact (Algebra.TensorProduct.lift left right (fun _ _ => Commute.all _ _)).toRingHom

@[simp]
theorem relativeTensorComparison_left (x : Aₗ) :
    relativeTensorComparison L f (relativeTensorLeft L f x) = map K L f x := by
  change map K L f x * iota K L B 1 = _
  rw [map_one, mul_one]

@[simp]
theorem relativeTensorComparison_right (x : B) :
    relativeTensorComparison L f (relativeTensorRight L f x) = iota K L B x := by
  change map K L f 1 * iota K L B x = _
  rw [map_one, one_mul]

omit [CompleteSpace L] in
private theorem relativeTensor_induction {motive : relativeTensor L f → Prop}
    (t : relativeTensor L f)
    (tmul : ∀ x y, motive (relativeTensorLeft L f x * relativeTensorRight L f y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive t := by
  let := (iota K L A).toAlgHom.toRingHom.toAlgebra
  let := f.toAlgHom.toRingHom.toAlgebra
  change Aₗ ⊗[A] B at t
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
    have h : (x ⊗ₜ[A] y : Aₗ ⊗[A] B) = relativeTensorLeft L f x * relativeTensorRight L f y := by
      change _ = (x ⊗ₜ[A] (1 : B)) * ((1 : Aₗ) ⊗ₜ[A] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [h]
    exact tmul x y
  | add x y hx hy => exact add x y hx hy

private theorem comparison_and_finite (hf : f.IsFiniteBanach) :
    Function.Bijective (relativeTensorComparison L f) ∧ (map K L f).IsFiniteBanach := by
  classical
  obtain ⟨n, b, M, hM, hb⟩ := hf
  let := (iota K L A).toAlgHom.toRingHom.toAlgebra
  let := f.toAlgHom.toRingHom.toAlgebra
  let T := Aₗ ⊗[A] B
  let p : (Fin n → Aₗ) →ₗ[Aₗ] T := coefficients (A := A) b
  have hp : Function.Surjective p := coefficients_surjective (A := A) (C := Aₗ) b
    (fun x => (hb x).imp fun _ h => h.1)
  let Q := (Fin n → Aₗ) ⧸ p.ker
  let e : T ≃ₗ[Aₗ] Q := coefficientClass b hp
  have hm (w : Fin n → Aₗ) : e (p w) = Submodule.Quotient.mk w :=
    coefficientClass_coefficients b hp w
  have hreps {t : T} {w : Fin n → Aₗ} (h : Submodule.Quotient.mk w = e t) : p w = t :=
    e.injective ((hm w).trans h)
  let : IsClosed (p.ker : Set (Fin n → Aₗ)) := isClosed_submodule_pi Aₗ _
  let : IsUltrametricDist Q := isUltrametricDist_submoduleQuotient _
  let l := relativeTensorLeft L f
  let r := relativeTensorRight L f
  let τ := relativeTensorComparison L f
  choose s hs using fun ij : Fin n × Fin n => hp (r (b ij.1) * r (b ij.2))
  let D₀ : ℝ := (∑ ij, ‖s ij‖) + 1
  have hD : 0 < D₀ := by dsimp [D₀]; positivity
  have hsn (i j : Fin n) : ‖s (i, j)‖ ≤ D₀ :=
    (Finset.single_le_sum (fun ij _ => norm_nonneg (s ij)) (Finset.mem_univ (i, j))).trans
      (le_add_of_nonneg_right zero_le_one)
  have hmul (x y : T) : ‖e (x * y)‖ ≤ D₀ * (‖e x‖ * ‖e y‖) := by
    apply le_mul_norm_mul_norm_quotient_of_forall_mk _ _ hD.le
    intro w w' hw hw'
    rw [← hreps hw, ← hreps hw']
    rw [show p w * p w' = p (∑ i, ∑ j, (w i * w' j) • s (i, j)) from
      coefficients_mul b (fun i j => s (i, j)) (fun i j => hs (i, j)) w w', hm]
    refine (Submodule.Quotient.norm_mk_le _ _).trans ?_
    have h₀ : 0 ≤ D₀ * (‖w‖ * ‖w'‖) := by positivity
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h₀
    intro i _
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h₀
    intro j _
    calc
      ‖(w i * w' j) • s (i, j)‖ ≤ ‖w i * w' j‖ * ‖s (i, j)‖ := norm_smul_le _ _
      _ ≤ (‖w‖ * ‖w'‖) * D₀ := by
        exact mul_le_mul ((norm_mul_le _ _).trans
          (mul_le_mul (norm_le_pi_norm w i) (norm_le_pi_norm w' j) (norm_nonneg _) (norm_nonneg _)))
          (hsn i j) (norm_nonneg _) (by positivity)
      _ = _ := mul_comm _ _
  have hl (x : Aₗ) : ‖e (l x)‖ ≤ ‖x‖ * ‖e 1‖ := by
    have hx : l x = x • (1 : T) := by
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [hx, map_smul]
    apply le_mul_norm_quotient_of_forall_mk _ (norm_nonneg x)
    intro w hw
    rw [← hw, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_smul_le _ _)
  have hr (y : B) : ‖e (r y)‖ ≤ M * ‖y‖ := by
    obtain ⟨a, ha, han⟩ := hb y
    have hc : p (fun i => iota K L A (a i)) = r y :=
      (coefficients_base (C := Aₗ) b a).trans (congrArg r ha)
    rw [← hc, hm]
    refine ((Submodule.Quotient.norm_mk_le _ _).trans ?_).trans han
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr fun i =>
      (norm_iota_le K L A (a i)).trans (norm_le_pi_norm a i)
  obtain ⟨F, hF, hfn⟩ := (map K L f).bounded
  let N : ℝ := ∑ i, ‖iota K L B (b i)‖
  have hN : 0 ≤ N := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hτ (t : T) : ‖τ t‖ ≤ (F * N) * ‖e t‖ := by
    apply le_mul_norm_quotient_of_forall_mk _ (mul_nonneg hF.le hN)
    intro w hw
    rw [← hreps hw]
    change ‖τ (∑ i, l (w i) * r (b i))‖ ≤ _
    simp only [map_sum, map_mul, relativeTensorComparison_left, relativeTensorComparison_right, τ, l, r]
    calc
      _ ≤ ∑ i, ‖map K L f (w i) * iota K L B (b i)‖ := norm_sum_le _ _
      _ ≤ ∑ i, F * ‖w‖ * ‖iota K L B (b i)‖ := Finset.sum_le_sum fun i _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((hfn (w i)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm w i) hF.le)) (norm_nonneg _))
      _ = _ := by rw [← Finset.mul_sum]; ring
  let q : AddGroupNorm T :=
    { toFun := fun x => D₀ * ‖e x‖
      map_zero' := by simp
      add_le' x y := by
        rw [map_add, ← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hD.le
      neg' x := by rw [map_neg, norm_neg]
      eq_zero_of_map_eq_zero' x hx := by
        apply e.injective
        rw [map_zero]
        exact norm_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hD.ne') }
  let nG := q.toNormedAddCommGroup
  let nR : NormedCommRing T :=
    { nG, (inferInstance : CommRing T) with
      norm_mul_le := fun x y => by
        change D₀ * ‖e (x * y)‖ ≤ (D₀ * ‖e x‖) * (D₀ * ‖e y‖)
        calc
          _ ≤ D₀ * (D₀ * (‖e x‖ * ‖e y‖)) := mul_le_mul_of_nonneg_left (hmul x y) hD.le
          _ = _ := by ring }
  have hn (x : T) : ‖x‖ = D₀ * ‖e x‖ := rfl
  let : IsUltrametricDist T := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    fun x y => by
      simp only [hn, map_add, ← mul_max_of_nonneg _ _ hD.le]
      exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max _ _) hD.le
  let : CompleteSpace T := by
    let E := e.toEquiv
    have ha : AntilipschitzWith ⟨D₀, hD.le⟩ E :=
      AntilipschitzWith.of_le_mul_dist fun x y => by
        change dist x y ≤ D₀ * dist (e x) (e y)
        rw [dist_eq_norm, dist_eq_norm, ← map_sub, hn]
    have hb : LipschitzWith ⟨1 / D₀, by positivity⟩ E :=
      LipschitzWith.of_dist_le_mul fun x y => by
        change dist (e x) (e y) ≤ (1 / D₀) * dist x y
        rw [dist_eq_norm, dist_eq_norm, ← map_sub, hn]
        exact le_of_eq (by field_simp)
    rw [completeSpace_iff_isComplete_range (ha.isUniformInducing hb.uniformContinuous), E.surjective.range_eq]
    exact isComplete_univ
  let : NormedAlgebra L T :=
    { (inferInstance : Algebra L T) with
      norm_smul_le := fun k x => by
        have hk : k • x = (algebraMap L Aₗ k) • x := by
          rw [Algebra.smul_def k, Algebra.smul_def (algebraMap L Aₗ k)]
          rfl
        rw [hn, hn, hk, map_smul, algebraMap_smul Aₗ k (e x)]
        calc
          _ ≤ D₀ * (‖k‖ * ‖e x‖) := mul_le_mul_of_nonneg_left (norm_smul_le k (e x)) hD.le
          _ = _ := by ring }
  let : IsScalarTower K L T := TensorProduct.isScalarTower_left
  let : NormedAlgebra K T :=
    { (inferInstance : Algebra K T) with
      norm_smul_le := fun k x => by
        rw [← algebraMap_smul L k x, ← norm_algebraMap' L k]
        exact norm_smul_le _ _ }
  let r₀ : BoundedAlgHom K B T :=
    { toRingHom := r
      commutes' := fun k => by
        change r (algebraMap K B k) = l (algebraMap L Aₗ (algebraMap K L k))
        rw [← f.toAlgHom.commutes k, relativeTensorRight_base, (iota K L A).toAlgHom.commutes]
        rfl
      bounded := ⟨D₀ * M, mul_pos hD hM, fun x => by
        change D₀ * ‖e (r x)‖ ≤ _
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hr x) hD.le⟩ }
  let j := lift K L B T r₀
  have hjr (x : B) : j (iota K L B x) = r x := lift_iota K L B T r₀ x
  have hjl (x : Aₗ) : j (map K L f x) = l x := by
    let l₀ : BoundedAlgHom L Aₗ T :=
      { toRingHom := l
        commutes' := fun _ => rfl
        bounded := ⟨D₀ * ‖e 1‖ + 1, by positivity, fun x => by
          change D₀ * ‖e (l x)‖ ≤ _
          calc
            _ ≤ D₀ * (‖x‖ * ‖e 1‖) := mul_le_mul_of_nonneg_left (hl x) hD.le
            _ ≤ _ := by nlinarith [norm_nonneg x]⟩ }
    have heq : j.comp (map K L f) = l₀ := by
      apply hom_ext K L A
      ext a
      change j (map K L f (iota K L A a)) = l (iota K L A a)
      rw [map_iota, hjr, relativeTensorRight_base]
    exact congrArg (fun h : BoundedAlgHom L Aₗ T => h x) heq
  have hcomp (t : T) : j (τ t) = t := by
    induction t using relativeTensor_induction L f with
    | tmul x y =>
      simp only [τ, map_mul, relativeTensorComparison_left, relativeTensorComparison_right, hjr, hjl]
      rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
      rfl
  let τ₀ : BoundedAlgHom L T (algebra K L B) :=
    { toRingHom := τ
      commutes' := fun c => by
        change τ (l (algebraMap L Aₗ c)) = _
        exact (relativeTensorComparison_left L f _).trans ((map K L f).toAlgHom.commutes c)
      bounded := ⟨(F * N + 1) / D₀, div_pos (by positivity) hD, fun x => by
        change ‖τ x‖ ≤ _
        rw [hn]
        calc
          _ ≤ (F * N) * ‖e x‖ := hτ x
          _ ≤ (F * N + 1) * ‖e x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
          _ = _ := by field_simp⟩ }
  have hback : τ₀.comp j = BoundedAlgHom.id L (algebra K L B) := by
    apply hom_ext K L B
    ext x
    change τ (j (iota K L B x)) = iota K L B x
    rw [hjr]
    exact relativeTensorComparison_right L f x
  have hyback (y : D) : τ (j y) = y :=
    congrArg (fun h : BoundedAlgHom L D D => h y) hback
  refine ⟨⟨Function.LeftInverse.injective hcomp, fun y => ⟨j y, hyback y⟩⟩, ?_⟩
  obtain ⟨J, hJ, hj⟩ := j.bounded
  let M' := J / D₀
  have hM' : 0 < M' := div_pos hJ hD
  refine ⟨n, fun i => iota K L B (b i), 2 * M', by positivity, fun y => ?_⟩
  by_cases hy : y = 0
  · subst y
    exact ⟨0, map_zero _, by simp⟩
  have hq : ‖e (j y)‖ ≤ M' * ‖y‖ := by
    have h := hj y
    change ‖j y‖ ≤ J * ‖y‖ at h
    rw [hn] at h
    rw [show M' * ‖y‖ = (J * ‖y‖) / D₀ by dsimp [M']; ring, le_div_iff₀ hD, mul_comm]
    exact h
  obtain ⟨w, hw, hwn⟩ := Submodule.Quotient.norm_mk_lt (e (j y))
    (mul_pos hM' (norm_pos_iff.mpr hy))
  refine ⟨w, ?_, ?_⟩
  · have heq : τ (p w) = (map K L f).coefficientMap (fun i => iota K L B (b i)) w := by
      change τ (∑ i, l (w i) * r (b i)) = _
      simp only [τ, l, r, map_sum, map_mul, relativeTensorComparison_left,
        relativeTensorComparison_right, BoundedAlgHom.coefficientMap_apply]
    rw [← heq, hreps hw, hyback]
  · calc
      ‖w‖ ≤ ‖e (j y)‖ + M' * ‖y‖ := hwn.le
      _ ≤ M' * ‖y‖ + M' * ‖y‖ := add_le_add hq le_rfl
      _ = 2 * M' * ‖y‖ := by ring

/-- The ordinary relative tensor comparison of a finite Banach map is bijective.
Its proof equips the ordinary tensor product with a complete quotient norm. -/
theorem relativeTensorComparison_bijective (hf : f.IsFiniteBanach) :
    Function.Bijective (relativeTensorComparison L f) :=
  (comparison_and_finite L f hf).1

/-- The canonical ring equivalence identifies the scalar extension of the
finite algebra with its ordinary relative base change. -/
def relativeTensorEquiv (hf : f.IsFiniteBanach) : relativeTensor L f ≃+* D :=
  RingEquiv.ofBijective (relativeTensorComparison L f) (relativeTensorComparison_bijective L f hf)

/-- Ground field extension preserves the bounded lifting condition for finite
Banach maps, with the images of the original generators. -/
theorem map_isFiniteBanach (hf : f.IsFiniteBanach) : (map K L f).IsFiniteBanach :=
  (comparison_and_finite L f hf).2

/-- The extended map of a finite Banach, algebraically finite étale map is
algebraically finite étale. The ring equivalence identifies this with ordinary
algebraic base change over the scalar-extended base algebra. -/
theorem map_algebraicallyFiniteEtale (hf : f.IsFiniteBanach) (he : f.AlgebraicallyFiniteEtale) :
    (map K L f).AlgebraicallyFiniteEtale := by
  refine ⟨(map_isFiniteBanach L f hf).finite, ?_⟩
  let := (iota K L A).toAlgHom.toRingHom.toAlgebra
  let := f.toAlgHom.toRingHom.toAlgebra
  let := (map K L f).toAlgHom.toRingHom.toAlgebra
  let : Algebra.Etale A B := he.2
  let e : (Aₗ ⊗[A] B) ≃ₐ[Aₗ] D :=
    { relativeTensorEquiv L f hf with
      commutes' := relativeTensorComparison_left L f }
  exact Algebra.Etale.of_equiv e

end ScalarExtension

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension
