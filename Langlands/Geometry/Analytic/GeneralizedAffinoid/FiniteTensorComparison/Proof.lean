import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Statement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.ClosedSubmodules
import Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalTensorComparisonProof
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # Finite Banach ordinary tensor comparison -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout

private theorem mul_sum_fin {R : Type*} [CommRing R] {n : ℕ} (a : R) (b : Fin n → R) :
    a * ∑ k, b k = ∑ k, a * b k :=
  Finset.mul_sum _ _ _

private theorem sum_mul_sum_fin {R : Type*} [CommRing R] {n : ℕ} (a b : Fin n → R) :
    (∑ i, a i) * ∑ j, b j = ∑ i, ∑ j, a i * b j :=
  Finset.sum_mul_sum _ _ _ _

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A B C : PresentedAffinoidAlgebra K}
  (f : BoundedAlgHom K A B) (g : BoundedAlgHom K A C)
  {n : ℕ} (b : Fin n → B)

/-- The coefficient sum `w ↦ ∑ k, w k ⊗ b k` of a tuple in the second factor,
written with the actual factor maps. -/
def coefficientSum : (Fin n → C) →+ algebraicBaseChange f g where
  toFun w := ∑ k, tensorLeft f g (w k) * tensorRight f g (b k)
  map_zero' := by simp only [Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
  map_add' w w' := by simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem coefficientSum_apply (w : Fin n → C) :
    coefficientSum f g b w = ∑ k, tensorLeft f g (w k) * tensorRight f g (b k) :=
  rfl

theorem coefficientSum_smul (x : C) (w : Fin n → C) :
    coefficientSum f g b (x • w) = tensorLeft f g x * coefficientSum f g b w := by
  rw [coefficientSum_apply, coefficientSum_apply, mul_sum_fin]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]

/-- Coefficients from the original base give the right factor of their sum. -/
theorem coefficientSum_baseMap (a : Fin n → A) :
    coefficientSum f g b (fun k => g (a k)) =
      tensorRight f g (f.coefficientMap b a) := by
  rw [coefficientSum_apply, BoundedAlgHom.coefficientMap_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, tensorRight_apply_map]

/-- A generating tuple of the finite map generates the ordinary tensor product
over its left factor. -/
theorem coefficientSum_surjective (hc : Function.Surjective (f.coefficientMap b)) :
    Function.Surjective (coefficientSum f g b) := by
  intro m
  induction m using algebraicBaseChange_induction f g with
  | mul x y =>
    obtain ⟨a, rfl⟩ := hc y
    exact ⟨x • fun k => g (a k), by
      rw [coefficientSum_smul, coefficientSum_baseMap]⟩
  | add m m' hm hm' =>
    obtain ⟨w, rfl⟩ := hm
    obtain ⟨w', rfl⟩ := hm'
    exact ⟨w + w', map_add _ _ _⟩

/-- Products of coefficient sums, given coefficients `s i j` for the products
of the generators. -/
theorem coefficientSum_mul (s : Fin n → Fin n → Fin n → C)
    (hs : ∀ i j, coefficientSum f g b (s i j) =
      tensorRight f g (b i) * tensorRight f g (b j))
    (u w : Fin n → C) :
    coefficientSum f g b u * coefficientSum f g b w =
      coefficientSum f g b (∑ i, ∑ j, (u i * w j) • s i j) := by
  simp only [map_sum, coefficientSum_smul, hs]
  rw [coefficientSum_apply, coefficientSum_apply, sum_mul_sum_fin]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

/-- The kernel of the coefficient sum, as a submodule over the left factor. -/
def coefficientKernel : Submodule C (Fin n → C) where
  carrier := {w | coefficientSum f g b w = 0}
  add_mem' {w w'} hw hw' := by
    change coefficientSum f g b (w + w') = 0
    rw [map_add, hw, hw', add_zero]
  zero_mem' := map_zero _
  smul_mem' x w hw := by
    change coefficientSum f g b (x • w) = 0
    rw [coefficientSum_smul, hw, mul_zero]

theorem mem_coefficientKernel {w : Fin n → C} :
    w ∈ coefficientKernel f g b ↔ coefficientSum f g b w = 0 :=
  Iff.rfl

/-- The quotient of coefficient tuples by the kernel of the coefficient sum. -/
abbrev CoefficientQuotient := (Fin n → C) ⧸ coefficientKernel f g b

theorem coefficientQuotient_mk_eq_mk_iff {w w' : Fin n → C} :
    (Submodule.Quotient.mk w : CoefficientQuotient f g b) = Submodule.Quotient.mk w' ↔
      coefficientSum f g b w = coefficientSum f g b w' := by
  rw [Submodule.Quotient.eq, mem_coefficientKernel, map_sub, sub_eq_zero]

variable (hsurj : Function.Surjective (coefficientSum f g b))

/-- The additive identification of the ordinary tensor product with the
coefficient quotient, given by any choice of coefficients. -/
def coefficientSection : algebraicBaseChange f g →+ CoefficientQuotient f g b where
  toFun m := Submodule.Quotient.mk (Function.surjInv hsurj m)
  map_zero' := by
    rw [← Submodule.Quotient.mk_zero, coefficientQuotient_mk_eq_mk_iff,
      Function.surjInv_eq hsurj, map_zero]
  map_add' m m' := by
    rw [← Submodule.Quotient.mk_add, coefficientQuotient_mk_eq_mk_iff, map_add,
      Function.surjInv_eq hsurj, Function.surjInv_eq hsurj, Function.surjInv_eq hsurj]

theorem coefficientSection_eq_mk_iff (m : algebraicBaseChange f g) (w : Fin n → C) :
    coefficientSection f g b hsurj m = Submodule.Quotient.mk w ↔
      m = coefficientSum f g b w := by
  change Submodule.Quotient.mk _ = _ ↔ _
  rw [coefficientQuotient_mk_eq_mk_iff, Function.surjInv_eq hsurj]

theorem coefficientSection_coefficientSum (w : Fin n → C) :
    coefficientSection f g b hsurj (coefficientSum f g b w) = Submodule.Quotient.mk w :=
  (coefficientSection_eq_mk_iff f g b hsurj _ w).mpr rfl

theorem coefficientSection_bijective :
    Function.Bijective (coefficientSection f g b hsurj) := by
  constructor
  · intro m m' h
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (coefficientSection f g b hsurj m')
    rw [← hw] at h
    rw [(coefficientSection_eq_mk_iff f g b hsurj m w).mp h,
      (coefficientSection_eq_mk_iff f g b hsurj m' w).mp hw.symm]
  · intro v
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    exact ⟨_, coefficientSection_coefficientSum f g b hsurj w⟩

theorem coefficientSection_tensorLeft_mul (x : C) (m : algebraicBaseChange f g) :
    coefficientSection f g b hsurj (tensorLeft f g x * m) =
      x • coefficientSection f g b hsurj m := by
  obtain ⟨w, rfl⟩ := hsurj m
  rw [← coefficientSum_smul, coefficientSection_coefficientSum,
    coefficientSection_coefficientSum, Submodule.Quotient.mk_smul]

theorem coefficientSection_algebraMap_mul (k : K) (m : algebraicBaseChange f g) :
    coefficientSection f g b hsurj (tensorLeft f g (algebraMap K C k) * m) =
      k • coefficientSection f g b hsurj m := by
  rw [coefficientSection_tensorLeft_mul, algebraMap_smul]

omit hsurj in
/-- The left factor acts boundedly on the coefficient quotient. -/
theorem norm_smul_coefficientQuotient_le (x : C) (v : CoefficientQuotient f g b) :
    ‖x • v‖ ≤ ‖x‖ * ‖v‖ :=
  le_mul_norm_quotient_of_forall_mk v (norm_nonneg x) fun w hw => by
    rw [← hw, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_smul_le x w)

omit hsurj in
/-- Scalars act boundedly on the coefficient quotient. -/
theorem norm_scalar_smul_coefficientQuotient_le (k : K) (v : CoefficientQuotient f g b) :
    ‖k • v‖ ≤ ‖k‖ * ‖v‖ :=
  le_mul_norm_quotient_of_forall_mk v (norm_nonneg k) fun w hw => by
    rw [← hw, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_smul_le k w)

/-- The quotient seminorm is submultiplicative up to the bound `D` on the
coefficients of the products of the generators. -/
theorem norm_coefficientSection_mul_le (s : Fin n → Fin n → Fin n → C)
    (hs : ∀ i j, coefficientSum f g b (s i j) =
      tensorRight f g (b i) * tensorRight f g (b j))
    (D : ℝ) (hD : 0 ≤ D) (hsn : ∀ i j, ‖s i j‖ ≤ D) (x y : algebraicBaseChange f g) :
    ‖coefficientSection f g b hsurj (x * y)‖ ≤
      D * (‖coefficientSection f g b hsurj x‖ * ‖coefficientSection f g b hsurj y‖) := by
  apply le_mul_norm_mul_norm_quotient_of_forall_mk _ _ hD
  intro u w hu hw
  rw [(coefficientSection_eq_mk_iff f g b hsurj x u).mp hu.symm,
    (coefficientSection_eq_mk_iff f g b hsurj y w).mp hw.symm,
    coefficientSum_mul f g b s hs, coefficientSection_coefficientSum]
  refine (Submodule.Quotient.norm_mk_le _ _).trans ?_
  have h0 : 0 ≤ D * (‖u‖ * ‖w‖) := by positivity
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0
  intro i _
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0
  intro j _
  calc
    ‖(u i * w j) • s i j‖ ≤ ‖u i * w j‖ * ‖s i j‖ := norm_smul_le _ _
    _ ≤ (‖u i‖ * ‖w j‖) * D :=
      mul_le_mul (norm_mul_le _ _) (hsn i j) (norm_nonneg _) (by positivity)
    _ ≤ (‖u‖ * ‖w‖) * D := by
      gcongr
      · exact norm_le_pi_norm u i
      · exact norm_le_pi_norm w j
    _ = _ := by ring

/-- The left factor is bounded for the quotient seminorm. -/
theorem norm_coefficientSection_tensorLeft_le (x : C) :
    ‖coefficientSection f g b hsurj (tensorLeft f g x)‖ ≤
      ‖coefficientSection f g b hsurj 1‖ * ‖x‖ := by
  rw [← mul_one (tensorLeft f g x), coefficientSection_tensorLeft_mul, mul_comm]
  exact norm_smul_coefficientQuotient_le f g b x _

/-- Bounded coefficient lifts make the right factor bounded for the quotient
seminorm. -/
theorem exists_norm_coefficientSection_tensorRight_le
    (hlift : ∃ D > 0, ∀ q : B, ∃ a : Fin n → A, f.coefficientMap b a = q ∧ ‖a‖ ≤ D * ‖q‖) :
    ∃ C > 0, ∀ q : B, ‖coefficientSection f g b hsurj (tensorRight f g q)‖ ≤ C * ‖q‖ := by
  obtain ⟨D, hD, hlift⟩ := hlift
  obtain ⟨Cβ, hCβ, hβ⟩ := g.bounded
  refine ⟨Cβ * D, by positivity, fun q => ?_⟩
  obtain ⟨a, rfl, han⟩ := hlift q
  rw [← coefficientSum_baseMap, coefficientSection_coefficientSum]
  have hpi : ‖(fun k => g (a k))‖ ≤ Cβ * ‖a‖ :=
    (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k =>
      (hβ (a k)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm a k) hCβ.le)
  calc
    ‖(Submodule.Quotient.mk (fun k => g (a k)) : CoefficientQuotient f g b)‖ ≤
        Cβ * ‖a‖ := (Submodule.Quotient.norm_mk_le _ _).trans hpi
    _ ≤ Cβ * (D * ‖f.coefficientMap b a‖) := by gcongr
    _ = _ := by ring

/-- The comparison is bounded for the quotient seminorm. -/
theorem exists_norm_tensorComparison_le :
    ∃ C > 0, ∀ m : algebraicBaseChange f g,
      ‖tensorComparison f g m‖ ≤ C * ‖coefficientSection f g b hsurj m‖ := by
  obtain ⟨Cc, hCc, hcomp⟩ := (rightMap f g).bounded
  let Cb : ℝ := ∑ k, ‖(leftMap f g) (b k)‖
  have hCb : 0 ≤ Cb := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨Cc * Cb + 1, by positivity, fun m => ?_⟩
  have key : ‖tensorComparison f g m‖ ≤ (Cc * Cb) * ‖coefficientSection f g b hsurj m‖ := by
    apply le_mul_norm_quotient_of_forall_mk _ (by positivity)
    intro w hw
    rw [(coefficientSection_eq_mk_iff f g b hsurj m w).mp hw.symm, coefficientSum_apply,
      map_sum]
    calc
      ‖∑ k, tensorComparison f g (tensorLeft f g (w k) * tensorRight f g (b k))‖ ≤
          ∑ k, ‖tensorComparison f g (tensorLeft f g (w k) * tensorRight f g (b k))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k, Cc * ‖w‖ * ‖(leftMap f g) (b k)‖ :=
        Finset.sum_le_sum fun k _ => by
          rw [tensorComparison_mul]
          exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            ((hcomp (w k)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm w k) hCc.le))
            (norm_nonneg _))
      _ = Cc * ‖w‖ * Cb := (Finset.mul_sum _ _ _).symm
      _ = Cc * Cb * ‖w‖ := by ring
  exact key.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
    (norm_nonneg _))

variable [CompleteSpace K]

omit hsurj in
/-- A positive real multiple of the coefficient quotient norm gives a complete
ultrametric normed algebra model, with no restriction on the scalar valuation. -/
theorem bijective_tensorComparison_of_generators
    (hlift : ∃ D > 0, ∀ q : B, ∃ a : Fin n → A,
      f.coefficientMap b a = q ∧ ‖a‖ ≤ D * ‖q‖)
    (D : ℝ) (hD : 0 < D)
    (hstruct : ∀ i j, ∃ s : Fin n → C,
      coefficientSum f g b s = tensorRight f g (b i) * tensorRight f g (b j) ∧
        ‖s‖ ≤ D) :
    Function.Bijective (tensorComparison f g) := by
  classical
  have hsurj : Function.Surjective (coefficientSum f g b) := by
    obtain ⟨M, _, hl⟩ := hlift
    exact coefficientSum_surjective f g b fun q => (hl q).imp fun _ h => h.1
  choose s hs hsn using hstruct
  obtain ⟨Cr, hCr, hr⟩ := exists_norm_coefficientSection_tensorRight_le f g b hsurj hlift
  obtain ⟨Ct, hCt, ht⟩ := exists_norm_tensorComparison_le f g b hsurj
  have hm := norm_coefficientSection_mul_le f g b hsurj s hs D hD.le hsn
  have hl := norm_coefficientSection_tensorLeft_le f g b hsurj
  have hK := coefficientSection_algebraMap_mul f g b hsurj
  have hnK := norm_scalar_smul_coefficientQuotient_le f g b
  have : IsClosed (coefficientKernel f g b : Set (Fin n → C)) :=
    PresentedAffinoidAlgebra.isClosed_submodule_pi C _
  have : IsUltrametricDist (CoefficientQuotient f g b) :=
    isUltrametricDist_submoduleQuotient _
  let γ := coefficientSection f g b hsurj
  have hγ := coefficientSection_bijective f g b hsurj
  let e : algebraicBaseChange f g ≃+ CoefficientQuotient f g b :=
    AddEquiv.ofBijective γ hγ
  let p : AddGroupNorm (algebraicBaseChange f g) :=
    { toFun := fun m => D * ‖γ m‖
      map_zero' := by simp only [map_zero, norm_zero, mul_zero]
      add_le' := fun x y => by
        rw [map_add, ← mul_add]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hD.le
      neg' := fun x => by rw [map_neg, norm_neg]
      eq_zero_of_map_eq_zero' := fun x hx => by
        apply hγ.1
        rw [map_zero]
        exact norm_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hD.ne') }
  let nG : NormedAddCommGroup (algebraicBaseChange f g) := p.toNormedAddCommGroup
  have hnorm : ∀ m : algebraicBaseChange f g, ‖m‖ = D * ‖γ m‖ := fun _ => rfl
  have hmul : ∀ x y : algebraicBaseChange f g, ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
    intro x y
    rw [hnorm, hnorm, hnorm]
    calc
      D * ‖γ (x * y)‖ ≤ D * (D * (‖γ x‖ * ‖γ y‖)) :=
        mul_le_mul_of_nonneg_left (hm x y) hD.le
      _ = D * ‖γ x‖ * (D * ‖γ y‖) := by ring
  let nR : NormedCommRing (algebraicBaseChange f g) :=
    { nG, (inferInstance : CommRing (algebraicBaseChange f g)) with
      norm_mul_le := hmul }
  let alg : Algebra K (algebraicBaseChange f g) :=
    ((tensorLeft f g).comp (algebraMap K C)).toAlgebra
  let : NormedAlgebra K (algebraicBaseChange f g) :=
    { alg with
      norm_smul_le := fun k m => by
        change ‖tensorLeft f g (algebraMap K C k) * m‖ ≤ ‖k‖ * ‖m‖
        rw [hnorm, hnorm, hK]
        calc
          D * ‖k • γ m‖ ≤ D * (‖k‖ * ‖γ m‖) :=
            mul_le_mul_of_nonneg_left (hnK k _) hD.le
          _ = ‖k‖ * (D * ‖γ m‖) := by ring }
  let : IsUltrametricDist (algebraicBaseChange f g) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
      rw [hnorm, hnorm, hnorm, map_add, ← mul_max_of_nonneg _ _ hD.le]
      exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max _ _) hD.le
  have : CompleteSpace (algebraicBaseChange f g) := by
    have hanti : AntilipschitzWith ⟨D, hD.le⟩ e :=
      AntilipschitzWith.of_le_mul_dist fun x y => by
        simp only [dist_eq_norm, ← map_sub]
        exact (hnorm (x - y)).le
    have hlip : LipschitzWith ⟨1 / D, by positivity⟩ e :=
      LipschitzWith.of_dist_le_mul fun x y => by
        simp only [dist_eq_norm, ← map_sub]
        change ‖γ (x - y)‖ ≤ (1 / D) * ‖x - y‖
        rw [hnorm]
        exact le_of_eq (by field_simp)
    rw [completeSpace_iff_isComplete_range (hanti.isUniformInducing hlip.uniformContinuous),
      e.surjective.range_eq]
    exact isComplete_univ
  refine bijective_tensorComparison_of_normedModel f g (RingEquiv.refl _) (fun _ => rfl)
    ⟨D * ‖γ 1‖ + 1, by positivity, fun x => ?_⟩ ⟨D * Cr, by positivity, fun y => ?_⟩
    ⟨Ct / D, by positivity, fun z => ?_⟩
  · change ‖tensorLeft f g x‖ ≤ _
    rw [hnorm]
    calc
      D * ‖γ (tensorLeft f g x)‖ ≤ D * (‖γ 1‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hl x) hD.le
      _ ≤ (D * ‖γ 1‖ + 1) * ‖x‖ := by nlinarith [norm_nonneg x]
  · change ‖tensorRight f g y‖ ≤ _
    rw [hnorm]
    calc
      D * ‖γ (tensorRight f g y)‖ ≤ D * (Cr * ‖y‖) :=
        mul_le_mul_of_nonneg_left (hr y) hD.le
      _ = D * Cr * ‖y‖ := by ring
  · change ‖tensorComparison f g z‖ ≤ _
    rw [hnorm]
    calc
      ‖tensorComparison f g z‖ ≤ Ct * ‖γ z‖ := ht z
      _ = Ct / D * (D * ‖γ z‖) := by field_simp

include hsurj in
omit [CompleteSpace K] in
/-- Finitely many product coefficients admit a common positive real bound,
including rank zero and trivially valued coefficient fields. -/
theorem exists_structure_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ i j, ∃ s : Fin n → C,
      coefficientSum f g b s = tensorRight f g (b i) * tensorRight f g (b j) ∧
        ‖s‖ ≤ D := by
  classical
  choose s hs using fun ij : Fin n × Fin n =>
    hsurj (tensorRight f g (b ij.1) * tensorRight f g (b ij.2))
  let D := (∑ ij, ‖s ij‖) + 1
  have hsum : 0 ≤ ∑ ij, ‖s ij‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨D, by dsimp [D]; linarith, fun i j => ⟨s (i, j), hs (i, j), ?_⟩⟩
  exact (Finset.single_le_sum (fun ij _ => norm_nonneg (s ij))
    (Finset.mem_univ (i, j))).trans (by dsimp [D]; linarith)

omit b hsurj in
/-- The canonical ordinary relative tensor map to the actual affinoid pushout
is bijective when the first map is finite Banach. -/
theorem tensorComparison_bijective (hf : f.IsFiniteBanach) :
    Function.Bijective (tensorComparison f g) := by
  obtain ⟨n, b, M, hM, hlift⟩ := hf
  have hsurj := coefficientSum_surjective f g b fun y => (hlift y).imp fun _ h => h.1
  obtain ⟨D, hD, hstruct⟩ := exists_structure_bound f g b hsurj
  exact bijective_tensorComparison_of_generators f g b ⟨M, hM, hlift⟩ D hD hstruct

omit f g b hsurj in
/-- Exact proof of the unrestricted finite Banach tensor comparison. -/
theorem finiteTensorComparison : FiniteTensorComparisonStatement (K := K) := by
  intro A B C f g hf
  exact tensorComparison_bijective f g hf

end Langlands.Analytic.PresentedAffinoidAlgebra.AffinoidPushout
