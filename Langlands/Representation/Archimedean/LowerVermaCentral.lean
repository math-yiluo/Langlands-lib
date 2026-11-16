import Langlands.Representation.Archimedean.LowerVermaPBW
import Langlands.Representation.Archimedean.ComplexJacquetFinite
import Langlands.Representation.Archimedean.Kostant.OrbitVanishing
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.Algebra.MvPolynomial.Funext
import Langlands.Automorphic.AssociatedGammaTriangular
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Central characters of lower Verma modules of `𝔤𝔩_n(ℂ)`

See the paired Markdown.
-/

noncomputable section

set_option autoImplicit false

namespace Langlands.Archimedean.VermaCentral

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping MvPolynomial Kostant VermaPBW

variable (n : ℕ)

/-! ## The Harish-Chandra map -/

section HC

/-- `X_p` on the diagonal unit `E_pp`, `0` on the other matrix units. -/
def Xd (c : Idx n) : MvPolynomial (Fin n) ℂ := if c.1 = c.2 then X c.1 else 0

/-- The linear map `γ : U → ℂ[λ]` with `γ(E^α) = ∏ Xd(c)` over the letters `c` of `E^α`. -/
def gam : VermaGL.glU n →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  (basisU n).constr ℂ fun α => ((expand (bsList n) α).map (Xd n)).prod

theorem gam_basisU (α : Idx n →₀ ℕ) :
    gam n (basisU n α) = ((expand (bsList n) α).map (Xd n)).prod :=
  (basisU n).constr_basis ℂ _ α

theorem eval_Xd (lam : Fin n → ℂ) (c : Idx n) : eval lam (Xd n c) = vVal n lam 0 c := by
  obtain ⟨p, q⟩ := c
  unfold Xd
  rcases lt_trichotomy p q with h | rfl | h
  · rw [ite_eq_right h.ne, map_zero]
    simp [vVal, h, supCoeff]
  · rw [ite_eq_left rfl, eval_X, vVal_diag]
  · rw [ite_eq_right h.ne', map_zero, vVal_of_lt n lam 0 h]

/-- `γ(u)(λ) = Ψ_{λ,0}(u)`. -/
theorem eval_gam (lam : Fin n → ℂ) (u : VermaGL.glU n) :
    eval lam (gam n u) = Psi n (vVal n lam 0) u := by
  have h : (MvPolynomial.aeval lam).toLinearMap ∘ₗ gam n = Psi n (vVal n lam 0) := by
    refine (basisU n).ext fun α => ?_
    rw [LinearMap.comp_apply, gam_basisU, Psi_basisU, wt, AlgHom.toLinearMap_apply,
      map_list_prod, List.map_map]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    rw [Function.comp_apply, MvPolynomial.aeval_eq_eval, eval_Xd]
  have := LinearMap.congr_fun h u
  rwa [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.aeval_eq_eval] at this

/-- A central element acts on the generator of `M⁻(λ)` by the scalar `γ(z)(λ)`. -/
theorem center_smul_gen (z : VermaGL.center n) (lam : Fin n → ℂ) :
    (z : VermaGL.glU n) • VermaGL.gen n lam = eval lam (gam n z) • VermaGL.gen n lam := by
  have hz : ∀ g : VermaGL.glU n, g * z = z * g := Subalgebra.mem_center_iff.mp z.2
  obtain ⟨c, hc⟩ := (lowerVermaWeight n lam).2 ((z : VermaGL.glU n) • VermaGL.gen n lam)
    (fun p => by rw [smul_smul, hz, mul_smul, unitU_smul_gen, smul_comm])
  have hmem : (z : VermaGL.glU n) - algebraMap ℂ (VermaGL.glU n) c ∈
      VermaGL.lowerVermaIdeal n lam := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, mk_eq_smul_gen,
      mk_eq_smul_gen, hc, algebraMap_smul, sub_self]
  have h := Psi_mul_mem_lowerVermaIdeal n lam 0 hmem 1
  rw [one_mul, map_sub, Algebra.algebraMap_eq_smul_one, map_smul, Psi_one, smul_eq_mul, mul_one,
    sub_eq_zero] at h
  rw [eval_gam, h, hc]

theorem gam_one : gam n 1 = 1 := by
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_gam, Psi_one, map_one]

/-- The Harish-Chandra homomorphism `γ : Z(𝔤𝔩_n) → ℂ[λ]`. -/
def gamC : VermaGL.center n →ₐ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun z := gam n z
  map_one' := gam_one n
  map_mul' z w := by
    refine MvPolynomial.funext fun lam => ?_
    have h := center_smul_gen n (z * w) lam
    rw [Subalgebra.coe_mul, mul_smul, center_smul_gen n w, smul_comm, center_smul_gen n z,
      smul_smul] at h
    have h' := smul_left_injective ℂ (gen_ne_zero n lam) h
    show eval lam (gam n ((z : VermaGL.glU n) * w)) = eval lam (gam n z * gam n w)
    rw [RingHom.map_mul (eval lam), ← h', mul_comm]
  map_zero' := by simp
  map_add' z w := by simp
  commutes' c := by
    refine MvPolynomial.funext fun lam => ?_
    show eval lam (gam n (algebraMap ℂ (VermaGL.glU n) c)) = _
    rw [eval_gam, Algebra.algebraMap_eq_smul_one, map_smul, Psi_one, smul_eq_mul, mul_one,
      MvPolynomial.algebraMap_eq, eval_C]

theorem gamC_apply (z : VermaGL.center n) : gamC n z = gam n z := rfl

theorem eval_gamC_smul_gen (z : VermaGL.center n) (lam : Fin n → ℂ) :
    (z : VermaGL.glU n) • VermaGL.gen n lam = eval lam (gamC n z) • VermaGL.gen n lam :=
  center_smul_gen n z lam

end HC

/-! ## Gelfand's central elements -/

section Gelfand

/-- The matrix `(E_pq)` of generators of `U`. -/
def Gm : Matrix (Fin n) (Fin n) (VermaGL.glU n) := Matrix.of fun p q => VermaGL.unitU n p q

/-- Gelfand's element `C_k = ∑_p (E^k)_pp`. -/
def gel (k : ℕ) : VermaGL.glU n := ∑ p, (Gm n ^ k) p p

theorem unitU_comm (a b c d : Fin n) :
    VermaGL.unitU n a b * VermaGL.unitU n c d - VermaGL.unitU n c d * VermaGL.unitU n a b =
      (if b = c then VermaGL.unitU n a d else 0) - (if d = a then VermaGL.unitU n c b else 0) := by
  have h := (UniversalEnvelopingAlgebra.ι ℂ (L := Matrix (Fin n) (Fin n) ℂ)).map_lie
    (Matrix.single a b (1 : ℂ)) (Matrix.single c d 1)
  rw [Ring.lie_def, Ring.lie_def, map_sub] at h
  rw [← h]
  congr 1
  · by_cases hbc : b = c
    · subst hbc
      rw [Matrix.single_mul_single_same, mul_one, ite_eq_left rfl]
    · rw [Matrix.single_mul_single_of_ne (1 : ℂ) a b c hbc, ite_eq_right hbc, map_zero]
  · by_cases hda : d = a
    · subst hda
      rw [Matrix.single_mul_single_same, mul_one, ite_eq_left rfl]
    · rw [Matrix.single_mul_single_of_ne (1 : ℂ) c d a hda, ite_eq_right hda, map_zero]

/-- Left multiplications `v ↦ E_ab v`. -/
def eL (a b : Fin n) : Module.End ℂ (VermaGL.glU n) := LinearMap.mulLeft ℂ (VermaGL.unitU n a b)

theorem isGlFamily_eL : ComplexJacquetFinite.IsGlFamily (eL n) := by
  intro a b c d
  refine LinearMap.ext fun v => ?_
  have h := congrArg (· * v) (unitU_comm n a b c d)
  simp only [sub_mul, mul_assoc] at h
  simp only [eL, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulLeft_apply, h]
  clear h
  split_ifs <;> simp_all

theorem eL_pow_apply (k : ℕ) (x y : Fin n) (v : VermaGL.glU n) :
    (Matrix.of (eL n) ^ k) x y v = (Gm n ^ k) x y * v := by
  induction k generalizing x y v with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    rw [ComplexJacquetFinite.pow_succ_apply, LinearMap.sum_apply, pow_succ', Matrix.mul_apply,
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Module.End.mul_apply, ih, eL, LinearMap.mulLeft_apply, mul_assoc]
    rfl

theorem unitU_mul_gel (k : ℕ) (a c : Fin n) :
    VermaGL.unitU n a c * gel n k = gel n k * VermaGL.unitU n a c := by
  have h : ∀ x y, VermaGL.unitU n a c * (Gm n ^ k) x y - (Gm n ^ k) x y * VermaGL.unitU n a c =
      (if x = c then (Gm n ^ k) a y else 0) - (if a = y then (Gm n ^ k) x c else 0) := by
    intro x y
    have h1 := LinearMap.congr_fun (ComplexJacquetFinite.comm_pow (isGlFamily_eL n) k a c x y) 1
    rw [LinearMap.sub_apply, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply,
      eL_pow_apply, eL_pow_apply] at h1
    simp only [eL, LinearMap.mulLeft_apply, mul_one] at h1
    rw [h1]
    by_cases h2 : x = c <;> by_cases h3 : a = y <;> simp [h2, h3, eL_pow_apply]
  rw [← sub_eq_zero, gel, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, sub_self]

theorem gel_mem_center (k : ℕ) : gel n k ∈ VermaGL.center n := by
  refine Kostant.mem_center_of_commute ℂ (Matrix (Fin n) (Fin n) ℂ) fun Y => ?_
  have hY : Y = ∑ a, ∑ c, Y a c • Matrix.single a c (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hY]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [unitU_mul_gel]

/-- Right multiplications `v ↦ v E_ba`. -/
def eR (a b : Fin n) : Module.End ℂ (VermaGL.glU n) := LinearMap.mulRight ℂ (VermaGL.unitU n b a)

theorem isGlFamily_eR : ComplexJacquetFinite.IsGlFamily (eR n) := by
  intro a b c d
  refine LinearMap.ext fun v => ?_
  have h := congrArg (v * ·) (unitU_comm n d c b a)
  simp only [mul_sub, ← mul_assoc] at h
  simp only [eR, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.mulRight_apply, h]
  clear h
  split_ifs <;> simp_all

theorem eR_pow_apply (k : ℕ) (x y : Fin n) (v : VermaGL.glU n) :
    (Matrix.of (eR n) ^ k) x y v = v * (Gm n ^ k) y x := by
  induction k generalizing x y v with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; simp
  | succ k ih =>
    rw [ComplexJacquetFinite.pow_succ_apply, LinearMap.sum_apply, pow_succ, Matrix.mul_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Module.End.mul_apply, ih, eR, LinearMap.mulRight_apply, mul_assoc]
    rfl

/-- The diagonal right multiplications `v ↦ v E_aa`. -/
def dR (a : Fin n) : Module.End ℂ (VermaGL.glU n) := eR n a a

theorem dR_commute (a b : Fin n) : Commute (dR n a) (dR n b) := by
  have hab : VermaGL.unitU n b b * VermaGL.unitU n a a =
      VermaGL.unitU n a a * VermaGL.unitU n b b := by
    have := unitU_comm n b b a a
    rw [← sub_eq_zero, this]
    by_cases h : b = a
    · subst h; simp
    · simp [h, Ne.symm h]
  show dR n a * dR n b = dR n b * dR n a
  ext v
  simp only [dR, eR, Module.End.mul_apply, LinearMap.mulRight_apply, mul_assoc, hab]

/-- The commutative algebra generated by the `dR a`. -/
def dAlg : Subalgebra ℂ (Module.End ℂ (VermaGL.glU n)) := Algebra.adjoin ℂ (Set.range (dR n))

theorem dAlg_commute {x y : Module.End ℂ (VermaGL.glU n)} (hx : x ∈ dAlg n) (hy : y ∈ dAlg n) :
    Commute x y := by
  have hgen : ∀ a ∈ Set.range (dR n), ∀ b ∈ Set.range (dR n), Commute a b := by
    rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    exact dR_commute n s t
  have h1 : ∀ a ∈ Set.range (dR n), Commute a y := fun a ha =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb => hgen a ha b hb
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun b hb => (h1 b hb).symm).symm

instance dAlgCommRing : CommRing (dAlg n) :=
  { (inferInstance : Ring (dAlg n)) with
    mul_comm := fun x y => Subtype.ext (dAlg_commute n x.2 y.2).eq }

/-- Polynomials in the diagonal right multiplications, `X_a ↦ (v ↦ v E_aa)`. -/
def psiR : MvPolynomial (Fin n) ℂ →ₐ[ℂ] Module.End ℂ (VermaGL.glU n) :=
  (dAlg n).val.comp
    (MvPolynomial.aeval fun a => ⟨dR n a, Algebra.subset_adjoin (Set.mem_range_self a)⟩)

theorem psiR_X (a : Fin n) : psiR n (X a) = eR n a a := by
  simp [psiR, dR]

theorem Psi_psiR (lam : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) (v : VermaGL.glU n) :
    Psi n (vVal n lam 0) (psiR n f v) = eval lam f * Psi n (vVal n lam 0) v := by
  induction f using MvPolynomial.induction_on generalizing v with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, Module.algebraMap_end_apply, map_smul,
      MvPolynomial.algebraMap_eq, eval_C, smul_eq_mul]
  | add f g hf hg => rw [map_add, LinearMap.add_apply, map_add, hf, hg, map_add, add_mul]
  | mul_X f a hf =>
    have h := Psi_mul_unitE_lo n lam 0 ⟨(a, a), lt_irrefl a⟩ (psiR n f v)
    rw [vVal_diag] at h
    change Psi n (vVal n lam 0) (psiR n f v * VermaGL.unitU n a a) = lam a * _ at h
    rw [mul_comm f (X a), map_mul, Module.End.mul_apply, psiR_X, eR, LinearMap.mulRight_apply, h, hf,
      MvPolynomial.eval_mul, eval_X]
    ring

/-- `Ψ_{λ,0}(C_k) = ∑_a g_k(a)(λ)` (Gelfand's recursion). -/
theorem Psi_gel (lam : Fin n → ℂ) (k : ℕ) :
    Psi n (vVal n lam 0) (gel n k) = eval lam (∑ a, ComplexJacquetFinite.gelPoly n k a) := by
  have hup : ∀ a b : Fin n, a < b → ∀ v, eR n a b v ∈ LinearMap.ker (Psi n (vVal n lam 0)) := by
    intro a b hab v
    rw [LinearMap.mem_ker, eR, LinearMap.mulRight_apply]
    have h := Psi_mul_unitE_lo n lam 0 ⟨(b, a), not_lt.mpr hab.le⟩ v
    rw [vVal_of_lt n lam 0 hab, zero_mul] at h
    exact h
  have hdiag : ∀ a, ∀ v ∈ LinearMap.ker (Psi n (vVal n lam 0)),
      eR n a a v ∈ LinearMap.ker (Psi n (vVal n lam 0)) := by
    intro a v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [eR, LinearMap.mulRight_apply]
    have h := Psi_mul_unitE_lo n lam 0 ⟨(a, a), lt_irrefl a⟩ v
    rw [hv, mul_zero] at h
    exact h
  have key := ComplexJacquetFinite.diag_pow (LinearMap.ker (Psi n (vVal n lam 0)))
    (isGlFamily_eR n) hup hdiag (psiR n) (psiR_X n)
  rw [gel, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h := key k a 1
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero, eR_pow_apply, one_mul, Psi_psiR, Psi_one,
    mul_one] at h
  exact h

theorem gam_gel (k : ℕ) : gam n (gel n k) = ∑ a, ComplexJacquetFinite.gelPoly n k a := by
  refine MvPolynomial.funext fun lam => ?_
  rw [eval_gam, Psi_gel]

end Gelfand

/-! ## Integrality of `ℂ[λ]` over the image of `γ` -/

section Integral

variable {σ : Type*} (A : Subalgebra ℂ (MvPolynomial σ ℂ))

/-- The `A`-span of the polynomials of total degree at most `d`. -/
def Tf (d : ℕ) : Submodule A (MvPolynomial σ ℂ) :=
  Submodule.span A {g | g.totalDegree ≤ d}

variable {A}

theorem mem_Tf_of_le {f : MvPolynomial σ ℂ} {d : ℕ} (h : f.totalDegree ≤ d) : f ∈ Tf A d :=
  Submodule.subset_span h

theorem Tf_mono {d d' : ℕ} (h : d ≤ d') {f : MvPolynomial σ ℂ} (hf : f ∈ Tf A d) :
    f ∈ Tf A d' :=
  Submodule.span_mono (fun _ (hg : _ ≤ d) => hg.trans h) hf

theorem mem_Tf_of_mem {f : MvPolynomial σ ℂ} (hf : f ∈ A) : f ∈ Tf A 0 := by
  have h : f = (⟨f, hf⟩ : A) • (1 : MvPolynomial σ ℂ) := by
    rw [Subalgebra.smul_def, smul_eq_mul, mul_one]
  rw [h]
  exact Submodule.smul_mem _ _ (mem_Tf_of_le (by simp))

theorem Tf_mul {f g : MvPolynomial σ ℂ} {d d' : ℕ} (hf : f ∈ Tf A d) (hg : g ∈ Tf A d') :
    f * g ∈ Tf A (d + d') := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    induction hg using Submodule.span_induction with
    | mem y hy =>
      exact mem_Tf_of_le ((totalDegree_mul x y).trans (add_le_add hx hy))
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y y' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul a y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x x' _ _ h h' => rw [add_mul]; exact Submodule.add_mem _ h h'
  | smul a x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h

theorem C_mul_mem_Tf {f : MvPolynomial σ ℂ} {d : ℕ} (c : ℂ) (hf : f ∈ Tf A d) :
    C c * f ∈ Tf A d := by
  simpa using Tf_mul (mem_Tf_of_le (A := A) (totalDegree_C c).le) hf

theorem neg_one_pow_mem_Tf (m d : ℕ) : ((-1 : MvPolynomial σ ℂ) ^ m) ∈ Tf A d := by
  refine mem_Tf_of_le ((totalDegree_pow _ _).trans ?_)
  simp [totalDegree_neg]

end Integral

section Newton

variable {n} {A : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)}

/-- Newton's identities: if every power sum `p_b`, `1 ≤ b ≤ n`, lies in `T_{b-1}`, every
elementary symmetric polynomial `e_k`, `1 ≤ k ≤ n`, lies in `T_{k-1}`. -/
theorem esymm_mem_Tf (hp : ∀ b, 1 ≤ b → b ≤ n → psum (Fin n) ℂ b ∈ Tf A (b - 1)) :
    ∀ k, 1 ≤ k → k ≤ n → esymm (Fin n) ℂ k ∈ Tf A (k - 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk1 hkn
  have hsum : (∑ a ∈ Finset.antidiagonal k with a.1 < k,
      (-1 : MvPolynomial (Fin n) ℂ) ^ a.1 * esymm (Fin n) ℂ a.1 * psum (Fin n) ℂ a.2) ∈
        Tf A (k - 1) := by
    refine Submodule.sum_mem _ fun a ha => ?_
    rw [Finset.mem_filter, Finset.mem_antidiagonal] at ha
    obtain ⟨hak, hlt⟩ := ha
    have hps : psum (Fin n) ℂ a.2 ∈ Tf A (a.2 - 1) := hp a.2 (by omega) (by omega)
    by_cases ha0 : a.1 = 0
    · rw [ha0, esymm_zero, pow_zero, one_mul, one_mul]
      exact Tf_mono (by omega) hps
    · have hes : esymm (Fin n) ℂ a.1 ∈ Tf A (a.1 - 1) := ih a.1 hlt (by omega) (by omega)
      exact Tf_mono (by omega) (Tf_mul (Tf_mul (neg_one_pow_mem_Tf a.1 0) hes) hps)
  have hk : ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) ∈ Tf A (k - 1) := by
    rw [mul_esymm_eq_sum]
    exact Tf_mono (by omega) (Tf_mul (neg_one_pow_mem_Tf (k + 1) 0) hsum)
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have heq : esymm (Fin n) ℂ k =
      C (k : ℂ)⁻¹ * ((k : MvPolynomial (Fin n) ℂ) * esymm (Fin n) ℂ k) := by
    rw [← mul_assoc, ← map_natCast C, ← map_mul, inv_mul_cancel₀ hk0, map_one, one_mul]
  rw [heq]
  exact C_mul_mem_Tf _ hk

/-- Under the same hypothesis `X_a^n ∈ T_{n-1}`. -/
theorem xpow_mem_Tf (hp : ∀ b, 1 ≤ b → b ≤ n → psum (Fin n) ℂ b ∈ Tf A (b - 1)) (a : Fin n) :
    X a ^ n ∈ Tf A (n - 1) := by
  have hV := congrArg (Polynomial.eval (-X a : MvPolynomial (Fin n) ℂ))
    (MvPolynomial.prod_C_add_X_eq_sum_esymm ℂ (Fin n))
  rw [Polynomial.eval_prod, Finset.prod_eq_zero (Finset.mem_univ a) (by simp),
    Polynomial.eval_finsetSum, Fintype.card_fin, Finset.sum_range_succ'] at hV
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    esymm_zero, one_mul, Nat.sub_zero] at hV
  have hneg : (-X a : MvPolynomial (Fin n) ℂ) ^ n =
      -∑ j ∈ Finset.range n, esymm (Fin n) ℂ (j + 1) * (-X a) ^ (n - (j + 1)) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hV.symm
  have hc : ((-X a : MvPolynomial (Fin n) ℂ) ^ n) ∈ Tf A (n - 1) := by
    rw [hneg]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have he := esymm_mem_Tf hp (j + 1) (by omega) (by omega)
    have hx : ((-X a : MvPolynomial (Fin n) ℂ) ^ (n - (j + 1))) ∈ Tf A (n - (j + 1)) :=
      mem_Tf_of_le ((totalDegree_pow _ _).trans (by simp [totalDegree_neg]))
    exact Tf_mono (by omega) (Tf_mul he hx)
  have hx : (X a : MvPolynomial (Fin n) ℂ) ^ n = (-1) ^ n * (-X a) ^ n := by
    rw [← mul_pow]; ring
  rw [hx]
  exact Tf_mono (by omega) (Tf_mul (neg_one_pow_mem_Tf n 0) hc)

end Newton

section Box

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m : ℕ} {A : Subalgebra ℂ (MvPolynomial σ ℂ)}

/-- If every `X_s^m` lies in `T_{m-1}`, the monomials with exponents `< m` span `ℂ[σ]` over
`A`. -/
theorem mem_span_box (hm : ∀ _ : σ, 0 < m) (hrel : ∀ s, X s ^ m ∈ Tf A (m - 1))
    (f : MvPolynomial σ ℂ) :
    f ∈ Submodule.span A ((fun α => monomial α (1 : ℂ)) ''
      (ComplexJacquetFinite.boxSet σ m : Set (σ →₀ ℕ))) := by
  set S := Submodule.span A ((fun α => monomial α (1 : ℂ)) ''
      (ComplexJacquetFinite.boxSet σ m : Set (σ →₀ ℕ))) with hS
  suffices H : ∀ D (f : MvPolynomial σ ℂ), f.totalDegree ≤ D → f ∈ S from H _ f le_rfl
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
  intro f hf
  rw [f.as_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hαD : (α.sum fun _ e => e) ≤ D := (le_totalDegree hα).trans hf
  have hCmem : C (f.coeff α) ∈ A := by
    rw [← MvPolynomial.algebraMap_eq]; exact A.algebraMap_mem _
  rw [show monomial α (f.coeff α) = (⟨C (f.coeff α), hCmem⟩ : A) • monomial α (1 : ℂ) by
    rw [Subalgebra.smul_def, smul_eq_mul, C_mul_monomial, mul_one]]
  refine Submodule.smul_mem _ _ ?_
  by_cases hbox : ∀ s, α s < m
  · exact Submodule.subset_span ⟨α, ComplexJacquetFinite.mem_boxSet hbox, rfl⟩
  · push Not at hbox
    obtain ⟨s, hs⟩ := hbox
    set β := α - Finsupp.single s m with hβ
    have hα' : α = β + Finsupp.single s m :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hs)).symm
    have hmon : monomial α (1 : ℂ) = monomial β 1 * X s ^ m := by
      rw [X_pow_eq_monomial, monomial_mul_monomial, ← hα', one_mul]
    have hdegα : (α.sum fun _ e => e) = (β.sum fun _ e => e) + m := by
      rw [hα', Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index rfl]
    have hm0 := hm s
    rw [hmon]
    suffices key : ∀ g ∈ Tf A (m - 1), monomial β (1 : ℂ) * g ∈ S from key _ (hrel s)
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      refine ih (D - 1) (by omega) _ ?_
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_monomial _ one_ne_zero]
      have : g.totalDegree ≤ m - 1 := hg
      omega
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add g g' _ _ h h' => rw [mul_add]; exact Submodule.add_mem _ h h'
    | smul a g _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h

end Box

section HCIntegral

/-- The image of `γ`. -/
abbrev imA : Subalgebra ℂ (MvPolynomial (Fin n) ℂ) := (gamC n).range

theorem gelSum_mem (k : ℕ) : (∑ a, ComplexJacquetFinite.gelPoly n k a) ∈ imA n :=
  ⟨⟨gel n k, gel_mem_center n k⟩, gam_gel n k⟩

theorem psum_mem_Tf (b : ℕ) (hb : 1 ≤ b) : psum (Fin n) ℂ b ∈ Tf (imA n) (b - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  have h1 : (∑ a, ComplexJacquetFinite.gelPoly n (k + 1) a) ∈ Tf (imA n) (k + 1 - 1) :=
    Tf_mono (Nat.zero_le _) (mem_Tf_of_mem (gelSum_mem n (k + 1)))
  have h2 : (∑ a, (ComplexJacquetFinite.gelPoly n (k + 1) a - X a ^ (k + 1))) ∈
      Tf (imA n) (k + 1 - 1) :=
    Submodule.sum_mem _ fun a _ =>
      mem_Tf_of_le (by simpa using ComplexJacquetFinite.totalDegree_gelPoly_sub k a)
  have h3 : psum (Fin n) ℂ (k + 1) = (∑ a, ComplexJacquetFinite.gelPoly n (k + 1) a) -
      ∑ a, (ComplexJacquetFinite.gelPoly n (k + 1) a - X a ^ (k + 1)) := by
    rw [Finset.sum_sub_distrib, sub_sub_cancel, psum]
  rw [h3]
  exact Submodule.sub_mem _ h1 h2

instance finite_imA : Module.Finite (imA n) (MvPolynomial (Fin n) ℂ) := by
  refine ⟨⟨(ComplexJacquetFinite.boxSet (Fin n) n).image fun α => monomial α (1 : ℂ), ?_⟩⟩
  rw [Finset.coe_image]
  refine eq_top_iff.2 fun f _ => mem_span_box (fun a => Nat.lt_of_le_of_lt (Nat.zero_le _) a.2)
    (xpow_mem_Tf fun b hb _ => psum_mem_Tf n b hb) f

instance isIntegral_imA : Algebra.IsIntegral (imA n) (MvPolynomial (Fin n) ℂ) :=
  Algebra.IsIntegral.of_finite _ _

end HCIntegral

/-! ## Injectivity of `γ` -/

section Injective

theorem not_mem_expand (α : Idx n →₀ ℕ) {c : Idx n} (hc : c ∉ (expand (bsList n) α).toFinset) :
    α c = 0 := by
  by_contra h
  apply hc
  rw [List.mem_toFinset]
  simp only [expand, List.mem_flatMap, List.mem_replicate]
  exact ⟨c, mem_bsList n c, h, rfl⟩

theorem prod_expand {M : Type*} [CommMonoid M] (α : Idx n →₀ ℕ) (f : Idx n → M) :
    ((expand (bsList n) α).map f).prod = ∏ c, f c ^ α c := by
  rw [Finset.prod_list_map_count, Finset.prod_subset (Finset.subset_univ _)]
  · refine Finset.prod_congr rfl fun c _ => ?_
    rw [count_expand (bsList_nodup n) (mem_bsList n)]
  · intro c _ hc
    rw [count_expand (bsList_nodup n) (mem_bsList n), not_mem_expand n α hc, pow_zero]

theorem sum_expand {M : Type*} [AddCommMonoid M] (α : Idx n →₀ ℕ) (f : Idx n → M) :
    ((expand (bsList n) α).map f).sum = ∑ c, α c • f c := by
  rw [Finset.sum_list_map_count, Finset.sum_subset (Finset.subset_univ _)]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [count_expand (bsList_nodup n) (mem_bsList n)]
  · intro c _ hc
    rw [count_expand (bsList_nodup n) (mem_bsList n), not_mem_expand n α hc, zero_smul]

/-- The element `H₀ = diag(0, -1, …, -(n-1))` of `U`. -/
def hD : VermaGL.glU n := UniversalEnvelopingAlgebra.ι ℂ (Matrix.diagonal (dZero n))

theorem hD_mul_W (l : List (Idx n)) :
    hD n * W n l = W n l * hD n + (l.map fun c => dZero n c.1 - dZero n c.2).sum • W n l := by
  induction l with
  | nil => rw [W_nil, mul_one, one_mul, List.map_nil, List.sum_nil, zero_smul, add_zero]
  | cons c l ih =>
    have h1 := ι_diagonal_mul n (dZero n) c
    rw [W_cons, List.map_cons, List.sum_cons]
    calc hD n * (UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * W n l)
        = (hD n * UniversalEnvelopingAlgebra.ι ℂ (unitE n c)) * W n l := (mul_assoc _ _ _).symm
      _ = (UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * hD n +
            (dZero n c.1 - dZero n c.2) • UniversalEnvelopingAlgebra.ι ℂ (unitE n c)) * W n l := by
          rw [hD, h1]
      _ = UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * (hD n * W n l) +
            (dZero n c.1 - dZero n c.2) • (UniversalEnvelopingAlgebra.ι ℂ (unitE n c) * W n l) := by
          rw [add_mul, mul_assoc, smul_mul_assoc]
      _ = _ := by
          rw [ih, mul_add, mul_smul_comm, ← mul_assoc, add_smul]
          abel

/-- The `H₀`-weight of the PBW monomial `E^α`. -/
def sWt (α : Idx n →₀ ℕ) : ℂ := ((expand (bsList n) α).map fun c => dZero n c.1 - dZero n c.2).sum

theorem hD_comm_basisU (α : Idx n →₀ ℕ) :
    hD n * basisU n α - basisU n α * hD n = sWt n α • basisU n α := by
  rw [basisU_apply, hD_mul_W, add_sub_cancel_left, sWt]

theorem repr_hD_comm (u : VermaGL.glU n) (α : Idx n →₀ ℕ) :
    (basisU n).repr (hD n * u - u * hD n) α = sWt n α * (basisU n).repr u α := by
  have h : (basisU n).coord α ∘ₗ (LinearMap.mulLeft ℂ (hD n) - LinearMap.mulRight ℂ (hD n)) =
      sWt n α • (basisU n).coord α := by
    refine (basisU n).ext fun β => ?_
    rw [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply, hD_comm_basisU, map_smul, LinearMap.smul_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, smul_eq_mul, smul_eq_mul]
    by_cases hβ : β = α
    · subst hβ; rfl
    · simp [hβ]
  have := LinearMap.congr_fun h u
  rwa [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul] at this

/-- An exponent without strictly lower letters and of weight zero is diagonal. -/
theorem isDiag_of_sWt (α : Idx n →₀ ℕ) (hlo : ∀ c : Idx n, α c ≠ 0 → c.1 ≤ c.2)
    (h0 : sWt n α = 0) : ∀ c : Idx n, α c ≠ 0 → c.1 = c.2 := by
  have hcast : sWt n α = ((∑ c : Idx n, α c * ((c.2 : ℕ) - (c.1 : ℕ)) : ℕ) : ℂ) := by
    rw [sWt, sum_expand, Nat.cast_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : α c = 0
    · simp [hc]
    · have hle : (c.1 : ℕ) ≤ c.2 := Fin.le_iff_val_le_val.mp (hlo c hc)
      rw [nsmul_eq_mul, Nat.cast_mul, Nat.cast_sub hle, dZero, dZero]
      ring
  rw [hcast, Nat.cast_eq_zero, Finset.sum_eq_zero_iff] at h0
  intro c hc
  have h1 := h0 c (Finset.mem_univ c)
  have hle : (c.1 : ℕ) ≤ c.2 := Fin.le_iff_val_le_val.mp (hlo c hc)
  rcases mul_eq_zero.mp h1 with h1 | h1
  · exact absurd h1 hc
  · exact Fin.ext (by omega)

/-- The diagonal part `p ↦ α(p, p)` of an exponent. -/
def dgExp (α : Idx n →₀ ℕ) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => α (p, p)

theorem gam_basisU_of_diag (α : Idx n →₀ ℕ) (hα : ∀ c : Idx n, α c ≠ 0 → c.1 = c.2) :
    gam n (basisU n α) = monomial (dgExp n α) 1 := by
  rw [gam_basisU, prod_expand, Fintype.prod_prod_type, monomial_eq, C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [Finset.prod_eq_single p]
  · simp [Xd, dgExp]
  · intro q _ hqp
    have hz : α (p, q) = 0 := by
      by_contra h
      exact hqp (hα (p, q) h).symm
    rw [hz, pow_zero]
  · simp

theorem gam_basisU_of_not_diag (α : Idx n →₀ ℕ) {c : Idx n} (hc : α c ≠ 0) (hne : c.1 ≠ c.2) :
    gam n (basisU n α) = 0 := by
  rw [gam_basisU, prod_expand]
  refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
  rw [Xd, ite_eq_right hne, zero_pow hc]

theorem coeff_gam (u : VermaGL.glU n) (α : Idx n →₀ ℕ) (hα : ∀ c : Idx n, α c ≠ 0 → c.1 = c.2) :
    (gam n u).coeff (dgExp n α) = (basisU n).repr u α := by
  have h : (lcoeff ℂ (dgExp n α)) ∘ₗ gam n = (basisU n).coord α := by
    refine (basisU n).ext fun β => ?_
    rw [LinearMap.comp_apply, Module.Basis.coord_apply, Module.Basis.repr_self, lcoeff_apply]
    by_cases hβ : ∀ c : Idx n, β c ≠ 0 → c.1 = c.2
    · rw [gam_basisU_of_diag n β hβ, MvPolynomial.coeff_monomial, Finsupp.single_apply]
      by_cases hβα : β = α
      · subst hβα; simp
      · rw [ite_eq_right hβα, ite_eq_right]
        intro hd
        apply hβα
        ext ⟨p, q⟩
        by_cases hpq : p = q
        · subst hpq
          have := congrArg (fun f : Fin n →₀ ℕ => f p) hd
          simpa [dgExp] using this
        · have h1 : β (p, q) = 0 := by
            by_contra h1; exact hpq (hβ _ h1)
          have h2 : α (p, q) = 0 := by
            by_contra h2; exact hpq (hα _ h2)
          rw [h1, h2]
    · push Not at hβ
      obtain ⟨c, hc, hne⟩ := hβ
      rw [gam_basisU_of_not_diag n β hc hne, Finsupp.single_apply, ite_eq_right]
      · simp
      · rintro rfl
        exact hne (hα c hc)
  have := LinearMap.congr_fun h u
  rwa [LinearMap.comp_apply, lcoeff_apply, Module.Basis.coord_apply] at this

/-- If `γ(z) = 0` for central `z`, every PBW monomial in `z` has a strictly lower letter. -/
theorem exists_lower_letter (z : VermaGL.center n) (hz : gam n z = 0) (α : Idx n →₀ ℕ)
    (hα : (basisU n).repr (z : VermaGL.glU n) α ≠ 0) : ∃ c : Idx n, α c ≠ 0 ∧ c.2 < c.1 := by
  by_contra hlo
  push Not at hlo
  have hc : hD n * (z : VermaGL.glU n) - z * hD n = 0 := by
    rw [sub_eq_zero]
    exact Subalgebra.mem_center_iff.mp z.2 (hD n)
  have hs := repr_hD_comm n (z : VermaGL.glU n) α
  rw [hc, map_zero, Finsupp.zero_apply] at hs
  have hs0 : sWt n α = 0 := by
    rcases mul_eq_zero.mp hs.symm with h | h
    · exact h
    · exact absurd h hα
  have hdiag := isDiag_of_sWt n α hlo hs0
  have := coeff_gam n z α hdiag
  rw [hz] at this
  apply hα
  rw [← this]
  simp

/-! ### Symbols -/

/-- The symbol data of `U(𝔤𝔩_n)` for the basis of matrix units. -/
abbrev sd := AssocSymbol.symbolData (stdB n)

theorem basisU_eq_om (α : Idx n →₀ ℕ) :
    basisU n α = orderedMonomial ℂ (Matrix (Fin n) (Fin n) ℂ) (stdB n) (bsList n) α := by
  rw [basisU, pbwBasis_apply]

theorem symbol_basisU {N : ℕ} (α : Idx n →₀ ℕ) (hα : α.degree ≤ N) :
    (sd n).symbol N (basisU n α) = if α.degree = N then monomial α 1 else 0 := by
  rw [basisU_eq_om]
  exact symbol_orderedMonomial ℂ _ (stdB n) (sd n) (AssocSymbol.symbolData_ξ_basis _)
    (bsList_nodup n) (mem_bsList n) hα

/-- The coadjoint derivation `X_c ↦ ξ⁅x, E_c⁆` of `ℂ[X_c]`. -/
def dx (x : Matrix (Fin n) (Fin n) ℂ) :
    Derivation ℂ (MvPolynomial (Idx n) ℂ) (MvPolynomial (Idx n) ℂ) :=
  mkDerivation ℂ fun c => (sd n).ξ ⁅x, stdB n c⁆

theorem dx_ξ (x y : Matrix (Fin n) (Fin n) ℂ) : dx n x ((sd n).ξ y) = (sd n).ξ ⁅x, y⁆ := by
  conv_rhs => rw [← (stdB n).sum_repr y]
  rw [AssocSymbol.symbolData_ξ, map_sum, lie_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Derivation.map_smul, dx, mkDerivation_X, lie_smul, map_smul]

theorem dx_isLeibniz (x : Matrix (Fin n) (Fin n) ℂ) : IsLeibniz ((dx n x).toLinearMap) := by
  intro f g
  change dx n x (f * g) = f * dx n x g + dx n x f * g
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem dx_symbol_center (z : VermaGL.center n) (x : Matrix (Fin n) (Fin n) ℂ) {N : ℕ}
    (hN : (z : VermaGL.glU n) ∈ degreeFiltration ℂ (Matrix (Fin n) (Fin n) ℂ) N) :
    dx n x ((sd n).symbol N z) = 0 := by
  have h := (sd n).symbol_commutator x (dx n x).toLinearMap (dx_isLeibniz n x)
    (fun y => dx_ξ n x y) hN
  have hz : UniversalEnvelopingAlgebra.ι ℂ x * (z : VermaGL.glU n) -
      z * UniversalEnvelopingAlgebra.ι ℂ x = 0 := by
    rw [sub_eq_zero]
    exact Subalgebra.mem_center_iff.mp z.2 _
  rw [hz, map_zero] at h
  exact h.symm

/-! ### Transfer to the Library's coadjoint derivations -/

/-- A single block of size `n`. -/
abbrev nU : Unit → ℕ := fun _ => n

/-- Matrix-unit indices as coordinates of the single block. -/
def eU (c : Idx n) : Coord (nU n) := ⟨(), c⟩

theorem dx_X (a b r q : Fin n) :
    dx n (unitE n (a, b)) (X (r, q)) =
      (if r = b then X (a, q) else 0) - (if q = a then X (r, b) else 0) := by
  rw [dx, mkDerivation_X, stdB_apply]
  have hl : ⁅unitE n (a, b), unitE n (r, q)⁆ =
      (if r = b then unitE n (a, q) else 0) - (if q = a then unitE n (r, b) else 0) := by
    rw [Ring.lie_def]
    congr 1
    · by_cases h : r = b
      · subst h
        rw [ite_eq_left rfl]
        simp only [unitE]
        rw [Matrix.single_mul_single_same, mul_one]
      · rw [ite_eq_right h]
        simp only [unitE]
        rw [Matrix.single_mul_single_of_ne (1 : ℂ) a b r (Ne.symm h)]
    · by_cases h : q = a
      · subst h
        rw [ite_eq_left rfl]
        simp only [unitE]
        rw [Matrix.single_mul_single_same, mul_one]
      · rw [ite_eq_right h]
        simp only [unitE]
        rw [Matrix.single_mul_single_of_ne (1 : ℂ) r q a h]
  have hξ : ∀ c, (sd n).ξ (unitE n c) = X c := fun c => by
    rw [← stdB_apply]
    exact AssocSymbol.symbolData_ξ_basis _ c
  rw [hl, map_sub]
  by_cases h1 : r = b <;> by_cases h2 : q = a <;> simp [h1, h2, hξ]

theorem rename_dx_X (a b : Fin n) (c : Idx n) :
    rename (eU n) (dx n (unitE n (a, b)) (X c)) =
      coadDer ℂ (nU n) (Kostant.unit ℂ (nU n) () a b) (X (eU n c)) := by
  obtain ⟨r, q⟩ := c
  rw [dx_X, eU, coadDer_unit_X_same (nU n) () a b r q]
  by_cases h1 : r = b <;> by_cases h2 : q = a <;> simp [h1, h2, eU]

theorem rename_dx (a b : Fin n) (f : MvPolynomial (Idx n) ℂ) :
    rename (eU n) (dx n (unitE n (a, b)) f) =
      coadDer ℂ (nU n) (Kostant.unit ℂ (nU n) () a b) (rename (eU n) f) := by
  induction f using MvPolynomial.induction_on with
  | C c => rw [rename_C, MvPolynomial.derivation_C, MvPolynomial.derivation_C, map_zero]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | mul_X f c hf =>
    rw [Derivation.leibniz, map_mul (rename (eU n)) f (X c), rename_X, Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul, rename_X]
    rw [← hf, rename_dx_X]

/-- Every complex matrix is conjugate to an upper triangular one. -/
theorem exists_triangular (M : Matrix (Fin n) (Fin n) ℂ) :
    ∃ P Q : Matrix (Fin n) (Fin n) ℂ, P * Q = 1 ∧ ∀ i j : Fin n, j < i → (Q * M * P) i j = 0 := by
  obtain ⟨t, ht⟩ : ∃ t : ℂ, M.charpoly.eval t ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : M.charpoly = 0 := Polynomial.funext fun t => by rw [h t, Polynomial.eval_zero]
    exact (Matrix.charpoly_monic M).ne_zero h0
  rw [Matrix.eval_charpoly] at ht
  set A := Matrix.scalar (Fin n) t - M with hAdef
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr ht)
  let ρ : Multiplicative ℤ →* Matrix (Fin n) (Fin n) ℂ :=
    (Units.coeHom _).comp (zpowersHom _ hA.unit)
  have hρ : ρ (Multiplicative.ofAdd 1) = A := by simp [ρ]
  obtain ⟨P, Q, hPQ, htri⟩ := LieKolchin.exists_triangularizing_cyclic n ρ
  refine ⟨P, Q, hPQ, fun i j hij => ?_⟩
  have h1 := htri (Multiplicative.ofAdd 1) i j hij
  rw [hρ] at h1
  have hQP : Q * P = 1 := mul_eq_one_comm.mp hPQ
  have hs : Matrix.scalar (Fin n) t = t • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hM : Q * M * P = t • (1 : Matrix (Fin n) (Fin n) ℂ) - Q * A * P := by
    rw [hAdef, hs, mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQP]
    abel
  rw [hM, Matrix.sub_apply, h1, sub_zero, Matrix.smul_apply, Matrix.one_apply_ne hij.ne',
    smul_zero]

/-- A polynomial killed by the coadjoint derivations and vanishing on upper triangular matrices
is zero. -/
theorem eq_zero_of_invariant (σ : MvPolynomial (Idx n) ℂ)
    (hinv : ∀ a b : Fin n, dx n (unitE n (a, b)) σ = 0)
    (hup : ∀ Y : Idx n → ℂ, (∀ c : Idx n, c.2 < c.1 → Y c = 0) → eval Y σ = 0) : σ = 0 := by
  set W : Submodule ℂ (MvPolynomial (Coord (nU n)) ℂ) := ℂ ∙ rename (eU n) σ with hW
  have hWst : ∀ (i : Unit) (a b : Fin (nU n i)), a ≠ b → ∀ f ∈ W,
      coadDer ℂ (nU n) (Kostant.unit ℂ (nU n) i a b) f ∈ W := by
    intro i a b _ f hf
    cases i
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
    rw [Derivation.map_smul, ← rename_dx n a b σ, hinv, map_zero, smul_zero]
    exact W.zero_mem
  have hev : ∀ M : Matrix (Fin n) (Fin n) ℂ, eval (fun c : Idx n => M c.1 c.2) σ = 0 := by
    intro M
    obtain ⟨P, Q, hPQ, htri⟩ := exists_triangular n M
    have hT : (fun _ : Unit => Q * M * P) ∈ zeroSet (nU n) W := by
      rw [zeroSet, Set.mem_ofPred_eq]
      intro f hf
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hf
      rw [smul_eq_C_mul, eval_mul, eval_rename]
      rw [hup (tuplePoint (nU n) (fun _ : Unit => Q * M * P) ∘ eU n)
        (fun c hc => htri c.1 c.2 hc), mul_zero]
    have hP : IsUnit P.det := Matrix.isUnit_det_of_right_inverse hPQ
    have h := conj_mem_zeroSet hWst (fun _ => P) (fun _ => hP) hT
    rw [zeroSet, Set.mem_ofPred_eq] at h
    have h2 := h (rename (eU n) σ) (Submodule.mem_span_singleton_self _)
    rw [eval_rename] at h2
    have hconj : P * (Q * M * P) * P⁻¹ = M := by
      rw [Matrix.inv_eq_right_inv hPQ]
      simp only [← mul_assoc, hPQ, one_mul]
      rw [mul_assoc, hPQ, mul_one]
    have hfun : (tuplePoint (nU n) (fun _ : Unit => P * (Q * M * P) * P⁻¹) ∘ eU n) =
        fun c : Idx n => M c.1 c.2 := by
      funext c
      simp only [Function.comp_apply, tuplePoint, eU, hconj]
    rw [hfun] at h2
    exact h2
  refine MvPolynomial.funext fun Y => ?_
  rw [map_zero]
  have := hev (Matrix.of fun i j => Y (i, j))
  simpa using this

/-- **Injectivity of the Harish-Chandra map.** -/
theorem gamC_injective : Function.Injective (gamC n) := by
  refine (injective_iff_map_eq_zero (gamC n)).2 fun z hz => ?_
  rw [gamC_apply] at hz
  by_contra hz0
  have hu : (z : VermaGL.glU n) ≠ 0 := fun h => hz0 (Subtype.ext h)
  set r := (basisU n).repr (z : VermaGL.glU n) with hr
  have hne : r.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    intro h
    apply hu
    rw [← (basisU n).linearCombination_repr (z : VermaGL.glU n), ← hr, h, map_zero]
  set N := r.support.sup Finsupp.degree with hNdef
  obtain ⟨α₀, hα₀, hN⟩ := Finset.exists_mem_eq_sup _ hne Finsupp.degree
  have hsum : (z : VermaGL.glU n) = ∑ β ∈ r.support, r β • basisU n β := by
    conv_lhs => rw [← (basisU n).linearCombination_repr (z : VermaGL.glU n)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
  have hmem : (z : VermaGL.glU n) ∈ degreeFiltration ℂ (Matrix (Fin n) (Fin n) ℂ) N := by
    rw [hsum]
    refine Submodule.sum_mem _ fun β hβ => Submodule.smul_mem _ _ ?_
    rw [basisU_eq_om]
    exact degreeFiltration_mono ℂ _ (Finset.le_sup hβ)
      (orderedMonomial_mem_degreeFiltration ℂ _ (stdB n) (bsList_nodup n) (mem_bsList n) β)
  set σ := (sd n).symbol N (z : VermaGL.glU n) with hσ
  have hσsum : σ = ∑ β ∈ r.support, r β • (if β.degree = N then monomial β (1 : ℂ) else 0) := by
    rw [hσ, hsum, map_sum]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [map_smul, symbol_basisU n β (Finset.le_sup hβ)]
  have hcoeff : σ.coeff α₀ = r α₀ := by
    rw [hσsum, MvPolynomial.coeff_sum, Finset.sum_eq_single α₀]
    · rw [MvPolynomial.coeff_smul, ← hN, ite_eq_left rfl, MvPolynomial.coeff_monomial, ite_eq_left rfl, smul_eq_mul, mul_one]
    · intro β _ hβα
      rw [MvPolynomial.coeff_smul]
      split_ifs
      · rw [MvPolynomial.coeff_monomial, ite_eq_right hβα, smul_zero]
      · simp
    · intro h
      exact absurd hα₀ h
  have hup : ∀ Y : Idx n → ℂ, (∀ c : Idx n, c.2 < c.1 → Y c = 0) → eval Y σ = 0 := by
    intro Y hY
    rw [hσsum, map_sum]
    refine Finset.sum_eq_zero fun β hβ => ?_
    obtain ⟨c, hc, hlt⟩ := exists_lower_letter n z hz β (Finsupp.mem_support_iff.mp hβ)
    rw [smul_eq_C_mul, eval_mul, eval_C]
    split_ifs
    · rw [eval_monomial, Finsupp.prod,
        Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hc) (by rw [hY c hlt, zero_pow hc]),
        mul_zero, mul_zero]
    · rw [map_zero, mul_zero]
  have hzero : σ = 0 :=
    eq_zero_of_invariant n σ (fun a b => dx_symbol_center n z _ hmem) hup
  rw [hzero] at hcoeff
  exact (Finsupp.mem_support_iff.mp hα₀) (hcoeff.symm.trans (by simp))

end Injective

/-! ## Central characters -/

section Character

/-- `γ` as an isomorphism of `Z(𝔤𝔩_n)` onto its image. -/
def eqv : VermaGL.center n ≃ₐ[ℂ] imA n := AlgEquiv.ofInjective (gamC n) (gamC_injective n)

theorem coe_eqv (z : VermaGL.center n) : ((eqv n z : imA n) : MvPolynomial (Fin n) ℂ) = gamC n z :=
  rfl

/-- The character of the image of `γ` corresponding to a central character `χ`. -/
def chiA (χ : VermaGL.center n →ₐ[ℂ] ℂ) : imA n →ₐ[ℂ] ℂ :=
  χ.comp ((eqv n).symm : imA n →ₐ[ℂ] VermaGL.center n)

theorem chiA_eqv (χ : VermaGL.center n →ₐ[ℂ] ℂ) (z : VermaGL.center n) :
    chiA n χ (eqv n z) = χ z := by
  show χ ((eqv n).symm (eqv n z)) = χ z
  rw [AlgEquiv.symm_apply_apply]

/-- The weights `λ` with `γ(z)(λ) = χ(z)` for all central `z`. -/
def fib (χ : VermaGL.center n →ₐ[ℂ] ℂ) : Set (Fin n → ℂ) :=
  {lam | ∀ z : VermaGL.center n, eval lam (gamC n z) = χ z}

theorem chiA_eval {χ : VermaGL.center n →ₐ[ℂ] ℂ} {lam : Fin n → ℂ} (h : lam ∈ fib n χ)
    (b : imA n) : chiA n χ b = eval lam (b : MvPolynomial (Fin n) ℂ) := by
  obtain ⟨z, rfl⟩ := (eqv n).surjective b
  rw [chiA_eqv, coe_eqv, h z]

/-- Every central character is attained (lying over). -/
theorem fib_nonempty (χ : VermaGL.center n →ₐ[ℂ] ℂ) : (fib n χ).Nonempty := by
  have hsurj : Function.Surjective (chiA n χ) := fun c =>
    ⟨algebraMap ℂ (imA n) c, (chiA n χ).commutes c⟩
  have hmax : (RingHom.ker (chiA n χ)).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hker : RingHom.ker (algebraMap (imA n) (MvPolynomial (Fin n) ℂ)) ≤
      RingHom.ker (chiA n χ) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hx0 : x = 0 := Subtype.ext hx
    rw [hx0]
    exact Ideal.zero_mem _
  obtain ⟨Q, hQ, hQP⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := MvPolynomial (Fin n) ℂ) _ hker
  obtain ⟨lam, hlam⟩ := MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton.mp hQ
  refine ⟨lam, fun z => ?_⟩
  set b : imA n := eqv n z - algebraMap ℂ (imA n) (χ z) with hb
  have hbk : b ∈ RingHom.ker (chiA n χ) := by
    rw [RingHom.mem_ker, hb, map_sub, AlgHom.commutes, chiA_eqv, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self]
  rw [← hQP, Ideal.mem_under, hlam, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hbk
  have hbv : algebraMap (imA n) (MvPolynomial (Fin n) ℂ) b = gamC n z - C (χ z) := by
    rw [hb, map_sub, ← IsScalarTower.algebraMap_apply ℂ (imA n) (MvPolynomial (Fin n) ℂ),
      MvPolynomial.algebraMap_eq]
    rfl
  rw [hbv, map_sub, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply,
    sub_eq_zero, MvPolynomial.aeval_eq_eval] at hbk
  exact hbk

/-- Each central character is attained at finitely many weights. -/
theorem fib_finite (χ : VermaGL.center n →ₐ[ℂ] ℂ) : (fib n χ).Finite := by
  have hint : ∀ a : Fin n, ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∀ lam ∈ fib n χ, q.IsRoot (lam a) := by
    intro a
    obtain ⟨p, hpm, hpX⟩ :=
      Algebra.IsIntegral.isIntegral (R := imA n) (X a : MvPolynomial (Fin n) ℂ)
    refine ⟨p.map (chiA n χ).toRingHom, (hpm.map _).ne_zero, fun lam hlam => ?_⟩
    have hev : (chiA n χ).toRingHom =
        (MvPolynomial.eval lam).comp (algebraMap (imA n) (MvPolynomial (Fin n) ℂ)) :=
      RingHom.ext fun b => chiA_eval n hlam b
    have h := congrArg (MvPolynomial.eval lam) hpX
    rw [Polynomial.hom_eval₂, map_zero, MvPolynomial.eval_X, ← hev, ← Polynomial.eval_map] at h
    exact h
  choose q hq0 hroot using hint
  refine Set.Finite.subset (Set.Finite.pi' (t := fun a => {x | (q a).IsRoot x})
    (fun a => Polynomial.finite_setOfPred_isRoot (hq0 a))) ?_
  intro lam hlam a
  exact hroot a lam hlam

/-! ### Height -/

/-- The height `h(x) = -Σ_r r · Re(x_r)`; positive roots `e_p - e_q` (`p < q`) have height
`q - p ≥ 1`. -/
def hgt (x : Fin n → ℂ) : ℝ := ∑ r : Fin n, -((r : ℕ) : ℝ) * (x r).re

theorem hgt_add (x y : Fin n → ℂ) : hgt n (x + y) = hgt n x + hgt n y := by
  simp only [hgt, Pi.add_apply, Complex.add_re, mul_add, Finset.sum_add_distrib]

theorem hgt_sub (x y : Fin n → ℂ) : hgt n (x - y) = hgt n x - hgt n y := by
  simp only [hgt, Pi.sub_apply, Complex.sub_re, mul_sub, Finset.sum_sub_distrib]

theorem hgt_single (p : Fin n) : hgt n (Pi.single p 1) = -((p : ℕ) : ℝ) := by
  rw [hgt, Finset.sum_eq_single p]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem cone_hgt {v : Fin n → ℂ} (hv : v ∈ VermaGL.posRootCone n) : v = 0 ∨ 1 ≤ hgt n v := by
  unfold VermaGL.posRootCone at hv
  induction hv using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨p, q, hpq, rfl⟩ := hx
    right
    rw [hgt_sub, hgt_single, hgt_single]
    have h1 : (p : ℕ) + 1 ≤ q := hpq
    have h2 : ((p : ℕ) : ℝ) + 1 ≤ ((q : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  | zero => left; rfl
  | add x y _ _ hx hy =>
    rcases hx with rfl | hx
    · rw [zero_add]
      exact hy
    rcases hy with rfl | hy
    · rw [add_zero]
      exact Or.inr hx
    right
    rw [hgt_add]
    linarith

end Character

/-- **Central characters of lower Verma modules.** Every character `χ` of `Z(𝔤𝔩_n(ℂ))` is the
central character of `M⁻(λ)` for some `Z`-extremal `λ`. -/
theorem lowerVermaCentral : VermaGL.CentralCharacterStatement := by
  intro n χ
  obtain ⟨lam, hlam, hmin⟩ :=
    Set.exists_min_image (fib n χ) (hgt n) (fib_finite n χ) (fib_nonempty n χ)
  refine ⟨lam, ?_, fun z => by rw [eval_gamC_smul_gen, hlam z]⟩
  intro μ hμ hne
  have hμF : μ ∉ fib n χ := by
    intro hμF
    have h1 := hmin μ hμF
    rcases cone_hgt n hμ with h0 | h0
    · exact hne (sub_eq_zero.mp h0).symm
    · rw [hgt_sub] at h0
      linarith
  simp only [fib, Set.mem_ofPred_eq, not_forall] at hμF
  obtain ⟨z, hz⟩ := hμF
  refine ⟨(z : VermaGL.glU n), z.2, χ z, by rw [eval_gamC_smul_gen, hlam z], fun h => hz ?_⟩
  rw [eval_gamC_smul_gen] at h
  exact smul_left_injective ℂ (gen_ne_zero n μ) h

end Langlands.Archimedean.VermaCentral
