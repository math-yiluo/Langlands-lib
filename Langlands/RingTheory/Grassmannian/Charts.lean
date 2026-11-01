import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Algebraic charts of the quotient Grassmannian

Adapted from the Anthropic FLT source at commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the two solutions
P2M/Sol/S_Module_Grassmannian_exists_chart_equiv_linearMap.lean and
P2M/Sol/S_Module_Grassmannian_exists_chart_equiv_algHom_symmetricAlgebra_quotient.lean.
The original distribution is licensed under Apache 2.0; see
licenses/Anthropic-FLT/LICENSE, NOTICE and ATTRIBUTION.md.
The paired Markdown records source comparisons and compatibility edits.
-/

open scoped TensorProduct
open TensorProduct

set_option autoImplicit false

namespace Module.Grassmannian.ChartLinear

variable (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M)
variable (A : Type) [CommRing A] [Algebra R A]

abbrev Chart : Type :=
  {N : Module.Grassmannian A (A ⊗[R] M) k //
    Function.Bijective fun v : Fin k → A => ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}

abbrev HomX : Type :=
  {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1}

variable {R A}

def cmap (N : Submodule A (A ⊗[R] M)) : (Fin k → A) →ₗ[A] (A ⊗[R] M) ⧸ N :=
  Fintype.linearCombination A (fun i => N.mkQ ((1 : A) ⊗ₜ[R] x i))

lemma coe_cmap (N : Submodule A (A ⊗[R] M)) :
    ⇑(cmap x N) = fun v : Fin k → A => ∑ i, v i • N.mkQ ((1 : A) ⊗ₜ[R] x i) := rfl

lemma cmap_single (N : Submodule A (A ⊗[R] M)) (j : Fin k) :
    cmap x N (Pi.single j 1) = N.mkQ ((1 : A) ⊗ₜ[R] x j) := by
  classical
  simp [cmap]

noncomputable def coordEquiv (N : Chart R x A) : (Fin k → A) ≃ₗ[A] (A ⊗[R] M) ⧸ N.1.toSubmodule :=
  LinearEquiv.ofBijective (cmap x N.1.toSubmodule) N.2

lemma coordEquiv_apply (N : Chart R x A) (v : Fin k → A) :
    coordEquiv x N v = cmap x N.1.toSubmodule v := rfl

lemma coordEquiv_symm_mkQ_x (N : Chart R x A) (j : Fin k) :
    (coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x j)) = Pi.single j 1 := by
  rw [LinearEquiv.symm_apply_eq, coordEquiv_apply, cmap_single]

noncomputable def toHomX (N : Chart R x A) : HomX R x A :=
  ⟨(((coordEquiv x N).symm.toLinearMap ∘ₗ N.1.toSubmodule.mkQ).restrictScalars R) ∘ₗ
      TensorProduct.mk R A M 1,
    fun j => by
      simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
        Function.comp_apply, TensorProduct.mk_apply]
      exact coordEquiv_symm_mkQ_x x N j⟩

lemma toHomX_apply (N : Chart R x A) (m : M) :
    (toHomX x N).1 m = (coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) := rfl

noncomputable abbrev ext' (ψ : M →ₗ[R] (Fin k → A)) : A ⊗[R] M →ₗ[A] (Fin k → A) :=
  ψ.liftBaseChange A

lemma ext'_surjective (ψ : HomX R x A) : Function.Surjective (ext' ψ.1) := by
  intro v
  refine ⟨∑ i, v i ⊗ₜ[R] x i, ?_⟩
  simp only [map_sum, LinearMap.liftBaseChange_tmul, ψ.2]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

noncomputable def quotEquiv (ψ : HomX R x A) :
    ((A ⊗[R] M) ⧸ LinearMap.ker (ext' ψ.1)) ≃ₗ[A] (Fin k → A) :=
  (ext' ψ.1).quotKerEquivOfSurjective (ext'_surjective x ψ)

lemma quotEquiv_mkQ (ψ : HomX R x A) (p : A ⊗[R] M) :
    quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ p) = ext' ψ.1 p :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

lemma quotEquiv_cmap (ψ : HomX R x A) (v : Fin k → A) :
    quotEquiv x ψ (cmap x (LinearMap.ker (ext' ψ.1)) v) = v := by
  simp only [coe_cmap, map_sum, map_smul, quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul,
    ψ.2]
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

lemma cmap_ker_eq (ψ : HomX R x A) :
    ⇑(cmap x (LinearMap.ker (ext' ψ.1))) = (quotEquiv x ψ).symm := by
  funext v
  rw [eq_comm, LinearEquiv.symm_apply_eq, quotEquiv_cmap]

noncomputable def ofHomX (ψ : HomX R x A) : Chart R x A := by
  refine ⟨{ toSubmodule := LinearMap.ker (ext' ψ.1)
            finite_quotient := Module.Finite.equiv (quotEquiv x ψ).symm
            projective_quotient := Module.Projective.of_equiv (quotEquiv x ψ).symm
            rankAtStalk_eq := fun p => ?_ }, ?_⟩
  · have : Nontrivial A := by
      by_contra h
      have := not_nontrivial_iff_subsingleton.mp h
      exact IsEmpty.false p
    rw [Module.rankAtStalk_eq_of_equiv (quotEquiv x ψ), Module.rankAtStalk_eq_finrank_of_free,
      Module.finrank_fin_fun]
    rfl
  · change Function.Bijective (cmap x (LinearMap.ker (ext' ψ.1)))
    rw [cmap_ker_eq]
    exact (quotEquiv x ψ).symm.bijective

lemma ofHomX_toSubmodule (ψ : HomX R x A) :
    (ofHomX x ψ).1.toSubmodule = LinearMap.ker (ext' ψ.1) := rfl

lemma ext'_toHomX (N : Chart R x A) :
    ext' (toHomX x N).1 = (coordEquiv x N).symm.toLinearMap ∘ₗ N.1.toSubmodule.mkQ := by
  refine TensorProduct.AlgebraTensorModule.ext fun a m => ?_
  simp only [LinearMap.liftBaseChange_tmul, toHomX_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← map_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

lemma ofHomX_toHomX (N : Chart R x A) : ofHomX x (toHomX x N) = N := by
  apply Subtype.ext
  apply Module.Grassmannian.ext
  rw [ofHomX_toSubmodule, ext'_toHomX, LinearEquiv.ker_comp, Submodule.ker_mkQ]

lemma coordEquiv_ofHomX_symm (ψ : HomX R x A) (y) :
    (coordEquiv x (ofHomX x ψ)).symm y = quotEquiv x ψ y := by
  have h1 : (coordEquiv x (ofHomX x ψ)) ((coordEquiv x (ofHomX x ψ)).symm y) = y :=
    LinearEquiv.apply_symm_apply _ _
  rw [coordEquiv_apply] at h1
  have h2 := congrArg (quotEquiv x ψ) h1

  change quotEquiv x ψ (cmap x (LinearMap.ker (ext' ψ.1)) _) = _ at h2
  rwa [quotEquiv_cmap] at h2

lemma toHomX_ofHomX (ψ : HomX R x A) : toHomX x (ofHomX x ψ) = ψ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro m
  rw [toHomX_apply, coordEquiv_ofHomX_symm]
  change quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ ((1 : A) ⊗ₜ[R] m)) = _
  rw [quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul]

noncomputable def chartEquiv : Chart R x A ≃ HomX R x A where
  toFun := toHomX x
  invFun := ofHomX x
  left_inv := ofHomX_toHomX x
  right_inv := toHomX_ofHomX x

variable {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)

def pushHomX (ψ : HomX R x A) : HomX R x B :=
  ⟨(φ.toLinearMap.compLeft (Fin k)) ∘ₗ ψ.1, fun j => by
    ext i
    simp [LinearMap.compLeft, ψ.2, Pi.single_apply, apply_ite φ]⟩

lemma pushHomX_apply (ψ : HomX R x A) (m : M) (i : Fin k) :
    (pushHomX x φ ψ).1 m i = φ (ψ.1 m i) := rfl

lemma map_ofHomX_toSubmodule (ψ : HomX R x A) :
    (Module.Grassmannian.map φ (ofHomX x ψ).1).toSubmodule =
      LinearMap.ker (ext' (pushHomX x φ ψ).1) := by
  classical
  rw [Module.Grassmannian.map_toSubmodule]
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <| IsScalarTower.algebraMap_eq R A B

  let T : B ⊗[A] ((A ⊗[R] M) ⧸ (ofHomX x ψ).1.toSubmodule) ≃ₗ[B] (Fin k → B) :=
    (quotEquiv x ψ).baseChange A B _ _ ≪≫ₗ TensorProduct.piScalarRight A B B (Fin k)
  have hT : (T.toLinearMap ∘ₗ Module.Grassmannian.baseChangeMkQ B (ofHomX x ψ).1.toSubmodule) =
      ext' (pushHomX x φ ψ).1 := by
    refine TensorProduct.AlgebraTensorModule.ext fun b m => ?_
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Module.Grassmannian.baseChangeMkQ, TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul]
    simp only [T]
    change TensorProduct.piScalarRight A B B (Fin k) (b ⊗ₜ[A] quotEquiv x ψ ((LinearMap.ker (ext' ψ.1)).mkQ _)) = _
    rw [quotEquiv_mkQ, LinearMap.liftBaseChange_tmul, one_smul]
    ext i
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Pi.smul_apply,
      pushHomX_apply, smul_eq_mul, Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]
    rfl
  rw [← hT, LinearEquiv.ker_comp]

lemma map_ofHomX (ψ : HomX R x A) :
    Module.Grassmannian.map φ (ofHomX x ψ).1 = (ofHomX x (pushHomX x φ ψ)).1 :=
  Module.Grassmannian.ext (map_ofHomX_toSubmodule x φ ψ)

lemma map_mem_chart (N : Chart R x A) :
    Function.Bijective fun v : Fin k → B =>
      ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i) := by
  have hN : N = ofHomX x (toHomX x N) := (ofHomX_toHomX x N).symm
  rw [hN, map_ofHomX]
  exact (ofHomX x (pushHomX x φ (toHomX x N))).2

lemma chartEquiv_map (N : Chart R x A) :
    chartEquiv x ⟨Module.Grassmannian.map φ N.1, map_mem_chart x φ N⟩ =
      pushHomX x φ (chartEquiv x N) := by
  have hN : N = ofHomX x (toHomX x N) := (ofHomX_toHomX x N).symm
  have : (⟨Module.Grassmannian.map φ N.1, map_mem_chart x φ N⟩ : Chart R x B) =
      ofHomX x (pushHomX x φ (toHomX x N)) := by
    apply Subtype.ext
    change Module.Grassmannian.map φ N.1 = _
    conv_lhs => rw [hN]
    exact map_ofHomX x φ (toHomX x N)
  rw [this]
  exact toHomX_ofHomX x _

end Module.Grassmannian.ChartLinear

open Module.Grassmannian.ChartLinear in
theorem Module.Grassmannian.exists_chart_equiv_linearMap
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M) :
    ∃ pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} ≃
          {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1},
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, (pt A N).1 m i • N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (ψ : {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1}),
          ((pt A).symm ψ).1.toSubmodule = LinearMap.ker (ψ.1.liftBaseChange A)) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            ∀ (m : M) (i : Fin k),
              (pt B ⟨Module.Grassmannian.map φ N.1, h⟩).1 m i = φ ((pt A N).1 m i)) := by
  refine ⟨fun A _ _ => chartEquiv (R := R) (A := A) x, ?_, ?_, ?_⟩
  ·
    intro A _ _ N m
    change cmap x N.1.toSubmodule ((coordEquiv x N).symm (N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m))) = _
    rw [← coordEquiv_apply, LinearEquiv.apply_symm_apply]
  · intro A _ _ ψ
    rfl
  · intro A B _ _ _ _ φ N
    exact ⟨map_mem_chart x φ N, fun m i => by
      have h := chartEquiv_map x φ N
      exact congrArg (fun ψ : HomX R x B => ψ.1 m i) h⟩

open scoped TensorProduct
open TensorProduct

set_option autoImplicit false

namespace Module.Grassmannian.ChartAlgebra

variable (R : Type) [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (x : Fin k → M)
variable (A : Type) [CommRing A] [Algebra R A]

def rels : Set (SymmetricAlgebra R (Fin k → M)) :=
  {a | ∃ i j : Fin k, a = SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) - if i = j then 1 else 0}

abbrev S : Type := SymmetricAlgebra R (Fin k → M) ⧸ Ideal.span (rels R x)

abbrev HomX : Type :=
  {ψ : M →ₗ[R] (Fin k → A) // ∀ j, ψ (x j) = Pi.single j 1}

variable {R A}

noncomputable def theta (ψ : M →ₗ[R] (Fin k → A)) : (Fin k → M) →ₗ[R] A :=
  LinearMap.lsum R (fun _ : Fin k => M) R fun i => (LinearMap.proj i).comp ψ

lemma theta_single (ψ : M →ₗ[R] (Fin k → A)) (i : Fin k) (m : M) :
    theta ψ (Pi.single i m) = ψ m i := by
  classical
  simp only [theta, LinearMap.lsum_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp,
    LinearMap.coe_proj, Function.comp_apply, Function.eval]
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, Pi.zero_apply])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

lemma lift_theta_mem (ψ : HomX R x A) (a : SymmetricAlgebra R (Fin k → M))
    (ha : a ∈ Ideal.span (rels R x)) : SymmetricAlgebra.lift (theta ψ.1) a = 0 := by
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨i, j, rfl⟩ := h
    rw [map_sub, SymmetricAlgebra.lift_ι_apply, theta_single, ψ.2 j, Pi.single_apply]
    split_ifs <;> simp
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul r a _ ha => rw [smul_eq_mul, map_mul, ha, mul_zero]

noncomputable def toPt (ψ : HomX R x A) : S R x →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (SymmetricAlgebra.lift (theta ψ.1)) (lift_theta_mem x ψ)

lemma toPt_mk_ι (ψ : HomX R x A) (w : Fin k → M) :
    toPt x ψ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ w)) = theta ψ.1 w := by
  change SymmetricAlgebra.lift (theta ψ.1) (SymmetricAlgebra.ι R _ w) = _
  exact SymmetricAlgebra.lift_ι_apply _ _

lemma toPt_mk_ι_single (ψ : HomX R x A) (i : Fin k) (m : M) :
    toPt x ψ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))) = ψ.1 m i := by
  rw [toPt_mk_ι, theta_single]

noncomputable def ofPt (g : S R x →ₐ[R] A) : HomX R x A := by
  classical
  refine ⟨LinearMap.pi fun i =>
      (g.comp (Ideal.Quotient.mkₐ R _)).toLinearMap ∘ₗ SymmetricAlgebra.ι R (Fin k → M) ∘ₗ
        LinearMap.single R (fun _ : Fin k => M) i, fun j => ?_⟩
  funext i
  simp only [LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk, LinearMap.coe_single]
  have hmem : SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) - (if i = j then 1 else 0) ∈
      Ideal.span (rels R x) := Ideal.subset_span ⟨i, j, rfl⟩
  have h0 : g (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) -
      (if i = j then 1 else 0))) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
  rw [map_sub, map_sub, sub_eq_zero] at h0
  rw [h0, Pi.single_apply]
  split_ifs <;> simp

lemma ofPt_apply (g : S R x →ₐ[R] A) (m : M) (i : Fin k) :
    (ofPt x g).1 m i = g (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))) := by
  classical
  simp [ofPt]

lemma ofPt_toPt (ψ : HomX R x A) : ofPt x (toPt x ψ) = ψ := by
  apply Subtype.ext
  apply LinearMap.ext
  intro m
  funext i
  rw [ofPt_apply, toPt_mk_ι_single]

lemma toPt_ofPt (g : S R x →ₐ[R] A) : toPt x (ofPt x g) = g := by
  classical
  refine Ideal.Quotient.algHom_ext R (SymmetricAlgebra.algHom_ext ?_)
  refine LinearMap.pi_ext fun i m => ?_
  change toPt x (ofPt x g) (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))) =
    g (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m)))
  rw [toPt_mk_ι, theta_single, ofPt_apply]

noncomputable def homEquivPt : HomX R x A ≃ (S R x →ₐ[R] A) where
  toFun := toPt x
  invFun := ofPt x
  left_inv := ofPt_toPt x
  right_inv := toPt_ofPt x

variable {B : Type} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B)

lemma homEquivPt_natural (ψ : HomX R x A) (ψ' : HomX R x B) (h : ∀ m i, ψ'.1 m i = φ (ψ.1 m i)) :
    homEquivPt x ψ' = φ.comp (homEquivPt x ψ) := by
  classical
  refine Ideal.Quotient.algHom_ext R (SymmetricAlgebra.algHom_ext ?_)
  refine LinearMap.pi_ext fun i m => ?_
  change toPt x ψ' (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))) =
    φ (toPt x ψ (Ideal.Quotient.mk _ (SymmetricAlgebra.ι R _ (Pi.single i m))))
  rw [toPt_mk_ι_single, toPt_mk_ι_single, h]

end Module.Grassmannian.ChartAlgebra

open Module.Grassmannian.ChartAlgebra in
theorem Module.Grassmannian.exists_chart_equiv_algHom_symmetricAlgebra_quotient
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (k : ℕ) (x : Fin k → M) :
    ∃ (J : Ideal (SymmetricAlgebra R (Fin k → M)))
      (_ : J = Ideal.span {a | ∃ i j : Fin k,
        a = SymmetricAlgebra.ι R (Fin k → M) (Pi.single i (x j)) - if i = j then 1 else 0})
      (pt : ∀ (A : Type) [CommRing A] [Algebra R A],
        {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)} ≃
          (SymmetricAlgebra R (Fin k → M) ⧸ J →ₐ[R] A)),
      (∀ (A : Type) [CommRing A] [Algebra R A]
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)})
          (m : M),
          ∑ i, pt A N (Ideal.Quotient.mk J (SymmetricAlgebra.ι R (Fin k → M) (Pi.single i m))) •
              N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i) =
            N.1.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m)) ∧
      (∀ (A B : Type) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B)
          (N : {N : Module.Grassmannian A (A ⊗[R] M) k //
            Function.Bijective fun v : Fin k → A =>
              ∑ i, v i • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x i)}),
          ∃ h : Function.Bijective fun v : Fin k → B =>
              ∑ i, v i • (Module.Grassmannian.map φ N.1).toSubmodule.mkQ ((1 : B) ⊗ₜ[R] x i),
            pt B ⟨Module.Grassmannian.map φ N.1, h⟩ = φ.comp (pt A N)) := by
  obtain ⟨pt₁, hcoord, -, hnat⟩ := Module.Grassmannian.exists_chart_equiv_linearMap R M k x
  refine ⟨Ideal.span (rels R x), rfl, fun A _ _ => (pt₁ A).trans (homEquivPt (R := R) (A := A) x), ?_, ?_⟩
  · intro A _ _ N m
    have h := hcoord A N m
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
    congr 1
    exact toPt_mk_ι_single x (pt₁ A N) i m
  · intro A B _ _ _ _ φ N
    obtain ⟨h, hφ⟩ := hnat A B φ N
    exact ⟨h, homEquivPt_natural x φ (pt₁ A N) (pt₁ B ⟨_, h⟩) hφ⟩
