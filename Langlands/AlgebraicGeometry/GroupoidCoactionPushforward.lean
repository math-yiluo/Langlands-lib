import Langlands.AlgebraicGeometry.GroupoidCoactionCocycleUniversal
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Pushforward along source-cartesian morphisms of affine relations -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

section RingLifts

variable {B C D S : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing S]
  [Algebra B C] [Algebra B D]

/-- The tensor-product lift of compatible ring maps, without a chosen algebra on the target. -/
def tensorRingLift (δ : D →+* S) (φ : C →+* S)
    (h : δ.comp (algebraMap B D) = φ.comp (algebraMap B C)) :
    D ⊗[B] C →+* S := by
  letI : Algebra B S := (δ.comp (algebraMap B D)).toAlgebra
  let δ' : D →ₐ[B] S := { δ with commutes' := fun _ => rfl }
  let φ' : C →ₐ[B] S :=
    { φ with commutes' := fun b => (congrArg (fun f : B →+* S => f b) h).symm }
  exact (Algebra.TensorProduct.lift δ' φ' fun _ _ => Commute.all _ _).toRingHom

@[simp]
lemma tensorRingLift_tmul (δ : D →+* S) (φ : C →+* S)
    (h : δ.comp (algebraMap B D) = φ.comp (algebraMap B C)) (d : D) (c : C) :
    tensorRingLift δ φ h (d ⊗ₜ[B] c) = δ d * φ c := rfl

end RingLifts

variable {B C D P : Type u} [CommRing B] [CommRing C] [CommRing D] [CommRing P]
  [Algebra B C] [Algebra B D] [Algebra D P]
variable (e : P ≃ₐ[D] D ⊗[B] C)

/-- The relation-ring map encoded by a source-cartesian square. -/
def cartesianBaseMap : C →+* P :=
  e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

@[simp]
lemma cartesianBaseMap_apply (c : C) :
    cartesianBaseMap e c = e.symm ((1 : D) ⊗ₜ[B] c) := rfl

@[simp]
lemma cartesianBaseMap_source (b : B) :
    cartesianBaseMap e (algebraMap B C b) = algebraMap D P (algebraMap B D b) := by
  apply e.injective
  simp [Algebra.TensorProduct.algebraMap_def]
  simpa only [Algebra.smul_def, mul_one] using
    (TensorProduct.smul_tmul (R := B) b (1 : D) (1 : C)).symm

lemma cartesianBaseMap_comp_source :
    (cartesianBaseMap e).comp (algebraMap B C) =
      (algebraMap D P).comp (algebraMap B D) := by
  ext b
  exact cartesianBaseMap_source e b

/-- A point of the base relation and a compatible point of the covering object give a
unique point of the covering relation. -/
def cartesianLift {S : Type u} [CommRing S] (δ : D →+* S) (φ : C →+* S)
    (h : δ.comp (algebraMap B D) = φ.comp (algebraMap B C)) : P →+* S :=
  (tensorRingLift δ φ h).comp e.toRingHom

@[simp]
lemma cartesianLift_symm_tmul {S : Type u} [CommRing S]
    (δ : D →+* S) (φ : C →+* S)
    (h : δ.comp (algebraMap B D) = φ.comp (algebraMap B C)) (d : D) (c : C) :
    cartesianLift e δ φ h (e.symm (d ⊗ₜ[B] c)) = δ d * φ c := by
  simp [cartesianLift]

@[simp]
lemma cartesianLift_source {S : Type u} [CommRing S]
    (δ : D →+* S) (φ : C →+* S)
    (h : δ.comp (algebraMap B D) = φ.comp (algebraMap B C)) :
    (cartesianLift e δ φ h).comp (algebraMap D P) = δ := by
  ext d
  change tensorRingLift δ φ h (e (algebraMap D P d)) = δ d
  rw [e.commutes]
  simp [Algebra.TensorProduct.algebraMap_def]

@[simp]
lemma cartesianLift_base {S : Type u} [CommRing S]
    (δ : D →+* S) (φ : C →+* S)
    (h : δ.comp (algebraMap B D) = φ.comp (algebraMap B C)) :
    (cartesianLift e δ φ h).comp (cartesianBaseMap e) = φ := by
  ext c
  simp

/-- The two maps in a source-cartesian square jointly determine a ring-valued point. -/
lemma cartesian_hom_ext {S : Type u} [CommRing S] {f g : P →+* S}
    (hD : f.comp (algebraMap D P) = g.comp (algebraMap D P))
    (hC : f.comp (cartesianBaseMap e) = g.comp (cartesianBaseMap e)) : f = g := by
  have hfg : f.comp e.symm.toRingHom = g.comp e.symm.toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul d c =>
      have hd := congrArg (fun k : D →+* S => k d) hD
      have hc := congrArg (fun k : C →+* S => k c) hC
      have hx : e.symm (d ⊗ₜ[B] c) =
          algebraMap D P d * cartesianBaseMap e c := by
        apply e.injective
        simp [Algebra.TensorProduct.algebraMap_def]
      change f (e.symm (d ⊗ₜ[B] c)) = g (e.symm (d ⊗ₜ[B] c))
      rw [hx, map_mul, map_mul]
      exact congrArg₂ (· * ·) hd hc
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  ext p
  simpa using congrArg (fun k : D ⊗[B] C →+* S => k (e p)) hfg

section PointLaws

variable {t : B →+* C} {td : D →+* P}
variable (hE : RingEtaleEquivalenceRelation t) (hP : RingEtaleEquivalenceRelation td)
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))

include hE hP ht in
/-- A lift of a diagonal base point is a diagonal covering point. -/
lemma cartesianLift_diagonal {S : Type u} [CommRing S]
    (δ : D →+* S) (φ : C →+* S)
    (hs : δ.comp (algebraMap B D) = φ.comp (algebraMap B C))
    (hφ : φ.comp t = δ.comp (algebraMap B D)) :
    (cartesianLift e δ φ hs).comp td = δ := by
  obtain ⟨ε, hεt, hεs⟩ := hP.refl S δ
  have hεbase : ε.comp (cartesianBaseMap e) = φ := by
    apply hE.hom_ext
    · rw [RingHom.comp_assoc, ht, ← RingHom.comp_assoc, hεt, hφ]
    · rw [RingHom.comp_assoc, cartesianBaseMap_comp_source,
        ← RingHom.comp_assoc, hεs, hs]
  have heq : cartesianLift e δ φ hs = ε := by
    apply cartesian_hom_ext e
    · rw [cartesianLift_source, hεs]
    · rw [cartesianLift_base, hεbase]
  rw [heq, hεt]

include hE hP ht in
/-- Composable lifts have the target required of the lifted composite. -/
lemma cartesian_composite_target {S : Type u} [CommRing S]
    (r₁ r₂ r₃ : P →+* S)
    (h : r₁.comp (algebraMap D P) = r₂.comp td)
    (hs : r₃.comp (algebraMap D P) = r₂.comp (algebraMap D P))
    (h₃ : (r₃.comp (cartesianBaseMap e)).comp t =
      (r₁.comp (cartesianBaseMap e)).comp t) :
    r₃.comp td = r₁.comp td := by
  obtain ⟨χ, hχt, hχs⟩ := hP.trans S r₁ r₂ h
  have hbase : χ.comp (cartesianBaseMap e) = r₃.comp (cartesianBaseMap e) := by
    apply hE.hom_ext
    · calc
        (χ.comp (cartesianBaseMap e)).comp t =
            (χ.comp td).comp (algebraMap B D) := by
              rw [RingHom.comp_assoc, ht, RingHom.comp_assoc]
        _ = (r₁.comp td).comp (algebraMap B D) := by rw [hχt]
        _ = (r₁.comp (cartesianBaseMap e)).comp t := by
          rw [RingHom.comp_assoc, ← ht, ← RingHom.comp_assoc]
        _ = (r₃.comp (cartesianBaseMap e)).comp t := h₃.symm
    · rw [RingHom.comp_assoc, RingHom.comp_assoc, cartesianBaseMap_comp_source,
        ← RingHom.comp_assoc, ← RingHom.comp_assoc, hχs, hs]
  have heq : χ = r₃ := cartesian_hom_ext e (hχs.trans hs.symm) hbase
  rw [← heq, hχt]

end PointLaws

section PointSpecialization

variable {S : Type u} [CommRing S] [Algebra B S]

/-- The source-preserving lift of a base point. -/
def cartesianPoint (φ : C →ₐ[B] S) : P →ₐ[D] D ⊗[B] S :=
  (Algebra.TensorProduct.map (AlgHom.id D D) φ).comp e.toAlgHom

@[simp]
lemma cartesianPoint_symm_tmul (φ : C →ₐ[B] S) (d : D) (c : C) :
    cartesianPoint e φ (e.symm (d ⊗ₜ[B] c)) = d ⊗ₜ[B] φ c := by
  simp [cartesianPoint]

@[simp]
lemma cartesianPoint_base (φ : C →ₐ[B] S) :
    (cartesianPoint e φ : P →+* D ⊗[B] S).comp (cartesianBaseMap e) =
      Algebra.TensorProduct.includeRight.toRingHom.comp (φ : C →+* S) := by
  ext c
  simp

variable {t : B →+* C} {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))

include ht in
lemma cartesianFirst_compat (φ₁ : C →+* S) (φ₂ : C →ₐ[B] S)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* S).comp t) :
    ((cartesianPoint e φ₂ : P →+* D ⊗[B] S).comp td).comp (algebraMap B D) =
      (Algebra.TensorProduct.includeRight.toRingHom.comp φ₁).comp (algebraMap B C) := by
  rw [RingHom.comp_assoc, ← ht, ← RingHom.comp_assoc, cartesianPoint_base,
    RingHom.comp_assoc, ← h, RingHom.comp_assoc]

/-- Lift the first of two composable base points using the target of the lifted second. -/
def cartesianFirst (φ₁ : C →+* S) (φ₂ : C →ₐ[B] S)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* S).comp t) : P →+* D ⊗[B] S :=
  cartesianLift e ((cartesianPoint e φ₂ : P →+* D ⊗[B] S).comp td)
    (Algebra.TensorProduct.includeRight.toRingHom.comp φ₁)
    (cartesianFirst_compat e ht φ₁ φ₂ h)

@[simp]
lemma cartesianFirst_source (φ₁ : C →+* S) (φ₂ : C →ₐ[B] S)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* S).comp t) :
    (cartesianFirst e ht φ₁ φ₂ h).comp (algebraMap D P) =
      (cartesianPoint e φ₂ : P →+* D ⊗[B] S).comp td := by
  exact cartesianLift_source e _ _ _

@[simp]
lemma cartesianFirst_base (φ₁ : C →+* S) (φ₂ : C →ₐ[B] S)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* S).comp t) :
    (cartesianFirst e ht φ₁ φ₂ h).comp (cartesianBaseMap e) =
      Algebra.TensorProduct.includeRight.toRingHom.comp φ₁ := by
  exact cartesianLift_base e _ _ _

include ht in
lemma cartesianPoint_diagonal (hE : RingEtaleEquivalenceRelation t)
    (hP : RingEtaleEquivalenceRelation td) (φ : C →ₐ[B] S)
    (hφ : (φ : C →+* S).comp t = algebraMap B S) :
    (cartesianPoint e φ : P →+* D ⊗[B] S).comp td = algebraMap D (D ⊗[B] S) := by
  have hs : (algebraMap D (D ⊗[B] S)).comp (algebraMap B D) =
      (Algebra.TensorProduct.includeRight.toRingHom.comp (φ : C →+* S)).comp
        (algebraMap B C) := by
    ext b
    simp [Algebra.TensorProduct.algebraMap_def, Algebra.algebraMap_eq_smul_one, smul_tmul]
  have hφ' : (Algebra.TensorProduct.includeRight.toRingHom.comp (φ : C →+* S)).comp t =
      (algebraMap D (D ⊗[B] S)).comp (algebraMap B D) := by
    rw [RingHom.comp_assoc, hφ]
    ext b
    simp [Algebra.TensorProduct.algebraMap_def, Algebra.algebraMap_eq_smul_one, smul_tmul]
  have heq : cartesianLift e (algebraMap D (D ⊗[B] S))
      (Algebra.TensorProduct.includeRight.toRingHom.comp (φ : C →+* S)) hs =
      (cartesianPoint e φ : P →+* D ⊗[B] S) := by
    apply cartesian_hom_ext e
    · ext d
      simp
    · rw [cartesianLift_base, cartesianPoint_base]
  rw [← heq]
  exact cartesianLift_diagonal e hE hP ht _ _ hs hφ'

include ht in
lemma cartesianPoint_composite_target (hE : RingEtaleEquivalenceRelation t)
    (hP : RingEtaleEquivalenceRelation td)
    (φ₁ : C →+* S) (φ₂ φ₃ : C →ₐ[B] S)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* S).comp t)
    (h₃ : (φ₃ : C →+* S).comp t = φ₁.comp t) :
    (cartesianPoint e φ₃ : P →+* D ⊗[B] S).comp td =
      (cartesianFirst e ht φ₁ φ₂ h).comp td := by
  apply cartesian_composite_target e hE hP ht (cartesianFirst e ht φ₁ φ₂ h)
    (cartesianPoint e φ₂) (cartesianPoint e φ₃)
    (cartesianFirst_source e ht φ₁ φ₂ h)
  · ext d
    simp
  · rw [cartesianPoint_base, cartesianFirst_base, RingHom.comp_assoc, h₃,
      RingHom.comp_assoc]

end PointSpecialization

section TensorComparison

variable [Algebra B P] [IsScalarTower B D P]
variable {M : Type v} [AddCommGroup M] [Module D M] [Module B M]
  [IsScalarTower B D M]
variable (S : Type u) [CommRing S] [Algebra B S]

/-- Cancel the covering object-ring factor in a module tensor. -/
def cartesianCancel :
    (D ⊗[B] S) ⊗[D] M ≃ₗ[B] S ⊗[B] M :=
  ((TensorProduct.comm D (D ⊗[B] S) M).restrictScalars B).trans
    (((AlgebraTensorModule.cancelBaseChange B D D M S).restrictScalars B).trans
      (TensorProduct.comm B M S))

@[simp]
lemma cartesianCancel_tmul (d : D) (s : S) (m : M) :
    cartesianCancel (D := D) S ((d ⊗ₜ[B] s) ⊗ₜ[D] m) = s ⊗ₜ[B] (d • m) := rfl

@[simp]
lemma cartesianCancel_symm_tmul (s : S) (m : M) :
    (cartesianCancel (D := D) (M := M) S).symm (s ⊗ₜ[B] m) =
      ((1 : D) ⊗ₜ[B] s) ⊗ₜ[D] m := rfl

variable {S}

lemma cartesianCancel_smul (s : S) (x : (D ⊗[B] S) ⊗[D] M) :
    cartesianCancel (D := D) S (((1 : D) ⊗ₜ[B] s) • x) =
      s • cartesianCancel (D := D) S x := by
  induction x using TensorProduct.inductionOn with
  | tmul y m =>
    induction y using TensorProduct.inductionOn with
    | tmul d a =>
      simp [smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, smul_eq_mul]
    | add y z hy hz => simp_all [add_tmul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- The tensor comparison used to restrict a covering coaction to the base object ring. -/
def pushforwardTensorEquiv : P ⊗[D] M ≃ₗ[B] C ⊗[B] M :=
  ((e.toLinearEquiv.rTensor M).restrictScalars B).trans (cartesianCancel C)

@[simp]
lemma pushforwardTensorEquiv_tmul (d : D) (c : C) (m : M) :
    pushforwardTensorEquiv e (e.symm (d ⊗ₜ[B] c) ⊗ₜ[D] m) =
      c ⊗ₜ[B] (d • m) := by
  simp [pushforwardTensorEquiv]

@[simp]
lemma pushforwardTensorEquiv_symm_tmul (c : C) (m : M) :
    (pushforwardTensorEquiv (M := M) e).symm (c ⊗ₜ[B] m) =
      cartesianBaseMap e c ⊗ₜ[D] m := rfl

@[simp]
lemma pushforwardTensorEquiv_base_tmul (c : C) (m : M) :
    pushforwardTensorEquiv e (cartesianBaseMap e c ⊗ₜ[D] m) = c ⊗ₜ[B] m := by
  change pushforwardTensorEquiv e (e.symm ((1 : D) ⊗ₜ[B] c) ⊗ₜ[D] m) = _
  simp

lemma pushforwardTensorEquiv_base_smul (c : C) (x : P ⊗[D] M) :
    pushforwardTensorEquiv e (cartesianBaseMap e c • x) =
      c • pushforwardTensorEquiv e x := by
  obtain ⟨y, rfl⟩ := (pushforwardTensorEquiv (M := M) e).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul a m =>
    simp only [pushforwardTensorEquiv_symm_tmul, smul_tmul', smul_eq_mul, ← map_mul,
      pushforwardTensorEquiv_base_tmul]
  | add x y hx hy =>
    simpa only [map_add, smul_add] using congrArg₂ (· + ·) hx hy

/-- Tensor cancellation commutes with specializing a base relation point. -/
lemma pushforwardTensorEquiv_specialize (φ : C →ₐ[B] S) (x : P ⊗[D] M) :
    cartesianCancel (D := D) S
        (LinearMap.rTensor M (cartesianPoint e φ).toLinearMap x) =
      LinearMap.rTensor M φ.toLinearMap (pushforwardTensorEquiv e x) := by
  obtain ⟨y, rfl⟩ := (e.toLinearEquiv.rTensor M).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul z m =>
    induction z using TensorProduct.inductionOn with
    | tmul d c => simp
    | add x y hx hy => simp_all [add_tmul]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

variable {t : B →+* C} {td : D →+* P}
variable (ht : (cartesianBaseMap e).comp t = td.comp (algebraMap B D))
variable (θ : GroupoidCoaction td M)

/-- The additive coaction on the underlying base module. -/
def pushforwardCoactionMap : M →+ C ⊗[B] M :=
  (pushforwardTensorEquiv e).toAddMonoidHom.comp θ.coaction

@[simp]
lemma pushforwardCoactionMap_apply (m : M) :
    pushforwardCoactionMap e θ m = pushforwardTensorEquiv e (θ.coaction m) := rfl

include ht in
lemma pushforwardCoactionMap_smul (b : B) (m : M) :
    pushforwardCoactionMap e θ (b • m) =
      t b • pushforwardCoactionMap e θ m := by
  change pushforwardTensorEquiv e (θ.coaction (b • m)) = _
  rw [← IsScalarTower.algebraMap_smul D b m, θ.map_smul]
  have hb : cartesianBaseMap e (t b) = td (algebraMap B D b) := RingHom.congr_fun ht b
  rw [← hb, pushforwardTensorEquiv_base_smul]
  rfl

lemma pushforwardTensorEquiv_compose
    (φ₁ : C →+* S) (φ₂ : C →ₐ[B] S)
    (h : φ₁.comp (algebraMap B C) = (φ₂ : C →+* S).comp t) (x : P ⊗[D] M) :
    cartesianCancel (D := D) S
        (coactionCompose td M θ.coaction θ.map_smul
          (cartesianFirst e ht φ₁ φ₂ h) (cartesianPoint e φ₂)
          (cartesianFirst_source e ht φ₁ φ₂ h) x) =
      coactionCompose t M (pushforwardCoactionMap e θ)
        (pushforwardCoactionMap_smul e ht θ) φ₁ φ₂ h (pushforwardTensorEquiv e x) := by
  obtain ⟨y, rfl⟩ := (pushforwardTensorEquiv (M := M) e).symm.surjective x
  induction y using TensorProduct.inductionOn with
  | tmul c m =>
    have hc : cartesianFirst e ht φ₁ φ₂ h (cartesianBaseMap e c) =
        (1 : D) ⊗ₜ[B] φ₁ c :=
      RingHom.congr_fun (cartesianFirst_base e ht φ₁ φ₂ h) c
    rw [pushforwardTensorEquiv_symm_tmul, pushforwardTensorEquiv_base_tmul]
    change cartesianCancel (D := D) S
        (cartesianFirst e ht φ₁ φ₂ h (cartesianBaseMap e c) •
          LinearMap.rTensor M (cartesianPoint e φ₂).toLinearMap (θ.coaction m)) =
      φ₁ c • LinearMap.rTensor M φ₂.toLinearMap (pushforwardCoactionMap e θ m)
    rw [hc, cartesianCancel_smul, pushforwardTensorEquiv_specialize]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Push a covering coaction to the base module along a source-cartesian ring square. -/
def pushforward (hE : RingEtaleEquivalenceRelation t)
    (hP : RingEtaleEquivalenceRelation td) : GroupoidCoaction t M where
  coaction := pushforwardCoactionMap e θ
  map_smul := pushforwardCoactionMap_smul e ht θ
  counit S _ _ φ hφ m := by
    rw [pushforwardCoactionMap_apply, ← pushforwardTensorEquiv_specialize,
      θ.counit (D ⊗[B] S) (cartesianPoint e φ) (cartesianPoint_diagonal e ht hE hP φ hφ)]
    simp [Algebra.TensorProduct.one_def]
  coassoc S _ _ φ₁ φ₂ φ₃ h h₃ m := by
    rw [pushforwardCoactionMap_apply, ← pushforwardTensorEquiv_specialize,
      θ.coassoc (D ⊗[B] S) (cartesianFirst e ht φ₁ φ₂ h)
        (cartesianPoint e φ₂) (cartesianPoint e φ₃)
        (cartesianFirst_source e ht φ₁ φ₂ h)
        (cartesianPoint_composite_target e ht hE hP φ₁ φ₂ φ₃ h h₃)]
    exact pushforwardTensorEquiv_compose e ht θ φ₁ φ₂ h (θ.coaction m)

end TensorComparison

end Langlands.AlgebraicGeometry.GroupoidCoaction
