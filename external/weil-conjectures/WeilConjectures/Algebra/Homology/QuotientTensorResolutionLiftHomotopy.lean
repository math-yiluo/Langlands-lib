/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # Homotopy independence of quotient tensor resolution lifts

Source: Stacks Project, Tag 00LS(2), projective lifting proof.
(blueprint: new-h2-quotient-tensor-resolution-lift-homotopy). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

namespace ModuleCat

private theorem prevD_chain
    {D : Type*} [Category D] [Preadditive D]
    {L M : ChainComplex D ℕ} (t : ∀ j l, L.X j ⟶ M.X l) (j : ℕ) :
    prevD j t = t j (j + 1) ≫ M.d (j + 1) j := by
  change t j ((ComplexShape.down ℕ).prev j) ≫ M.d ((ComplexShape.down ℕ).prev j) j = _
  rw [ChainComplex.prev]

private theorem augmented_lift_homotopy
    {D : Type*} [Category D] [Abelian D] {M N : D}
    (P : ProjectiveResolution M) (K : ChainComplex D ℕ) (π : K.X 0 ⟶ N)
    (hz : K.d 1 0 ≫ π = 0)
    (hzero : (ShortComplex.mk (K.d 1 0) π hz).Exact)
    (hsucc : ∀ n : ℕ,
      (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
        (K.d_comp_d _ _ _)).Exact)
    (a a' : P.complex ⟶ K) (haug : a.f 0 ≫ π = a'.f 0 ≫ π) :
    Nonempty (Homotopy a a') := by
  let f := a - a'
  have hf : f.f 0 ≫ π = 0 := by
    change (a.f 0 - a'.f 0) ≫ π = 0
    rw [Preadditive.sub_comp, haug, sub_self]
  let s₀ := hzero.liftFromProjective (f.f 0) hf
  have hs₀ : s₀ ≫ K.d 1 0 = f.f 0 := hzero.liftFromProjective_comp _ _
  have h₁ : (f.f 1 - P.complex.d 1 0 ≫ s₀) ≫ K.d 1 0 = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hs₀, f.comm, sub_self]
  let s₁ := (hsucc 0).liftFromProjective (f.f 1 - P.complex.d 1 0 ≫ s₀) h₁
  have hs₁ : s₁ ≫ K.d 2 1 = f.f 1 - P.complex.d 1 0 ≫ s₀ :=
    (hsucc 0).liftFromProjective_comp _ _
  refine ⟨Homotopy.equivSubZero.invFun
    (Homotopy.mkInductive f s₀ hs₀.symm s₁ ?_ ?_)⟩
  · exact (sub_eq_iff_eq_add.mp hs₁.symm).trans (add_comm _ _)
  · intro n data
    rcases data with ⟨g, g', hg⟩
    have hnext : (f.f (n + 2) - P.complex.d (n + 2) (n + 1) ≫ g') ≫
        K.d (n + 2) (n + 1) = 0 := by
      simp [hg]
    refine ⟨(hsucc (n + 1)).liftFromProjective _ hnext, ?_⟩
    have hc := (hsucc (n + 1)).liftFromProjective_comp _ hnext
    exact (sub_eq_iff_eq_add.mp hc.symm).trans (add_comm _ _)

private noncomputable def quotientTensorLift
    {A C : Type u} [CommRing A] [CommRing C]
    (I : Ideal A) (J : Ideal C) (φ : A →+* C) (ψ : (A ⧸ I) →+* (C ⧸ J))
    (hψ : ∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x))
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} C}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    (tensorRight (ModuleCat.of A (A ⧸ I))).obj M ⟶
      (ModuleCat.restrictScalars φ).obj ((tensorRight (ModuleCat.of C (C ⧸ J))).obj N) := by
  let f' : M →ₛₗ[φ] N :=
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := f.hom.map_smul }
  let ψ' : (A ⧸ I) →ₛₗ[φ] (C ⧸ J) :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := by
        intro r y
        change ψ (Ideal.Quotient.mk I r * y) = Ideal.Quotient.mk J (φ r) * ψ y
        rw [map_mul, hψ] }
  let t := TensorProduct.map f' ψ'
  exact ModuleCat.ofHom
    (X := (tensorRight (ModuleCat.of A (A ⧸ I))).obj M)
    (Y := (ModuleCat.restrictScalars φ).obj
      ((tensorRight (ModuleCat.of C (C ⧸ J))).obj N))
    { toFun := t
      map_add' := t.map_add
      map_smul' := t.map_smulₛₗ }

private theorem quotientTensorLift_tmul
    {A C : Type u} [CommRing A] [CommRing C]
    (I : Ideal A) (J : Ideal C) (φ : A →+* C) (ψ : (A ⧸ I) →+* (C ⧸ J))
    (hψ : ∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x))
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} C}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (x : M) (y : A ⧸ I) :
    quotientTensorLift I J φ ψ hψ f (x ⊗ₜ[A] y) =
      (show N from f x) ⊗ₜ[C] (ψ y) := rfl

/-- Two augmented lifts of the same quotient map induce homotopic quotient tensor maps,
even when restriction of scalars does not preserve projective objects.
Source: Stacks Project, Tag 00LS(2); its proof uses only the projective lifting property.
(blueprint: new-h2-quotient-tensor-resolution-lift-homotopy).

Proof: Restriction of scalars is exact, so the augmented complex Res(R) is
an exact resolution of Res(C/J); its terms need not be projective over A.
Subtract a' from a. The common augmentation equation says the difference in
degree zero lands in the augmentation kernel. Lift it through the differential
from Res(R_1) using projectivity of P_0. Inductively, subtract the already
constructed homotopy term from the difference in degree j. The chain-map
identity says the result lands in the kernel of the next differential.
Exactness of Res(R) and projectivity of P_j lift it to Res(R_{j+1}).
This constructs an A-linear homotopy H between a and a'. For each component
H_j define the A-linear tensor map x tensor y to H_j(x) tensor psi(y).
The quotient compatibility equation makes this balanced over A, since H_j is
A-linear into restriction of scalars. Extend by the tensor universal property.
The differential and addition identities on pure tensors show that these maps
form a homotopy between k and k', using their given pure tensor equations.
Pure tensors generate, so the identities hold on all tensors. This argument
also covers zero quotient rings and degree zero without additional assumptions. -/
theorem quotient_tensor_resolution_lift_homotopy
    {A C : Type u} [CommRing A] [CommRing C]
    (I : Ideal A) (J : Ideal C) (φ : A →+* C)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (R : ProjectiveResolution (ModuleCat.of C (C ⧸ J))) :
    let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
    let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex (.down ℕ)
    ∀ (ψ : (A ⧸ I) →+* (C ⧸ J))
      (a a' : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj R.complex)
      (k k' : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj (TC.obj R.complex)),
      (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) →
      (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) →
      (∀ x : P.complex.X 0, R.π.f 0 (a'.f 0 x) = ψ (P.π.f 0 x)) →
      (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
        k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) →
      (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
        k'.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a'.f j x) ⊗ₜ[C] (ψ y)) →
      Nonempty (Homotopy k k') := by
  intro TA TC ψ a a' k k' hψ ha ha' hk hk'
  let F := ModuleCat.restrictScalars φ
  let K := (F.mapHomologicalComplex (.down ℕ)).obj R.complex
  have hz : K.d 1 0 ≫ F.map (R.π.f 0) = 0 := by
    change F.map (R.complex.d 1 0) ≫ F.map (R.π.f 0) = 0
    rw [← F.map_comp, R.complex_d_comp_π_f_zero, F.map_zero]
  have hzero : (ShortComplex.mk (K.d 1 0) (F.map (R.π.f 0)) hz).Exact :=
    (R.exact₀).map F
  have hsucc (j : ℕ) :
      (ShortComplex.mk (K.d (j + 2) (j + 1)) (K.d (j + 1) j)
        (K.d_comp_d _ _ _)).Exact := (R.exact_succ j).map F
  have haug : a.f 0 ≫ F.map (R.π.f 0) = a'.f 0 ≫ F.map (R.π.f 0) := by
    ext x
    exact (ha x).trans (ha' x).symm
  obtain ⟨H⟩ := augmented_lift_homotopy P K _ hz hzero hsucc a a' haug
  let T : ∀ j l, (TA.obj P.complex).X j ⟶
      ((F.mapHomologicalComplex (.down ℕ)).obj (TC.obj R.complex)).X l :=
    fun j l ↦ quotientTensorLift I J φ ψ hψ (H.hom j l)
  refine ⟨{ hom := T, zero := ?_, comm := ?_ }⟩
  · intro j l hjl
    have h := H.zero j l hjl
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change quotientTensorLift I J φ ψ hψ (H.hom j l) (x ⊗ₜ[A] y) = 0
    rw [quotientTensorLift_tmul, h]
    exact TensorProduct.zero_tmul _ _
  · intro j
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    have hc := ConcreteCategory.congr_hom (H.comm j) x
    simp only [dNext_nat, prevD_chain] at hc ⊢
    change a.f j x = H.hom (j - 1) j (P.complex.d j (j - 1) x) +
      K.d (j + 1) j (H.hom j (j + 1) x) + a'.f j x at hc
    change k.f j (x ⊗ₜ[A] y) =
      T (j - 1) j ((TA.obj P.complex).d j (j - 1) (x ⊗ₜ[A] y)) +
      ((F.mapHomologicalComplex (.down ℕ)).obj (TC.obj R.complex)).d (j + 1) j
        (T j (j + 1) (x ⊗ₜ[A] y)) + k'.f j (x ⊗ₜ[A] y)
    rw [hk, hk']
    change (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y) =
      (show R.complex.X j from
        H.hom (j - 1) j (P.complex.d j (j - 1) x)) ⊗ₜ[C] (ψ y) +
      (R.complex.d (j + 1) j
        (show R.complex.X (j + 1) from H.hom j (j + 1) x)) ⊗ₜ[C] (ψ y) +
      (show R.complex.X j from a'.f j x) ⊗ₜ[C] (ψ y)
    rw [hc]
    simp only [TensorProduct.add_tmul]
    rfl

end ModuleCat
