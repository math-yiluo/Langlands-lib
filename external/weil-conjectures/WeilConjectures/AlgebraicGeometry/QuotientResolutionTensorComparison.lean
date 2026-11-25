/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Augmented tensor comparisons for quotient resolutions
Source: Stacks Project, Tag 00LS.
(blueprint: new-p4-quotient-resolution-tensor-comparison). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restricted_resolution_lift
    (A C : Type u) [CommRing A] [CommRing C] (φ : A →+* C)
    (M : ModuleCat.{u} A) (N : ModuleCat.{u} C)
    (P : ProjectiveResolution M) (R : ProjectiveResolution N)
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    ∃ a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj R.complex,
      a.f 0 ≫ (ModuleCat.restrictScalars φ).map (R.π.f 0) = P.π.f 0 ≫ f := by
  classical
  let F := ModuleCat.restrictScalars φ
  let L := (F.mapHomologicalComplex (.down ℕ)).obj R.complex
  let e := F.map (R.π.f 0)
  let z := Projective.factorThru (P.π.f 0 ≫ f) e
  have hz : z ≫ e = P.π.f 0 ≫ f := Projective.factorThru_comp _ _
  have h₀ := R.exact₀.map F
  let o := h₀.liftFromProjective (P.complex.d 1 0 ≫ z) (by
    change (P.complex.d 1 0 ≫ z) ≫ e = 0
    rw [Category.assoc, hz, ← Category.assoc, P.complex_d_comp_π_f_zero,
      Limits.zero_comp])
  have ho : o ≫ L.d 1 0 = P.complex.d 1 0 ≫ z :=
    h₀.liftFromProjective_comp _ _
  let step : ∀ (n : ℕ)
      (p : Σ' (g : P.complex.X n ⟶ L.X n)
        (g' : P.complex.X (n + 1) ⟶ L.X (n + 1)),
        g' ≫ L.d (n + 1) n = P.complex.d (n + 1) n ≫ g),
      Σ' g'' : P.complex.X (n + 2) ⟶ L.X (n + 2),
        g'' ≫ L.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ p.2.1 := by
    intro n p
    have hn := (R.exact_succ n).map F
    let b := P.complex.d (n + 2) (n + 1) ≫ p.2.1
    have hb : b ≫ L.d (n + 1) n = 0 := by
      dsimp only [b]
      rw [Category.assoc, p.2.2, ← Category.assoc, HomologicalComplex.d_comp_d,
        Limits.zero_comp]
    exact ⟨hn.liftFromProjective b hb, hn.liftFromProjective_comp b hb⟩
  exact ⟨ChainComplex.mkHom P.complex L z o ho step, hz⟩

/-- A ring homomorphism carrying one ideal into another admits an augmented
comparison of the chosen quotient resolutions and the induced tensor complexes.
Source: Stacks Project, Tag 00LS, comparison of resolutions.
(blueprint: new-p4-quotient-resolution-tensor-comparison).

Proof: The ideal containment gives the quotient homomorphism ψ. Restrict the
augmented target resolution to A; restriction of scalars is exact, so it is
still an exact augmented complex. Inductively lift the quotient map from each
projective source term: degree zero lifts through the surjective augmentation,
degree one through its kernel, and degree j+1 through the cycles in degree j.
This constructs a with the required augmentation equation. Define k degreewise
by x tensor y mapping to a(x) tensor ψ(y). Compatibility of ψ with φ and
A-linearity of a prove the balancing relation. The chain equation for a proves
the chain equation for k on pure tensors, hence on all tensors by induction.
No flatness of φ or projectivity of the restricted target terms is needed.
The argument includes zero quotients and arbitrary commutative rings. -/
theorem exists_quotient_resolution_tensor_comparison
    (A C : Type u) [CommRing A] [CommRing C]
    (I : Ideal A) (J : Ideal C) (φ : A →+* C)
    (hI : ∀ x ∈ I, φ x ∈ J)
    (P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)))
    (R : ProjectiveResolution (ModuleCat.of C (C ⧸ J))) :
          let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)
          let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex
            (.down ℕ)
          ∃ (ψ : (A ⧸ I) →+* (C ⧸ J))
            (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) ∧
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) ∧
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) := by
  classical
  let ψ := Ideal.quotientMap J φ hI
  have hψ : ∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x) := by
    intro x
    rfl
  let b : (A ⧸ I) →ₛₗ[φ] (C ⧸ J) :=
    { toFun := ψ
      map_add' := ψ.map_add
      map_smul' := by
        intro r y
        change ψ (Ideal.Quotient.mk I r * y) = Ideal.Quotient.mk J (φ r) * ψ y
        rw [map_mul, hψ] }
  let f : ModuleCat.of A (A ⧸ I) ⟶
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of C (C ⧸ J)) :=
    ModuleCat.ofHom (X := ModuleCat.of A (A ⧸ I))
      (Y := (ModuleCat.restrictScalars φ).obj (ModuleCat.of C (C ⧸ J)))
      { toFun := b
        map_add' := b.map_add
        map_smul' := b.map_smul' }
  obtain ⟨a, ha⟩ := restricted_resolution_lift A C φ _ _ P R f
  let au (j : ℕ) : P.complex.X j →ₛₗ[φ] R.complex.X j :=
    { toFun := a.f j
      map_add' := (a.f j).hom.map_add
      map_smul' := (a.f j).hom.map_smul }
  let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex (.down ℕ)
  let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex (.down ℕ)
  let kf (j : ℕ) : (TA.obj P.complex).X j ⟶
      (ModuleCat.restrictScalars φ).obj ((TC.obj R.complex).X j) :=
    ModuleCat.ofHom (X := (TA.obj P.complex).X j)
      (Y := (ModuleCat.restrictScalars φ).obj ((TC.obj R.complex).X j))
      { toFun := TensorProduct.map (au j) b
        map_add' := (TensorProduct.map (au j) b).map_add
        map_smul' := (TensorProduct.map (au j) b).map_smul' }
  let k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
      (.down ℕ)).obj (TC.obj R.complex) :=
    { f := kf
      comm' := by
        intro j l hjl
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        change R.complex.d j l (a.f j x) ⊗ₜ[C] ψ y =
          (show R.complex.X l from a.f l (P.complex.d j l x)) ⊗ₜ[C] ψ y
        have h := congrArg (fun g ↦ g x) (a.comm j l)
        exact congrArg (fun z : R.complex.X l ↦ z ⊗ₜ[C] ψ y) h }
  refine ⟨ψ, a, k, hψ, ?_, ?_⟩
  · intro x
    exact (congrArg (fun g ↦ g x) ha)
  · intro j x y
    rfl

end AlgebraicGeometry
