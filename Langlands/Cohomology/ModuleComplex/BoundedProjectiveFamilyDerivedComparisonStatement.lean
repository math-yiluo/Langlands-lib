import Langlands.Cohomology.PerfectModuleComplex

set_option autoImplicit false

universe u

open CategoryTheory TensorProduct

namespace Langlands.Cohomology.ModuleComplex

attribute [local instance] HasDerivedCategory.standard

/-- Convert one bounded finite projective family and explicit cycle tests into
derived comparisons, over the original ring and every scalar ring. -/
def BoundedProjectiveFamilyDerivedComparisonStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (K : ℕ → Type u) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    [∀ i, Module.Finite R (K i)] [∀ i, Module.Projective R (K i)]
    (δ : ∀ i, K i →ₗ[R] K (i + 1)) (_hδδ : ∀ i, δ (i + 1) ∘ₗ δ i = 0)
    (n : ℕ) (_hbound : ∀ i, n < i → Subsingleton (K i)),
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      IsStrictlyPerfect P ∧
      (∀ (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)]
        (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
        (φ : ∀ i, K i →ₗ[R] C i) (_hφ : ∀ i, d i ∘ₗ φ i = φ (i + 1) ∘ₗ δ i)
        (_h0inj : ∀ x : K 0, δ 0 x = 0 → φ 0 x = 0 → x = 0)
        (_h0surj : ∀ y : C 0, d 0 y = 0 → ∃ x : K 0, δ 0 x = 0 ∧ φ 0 x = y)
        (_hposinj : ∀ (i : ℕ) (x : K (i + 1)), δ (i + 1) x = 0 →
          φ (i + 1) x ∈ LinearMap.range (d i) → x ∈ LinearMap.range (δ i))
        (_hpossurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
          ∃ x : K (i + 1), δ (i + 1) x = 0 ∧
            φ (i + 1) x - y ∈ LinearMap.range (d i)),
        Nonempty (DerivedCategory.Q.obj P ≅
          DerivedCategory.Q.obj
            ((CochainComplex.of (fun i => ModuleCat.of R (C i))
              (fun i => ModuleCat.ofHom (d i)) (fun i => by
                apply ModuleCat.hom_ext
                exact hdd i)).extend ComplexShape.embeddingUpNat))) ∧
      ∀ (A : Type u) [CommRing A] (f : R →+* A),
        letI := f.toAlgebra
        ∀ (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module A (C i)]
          (d : ∀ i, C i →ₗ[A] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
          (Θ : ∀ i, A ⊗[R] K i →ₗ[A] C i)
          (_hΘ : ∀ i, Θ (i + 1) ∘ₗ (δ i).baseChange A = d i ∘ₗ Θ i)
          (_h0inj : ∀ x : A ⊗[R] K 0,
            (δ 0).baseChange A x = 0 → Θ 0 x = 0 → x = 0)
          (_h0surj : ∀ y : C 0, d 0 y = 0 →
            ∃ x : A ⊗[R] K 0, (δ 0).baseChange A x = 0 ∧ Θ 0 x = y)
          (_hposinj : ∀ (i : ℕ) (x : A ⊗[R] K (i + 1)),
            (δ (i + 1)).baseChange A x = 0 →
            Θ (i + 1) x ∈ LinearMap.range (d i) →
            x ∈ LinearMap.range ((δ i).baseChange A))
          (_hpossurj : ∀ (i : ℕ) (y : C (i + 1)), d (i + 1) y = 0 →
            ∃ x : A ⊗[R] K (i + 1), (δ (i + 1)).baseChange A x = 0 ∧
              Θ (i + 1) x - y ∈ LinearMap.range (d i)),
          Nonempty (DerivedCategory.Q.obj ((baseChange f).obj P) ≅
            DerivedCategory.Q.obj
              ((CochainComplex.of (fun i => ModuleCat.of A (C i))
                (fun i => ModuleCat.ofHom (d i)) (fun i => by
                  apply ModuleCat.hom_ext
                  exact hdd i)).extend ComplexShape.embeddingUpNat))

end Langlands.Cohomology.ModuleComplex
