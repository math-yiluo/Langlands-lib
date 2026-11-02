import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Faithfully flat finitely presented models

Stacks Project, Tag 034Y (Algebra, Lemma 10.168.2) and Tag 0367.
-/

universe u

open TensorProduct

namespace Langlands.Algebra

/-- The image of `Spec (S ⊗[R] T) → Spec S` contains every prime whose contraction to `R`
lies in the image of `Spec T → Spec R`. -/
theorem mem_range_comap_tensorProduct {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (P : PrimeSpectrum S)
    (hP : PrimeSpectrum.comap (algebraMap R S) P ∈
      Set.range (PrimeSpectrum.comap (algebraMap R T))) :
    P ∈ Set.range (PrimeSpectrum.comap (algebraMap S (S ⊗[R] T))) := by
  set p := PrimeSpectrum.comap (algebraMap R S) P
  rw [← PrimeSpectrum.nontrivial_iff_mem_rangeComap] at hP ⊢
  let φ : p.asIdeal.ResidueField →+* P.asIdeal.ResidueField :=
    Ideal.ResidueField.map p.asIdeal P.asIdeal (algebraMap R S) rfl
  let _ : Algebra p.asIdeal.ResidueField P.asIdeal.ResidueField := φ.toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField P.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply R S P.asIdeal.ResidueField]
      exact (Ideal.ResidueField.map_algebraMap p.asIdeal P.asIdeal (algebraMap R S) rfl r).symm
  have := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right
    (R := p.asIdeal.ResidueField) P.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] T)
    φ.injective
  exact ((Algebra.TensorProduct.cancelBaseChange R S P.asIdeal.ResidueField
      P.asIdeal.ResidueField T).trans
    (Algebra.TensorProduct.cancelBaseChange R p.asIdeal.ResidueField P.asIdeal.ResidueField
      P.asIdeal.ResidueField T).symm).toEquiv.nontrivial

/-- If `B ≃ A ⊗[A₀] B₀` is faithfully flat over `A` and `B₀` is flat and finitely presented over
`A₀`, then `1 = ∑ aᵢ yᵢ` in `A` with `yᵢ ∈ A₀` such that each `D(yᵢ) ⊆ Spec A₀` lies in the image
of `Spec B₀`. -/
theorem exists_sum_eq_one_of_faithfullyFlat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {A₀ B₀ : Type*} [CommRing A₀] [CommRing B₀] [Algebra A₀ A]
    [Algebra A₀ B₀] [Algebra.FinitePresentation A₀ B₀] [Module.Flat A₀ B₀]
    (e : A ⊗[A₀] B₀ ≃ₐ[A] B) :
    ∃ (n : ℕ) (a : Fin n → A) (y : Fin n → A₀),
      (∀ i (p : PrimeSpectrum A₀), y i ∉ p.asIdeal →
        p ∈ Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀))) ∧
      ∑ i, a i * algebraMap A₀ A (y i) = 1 := by
  -- The image `U` of `Spec B₀ → Spec A₀` is open, with closed complement `V(I)`.
  set U := Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀)) with hU_def
  have hU : IsOpen U :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation.isOpen_range
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Uᶜ).mp hU.isClosed_compl
  -- Every prime of `A` contracts into `U`, since `A → B ≃ A ⊗[A₀] B₀` is faithfully flat.
  have hmap (q : PrimeSpectrum A) : PrimeSpectrum.comap (algebraMap A₀ A) q ∈ U := by
    obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) q
    let g : B₀ →+* B := (e : A ⊗[A₀] B₀ →ₐ[A] B).toRingHom.comp
      (Algebra.TensorProduct.includeRight : B₀ →ₐ[A₀] A ⊗[A₀] B₀).toRingHom
    have hg : g.comp (algebraMap A₀ B₀) = (algebraMap A B).comp (algebraMap A₀ A) := by
      ext x
      simp only [g, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        AlgHom.commutes]
      exact e.commutes (algebraMap A₀ A x)
    refine ⟨PrimeSpectrum.comap g Q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, hg, PrimeSpectrum.comap_comp_apply, hQ]
  -- Hence `I` generates the unit ideal of `A`.
  have hItop : I.map (algebraMap A₀ A) = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    have h₂ : PrimeSpectrum.comap (algebraMap A₀ A) ⟨m, hm.isPrime⟩ ∈ Uᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus]
      exact Ideal.map_le_iff_le_comap.mp hle
    exact h₂ (hmap ⟨m, hm.isPrime⟩)
  have h1 : (1 : A) ∈ Submodule.span A (algebraMap A₀ A '' I) := by
    change (1 : A) ∈ I.map (algebraMap A₀ A)
    rw [hItop]
    exact Submodule.mem_top
  obtain ⟨n, a, x, hx⟩ := Submodule.mem_span_set'.mp h1
  choose y hyI hyx using fun i => (x i).2
  refine ⟨n, a, y, fun i p hp => ?_, ?_⟩
  · by_contra hc
    have hc' : p ∈ Uᶜ := hc
    rw [hI, PrimeSpectrum.mem_zeroLocus] at hc'
    exact hp (hc' (hyI i))
  · rw [← hx]
    exact Finset.sum_congr rfl fun i _ => by rw [hyx i, smul_eq_mul]

/-- Under the conclusion of `exists_sum_eq_one_of_faithfullyFlat`, the base change of `B₀` to
any `A₀`-algebra `A₁` in which `1 = ∑ aᵢ yᵢ` is faithfully flat. -/
theorem faithfullyFlat_tensorProduct_of_sum_eq_one {A₀ B₀ A₁ : Type*} [CommRing A₀]
    [CommRing B₀] [CommRing A₁] [Algebra A₀ B₀] [Algebra A₀ A₁] [Module.Flat A₀ B₀] {n : ℕ}
    (a : Fin n → A₁) (y : Fin n → A₀)
    (hy : ∀ i (p : PrimeSpectrum A₀), y i ∉ p.asIdeal →
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀)))
    (hsum : ∑ i, a i * algebraMap A₀ A₁ (y i) = 1) :
    Module.FaithfullyFlat A₁ (A₁ ⊗[A₀] B₀) := by
  refine Module.FaithfullyFlat.of_comap_surjective fun P => mem_range_comap_tensorProduct P ?_
  by_contra hc
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hsum]
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ ?_
  by_contra hi
  exact hc (hy i _ hi)

/-- **Stacks 034Y** (Algebra, Lemma 10.168.2), in the form used for Tag 0367: if `A → B` is
faithfully flat and `B ≃ A ⊗[A₀] B₀` for a flat, finitely presented algebra `B₀` over a finite
type `ℤ`-subalgebra `A₀ ⊆ A`, then for any ring `R → A` there is a finite type `R`-subalgebra
`A₁ ⊆ A` and a faithfully flat, finitely presented `A₁`-algebra `B₁` with `B ≃ A ⊗[A₁] B₁`. -/
theorem exists_faithfullyFlat_finitePresentation_model_of_flat_model
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Module.FaithfullyFlat A B] (A₀ : Subalgebra ℤ A) (B₀ : Type u) [CommRing B₀]
    [Algebra A₀ B₀] [Algebra.FiniteType ℤ A₀] [Algebra.FinitePresentation A₀ B₀]
    [Module.Flat A₀ B₀] (e : A ⊗[A₀] B₀ ≃ₐ[A] B) :
    ∃ (A₁ : Subalgebra R A) (B₁ : Type u) (_ : CommRing B₁) (_ : Algebra A₁ B₁),
      Algebra.FiniteType R A₁ ∧ Algebra.FinitePresentation A₁ B₁ ∧
        Module.FaithfullyFlat A₁ B₁ ∧ Nonempty (A ⊗[A₁] B₁ ≃ₐ[A] B) := by
  obtain ⟨n, a, y, hy, hsum⟩ := exists_sum_eq_one_of_faithfullyFlat e
  -- Enlarge `A₀` by generators and the coefficients `a i`.
  obtain ⟨t, ht⟩ := (Subalgebra.fg_iff_finiteType A₀).mpr inferInstance
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : Subalgebra R A, A₁ = Algebra.adjoin R (↑t ∪ Set.range a) := ⟨_, rfl⟩
  have hft : Algebra.FiniteType R A₁ := hA₁ ▸
    Algebra.FiniteType.adjoin_of_finite (t.finite_toSet.union (Set.finite_range a))
  have hle₀ : Algebra.adjoin ℤ (t : Set A) ≤ A₁.restrictScalars ℤ := by
    refine Algebra.adjoin_le fun w hw => ?_
    rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars, hA₁]
    exact Algebra.subset_adjoin (R := R) (Set.mem_union_left _ hw)
  have hle (z : A) (hz : z ∈ A₀) : z ∈ A₁ :=
    (Subalgebra.mem_restrictScalars ℤ).mp (hle₀ (ht ▸ hz))
  have ha (i : Fin n) : a i ∈ A₁ := by
    rw [hA₁]
    exact Algebra.subset_adjoin (R := R) (Set.mem_union_right _ ⟨i, rfl⟩)
  let φ : A₀ →+* A₁ := (algebraMap A₀ A).codRestrict A₁ fun z => hle z z.2
  let _ : Algebra A₀ A₁ := φ.toAlgebra
  have : IsScalarTower A₀ A₁ A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hff : Module.FaithfullyFlat A₁ (A₁ ⊗[A₀] B₀) := by
    refine faithfullyFlat_tensorProduct_of_sum_eq_one (fun i => ⟨a i, ha i⟩) y hy ?_
    apply Subtype.ext
    change A₁.val _ = A₁.val 1
    rw [map_sum, map_one, ← hsum]
    rfl
  have hfp : Algebra.FinitePresentation A₁ (A₁ ⊗[A₀] B₀) := inferInstance
  let e' : A ⊗[A₁] (A₁ ⊗[A₀] B₀) ≃ₐ[A] B :=
    (Algebra.TensorProduct.cancelBaseChange A₀ A₁ A A B₀).trans e
  exact ⟨A₁, A₁ ⊗[A₀] B₀, inferInstance, inferInstance, hft, hfp, hff, ⟨e'⟩⟩

/-- **Stacks 0367** (algebra form): let `R → A → B` be ring maps with `A → B` faithfully flat and
`R → B` of finite type. If `B` has a flat, finitely presented model `B ≃ A ⊗[A₀] B₀` over a finite
type `ℤ`-subalgebra `A₀ ⊆ A` (Stacks 10.168.1(1)), then `R → A` is of finite type. -/
theorem finiteType_of_faithfullyFlat_of_flat_model (R A B : Type u) [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FiniteType R B]
    (h : ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      Algebra.FiniteType ℤ A₀ ∧ Algebra.FinitePresentation A₀ B₀ ∧ Module.Flat A₀ B₀ ∧
        Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B)) :
    Algebra.FiniteType R A := by
  obtain ⟨A₀, B₀, _, _, _, _, _, ⟨e⟩⟩ := h
  obtain ⟨A₁, B₁, _, _, hA₁, _, _, ⟨e'⟩⟩ :=
    exists_faithfullyFlat_finitePresentation_model_of_flat_model R A B A₀ B₀ e
  have : IsScalarTower R A₁ B :=
    IsScalarTower.of_algebraMap_eq fun r => IsScalarTower.algebraMap_apply R A B r
  have : Algebra.FiniteType A₁ B := .of_restrictScalars_finiteType R A₁ B
  have : Algebra.FiniteType A₁ (B₁ ⊗[A₁] A) :=
    this.equiv ((e'.restrictScalars A₁).symm.trans (Algebra.TensorProduct.comm A₁ A B₁))
  have : Algebra.FiniteType B₁ (B₁ ⊗[A₁] A) := .of_restrictScalars_finiteType A₁ B₁ _
  have : Algebra.FiniteType A₁ A := .of_finiteType_tensorProduct_of_faithfullyFlat B₁
  exact hA₁.trans this

end Langlands.Algebra
