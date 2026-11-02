import Langlands.Algebra.FlatFinitePresentationModel
import Langlands.Algebra.FaithfullyFlatFinitePresentationModel
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability

/-!
# Descent of finite presentation along a faithfully flat map on the source

Stacks Project, Tag 02KK (Descent, Lemma 35.14.1), finite presentation case.
-/

universe u

open TensorProduct

namespace Langlands.Algebra

/-- The descent step: given a finitely presented `R`-algebra `T` sitting between a ring `A₀`
and `A`, together with elements of `T` witnessing that the image of `Spec T → Spec A₀` lies in
the image of `Spec B₀ → Spec A₀`, finite presentation of `R → A ⊗[A₀] B₀` descends to
`R → A`. -/
theorem finitePresentation_of_finitePresentation_cover (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Algebra.FinitePresentation R B]
    {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] [Algebra A₀ A] [Algebra A₀ B₀]
    [Algebra.FinitePresentation A₀ B₀] [Module.Flat A₀ B₀] (e : A ⊗[A₀] B₀ ≃ₐ[A] B)
    {n : ℕ} (y : Fin n → A₀)
    (hy : ∀ i (p : PrimeSpectrum A₀), y i ∉ p.asIdeal →
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀)))
    (T : Type u) [CommRing T] [Algebra R T] [Algebra A₀ T] [Algebra T A]
    [IsScalarTower R T A] [IsScalarTower A₀ T A] [Algebra.FinitePresentation R T]
    (x : Fin n → T) (hx : ∑ i, x i * algebraMap A₀ T (y i) = 1) :
    Algebra.FinitePresentation R A := by
  -- `Q = T ⊗[A₀] B₀` is faithfully flat and finitely presented over `T`.
  have hQff : Module.FaithfullyFlat T (T ⊗[A₀] B₀) :=
    faithfullyFlat_tensorProduct_of_sum_eq_one x y hy hx
  -- `B ≃ A ⊗[T] Q`.
  let ψ : A ⊗[T] (T ⊗[A₀] B₀) ≃ₐ[A] B :=
    (Algebra.TensorProduct.cancelBaseChange A₀ T A A B₀).trans e
  let g : T ⊗[A₀] B₀ →+* B := ψ.toRingHom.comp
    (Algebra.TensorProduct.includeRight : T ⊗[A₀] B₀ →ₐ[T] A ⊗[T] (T ⊗[A₀] B₀)).toRingHom
  let f : R →+* T ⊗[A₀] B₀ := (algebraMap T (T ⊗[A₀] B₀)).comp (algebraMap R T)
  have hgf : g.comp f = algebraMap R B := by
    ext r
    change ψ (Algebra.TensorProduct.includeRight
      (algebraMap T (T ⊗[A₀] B₀) (algebraMap R T r))) = algebraMap R B r
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply T A (A ⊗[T] (T ⊗[A₀] B₀)),
      AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply R T A,
      ← IsScalarTower.algebraMap_apply R A B]
  have hf : f.FiniteType :=
    (RingHom.FiniteType.of_finitePresentation
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)).comp
      (RingHom.FiniteType.of_finitePresentation
        (RingHom.finitePresentation_algebraMap.mpr inferInstance))
  have hg : g.FinitePresentation := RingHom.FinitePresentation.of_comp_finiteType f
    (by rw [hgf]; exact RingHom.finitePresentation_algebraMap.mpr inferInstance) hf
  have H : (Algebra.TensorProduct.includeRight.toRingHom :
      T ⊗[A₀] B₀ →+* A ⊗[T] (T ⊗[A₀] B₀)).FinitePresentation := by
    have : (Algebra.TensorProduct.includeRight.toRingHom :
        T ⊗[A₀] B₀ →+* A ⊗[T] (T ⊗[A₀] B₀)) = (ψ.symm.toRingEquiv.toRingHom).comp g :=
      RingHom.ext fun z => (ψ.symm_apply_apply _).symm
    rw [this]
    exact (RingHom.FinitePresentation.of_bijective ψ.symm.bijective).comp hg
  -- Descend along `T → Q`, then compose with `R → T`.
  have hTA : (algebraMap T A).FinitePresentation :=
    RingHom.FinitePresentation.codescendsAlong_faithfullyFlat.includeRight _ T A
      (T ⊗[A₀] B₀)
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hQff) H
  rw [← RingHom.finitePresentation_algebraMap, IsScalarTower.algebraMap_eq R T A]
  exact hTA.comp (RingHom.finitePresentation_algebraMap.mpr inferInstance)

/-- The descent step with an explicit finitely presented `R`-algebra `S` mapping to `A` and
receiving `A₀`: the ring `T = S[X₁, …, Xₙ] / (∑ Xᵢ yᵢ - 1)` satisfies the hypotheses of
`finitePresentation_of_finitePresentation_cover`. -/
theorem finitePresentation_of_finitePresentation_cover_of_sum (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Algebra.FinitePresentation R B]
    {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] [Algebra A₀ A] [Algebra A₀ B₀]
    [Algebra.FinitePresentation A₀ B₀] [Module.Flat A₀ B₀] (e : A ⊗[A₀] B₀ ≃ₐ[A] B)
    {n : ℕ} (a : Fin n → A) (y : Fin n → A₀)
    (hy : ∀ i (p : PrimeSpectrum A₀), y i ∉ p.asIdeal →
      p ∈ Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀)))
    (hsum : ∑ i, a i * algebraMap A₀ A (y i) = 1)
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (ι : A₀ →+* S) (χ : S →+* A) (hχR : χ.comp (algebraMap R S) = algebraMap R A)
    (hχι : χ.comp ι = algebraMap A₀ A) :
    Algebra.FinitePresentation R A := by
  -- `T = S[X₁, …, Xₙ] / (∑ Xᵢ yᵢ - 1)`, finitely presented over `R`.
  let ι' : A₀ →+* MvPolynomial (Fin n) S := MvPolynomial.C.comp ι
  let rel : MvPolynomial (Fin n) S := ∑ i, MvPolynomial.X i * ι' (y i) - 1
  let ψ₀ : MvPolynomial (Fin n) S →+* A := MvPolynomial.eval₂Hom χ a
  have hψ₀ι (z : A₀) : ψ₀ (ι' z) = algebraMap A₀ A z := by
    simp only [ψ₀, ι', RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
    exact RingHom.congr_fun hχι z
  have hrel : ψ₀ rel = 0 := by
    simp only [rel, map_sub, map_sum, map_mul, map_one, hψ₀ι, ψ₀, MvPolynomial.eval₂Hom_X']
    rw [sub_eq_zero]
    exact hsum
  let φ : MvPolynomial (Fin n) S ⧸ Ideal.span {rel} →+* A :=
    Ideal.Quotient.lift _ ψ₀ fun x hx => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, hrel, mul_zero]
  let _ : Algebra A₀ (MvPolynomial (Fin n) S ⧸ Ideal.span {rel}) :=
    ((Ideal.Quotient.mk _).comp ι').toAlgebra
  let _ : Algebra (MvPolynomial (Fin n) S ⧸ Ideal.span {rel}) A := φ.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) S ⧸ Ideal.span {rel}) A :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap R A r = φ (Ideal.Quotient.mk _ (MvPolynomial.C (algebraMap R S r)))
      simp only [φ, Ideal.Quotient.lift_mk, ψ₀, MvPolynomial.eval₂Hom_C]
      exact (RingHom.congr_fun hχR r).symm
  have : IsScalarTower A₀ (MvPolynomial (Fin n) S ⧸ Ideal.span {rel}) A :=
    IsScalarTower.of_algebraMap_eq fun z => by
      change algebraMap A₀ A z = φ (Ideal.Quotient.mk _ (ι' z))
      simp only [φ, Ideal.Quotient.lift_mk, hψ₀ι]
  have : Algebra.FinitePresentation R (MvPolynomial (Fin n) S ⧸ Ideal.span {rel}) :=
    have : Algebra.FinitePresentation R (MvPolynomial (Fin n) S) := .trans R S _
    .quotient (Submodule.fg_span_singleton rel)
  refine finitePresentation_of_finitePresentation_cover R A B e y hy
    (MvPolynomial (Fin n) S ⧸ Ideal.span {rel})
    (fun i => Ideal.Quotient.mk _ (MvPolynomial.X i)) ?_
  rw [← sub_eq_zero]
  change ∑ i, Ideal.Quotient.mk _ (MvPolynomial.X i) * Ideal.Quotient.mk _ (ι' (y i)) -
    Ideal.Quotient.mk (Ideal.span {rel}) 1 = 0
  simp only [← map_mul, ← map_sum, ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)

/-- **Stacks 02KK** (Descent, Lemma 35.14.1), finite presentation case, algebra form: let
`R → A → B` be ring maps with `A → B` faithfully flat and of finite presentation. If `R → B` is of
finite presentation, then so is `R → A`. -/
theorem finitePresentation_of_faithfullyFlat_of_finitePresentation (R A B : Type u)
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B]
    [Algebra.FinitePresentation R B] : Algebra.FinitePresentation R A := by
  obtain ⟨A₀, B₀, _, _, hA₀, _, _, ⟨e⟩⟩ :=
    exists_flat_finitePresentation_model A B inferInstance inferInstance
  obtain ⟨n, a, y, hy, hsum⟩ := exists_sum_eq_one_of_faithfullyFlat e
  have : Algebra.FinitePresentation ℤ A₀ := Algebra.FinitePresentation.of_finiteType.mp hA₀
  let χ : R ⊗[ℤ] A₀ →ₐ[ℤ] A :=
    Algebra.TensorProduct.productMap (algebraMap R A).toIntAlgHom A₀.val
  refine finitePresentation_of_finitePresentation_cover_of_sum R A B e a y hy hsum
    (R ⊗[ℤ] A₀) Algebra.TensorProduct.includeRight.toRingHom χ.toRingHom ?_ ?_
  · ext r
    simp [χ, Algebra.TensorProduct.productMap_apply_tmul]
  · ext z
    simp [χ, Algebra.TensorProduct.productMap_apply_tmul]

end Langlands.Algebra
