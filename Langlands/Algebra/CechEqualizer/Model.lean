import Langlands.Algebra.CechEqualizer.Good
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

open TensorProduct

namespace Langlands.Algebra.CechEqualizer

variable {A₀ A : Type*} [CommRing A₀] [CommRing A] [Algebra A₀ A]

/-- Over a noetherian ring `A₀`, every associated prime of an `A₀`-algebra `A` (viewed as an
`A₀`-module) is the contraction of a prime ideal of `A`. -/
lemma exists_comap_eq_of_mem_associatedPrimes [IsNoetherianRing A₀] (q : Ideal A₀)
    (hq : q ∈ associatedPrimes A₀ A) :
    ∃ P : Ideal A, P.IsPrime ∧ P.comap (algebraMap A₀ A) = q := by
  obtain ⟨hprime, a, rfl⟩ := isAssociatedPrime_iff.mp hq
  let I : Ideal A := (⊥ : Submodule A A).colon {a}
  have hI : I.comap (algebraMap A₀ A) = (⊥ : Submodule A₀ A).colon {a} := by
    ext x
    simp [I, Submodule.mem_colon_singleton, Algebra.smul_def]
  obtain ⟨P, hP, -, hPq⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes (algebraMap A₀ A)
    ((⊥ : Submodule A₀ A).colon {a}) (I := I)
    (by rw [hI, Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
  exact ⟨P, hP, hPq⟩

variable {C₀ C₁ C₀' C₁' : Type*} [CommRing C₀] [CommRing C₁] [Algebra A C₀] [Algebra A C₁]
  [CommRing C₀'] [CommRing C₁'] [Algebra A₀ C₀'] [Algebra A₀ C₁']
  {δ₁ δ₂ : C₀ →ₐ[A] C₁} {d : C₀' →ₗ[A₀] C₁'} {e₀ : A ⊗[A₀] C₀' ≃ₗ[A] C₀}
  {e₁ : A ⊗[A₀] C₁' →ₗ[A] C₁}

/-- The fibre hypothesis at a prime `P` of `A` makes the residue field `κ(P)` good for `d`. -/
lemma good_residueField (he₀ : e₀ (1 ⊗ₜ 1) = 1)
    (hde : ∀ y, e₁ (d.lTensor A y) = δ₁ (e₀ y) - δ₂ (e₀ y)) (P : Ideal A) [P.IsPrime]
    (hP : ∀ x : P.ResidueField ⊗[A] C₀,
      Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₁ x =
        Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₂ x →
      x ∈ Set.range (algebraMap P.ResidueField (P.ResidueField ⊗[A] C₀))) :
    Good d P.ResidueField := by
  let K := P.ResidueField
  let c₀ := TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ A A K C₀'
  let c₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange A₀ A A K C₁'
  let f₀ : K ⊗[A₀] C₀' →ₗ[A] K ⊗[A] C₀ :=
    (e₀.lTensor K).toLinearMap ∘ₗ c₀.symm.toLinearMap
  let f₁ : K ⊗[A₀] C₁' →ₗ[A] K ⊗[A] C₁ :=
    e₁.lTensor K ∘ₗ c₁.symm.toLinearMap
  have hf : ∀ y, f₁ (d.lTensor K y) =
      Algebra.TensorProduct.map (AlgHom.id A K) δ₁ (f₀ y) -
        Algebra.TensorProduct.map (AlgHom.id A K) δ₂ (f₀ y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul k c =>
      have := hde (1 ⊗ₜ c)
      simp only [LinearMap.lTensor_tmul] at this
      simp [f₀, f₁, c₀, c₁, this, tmul_sub]
    | add y y' hy hy' => simp only [map_add, hy, hy']; abel
  intro y hy
  obtain ⟨k, hk⟩ := hP (f₀ y) (sub_eq_zero.mp (by rw [← hf, hy, map_zero]))
  refine ⟨k, ?_⟩
  have he₀' : e₀.symm 1 = 1 ⊗ₜ 1 := by rw [LinearEquiv.symm_apply_eq, he₀]
  have : f₀ (k ⊗ₜ 1) = f₀ y := by
    rw [← hk]
    simp [f₀, c₀, he₀, Algebra.TensorProduct.algebraMap_apply]
  have hinj : Function.Injective f₀ := (c₀.symm.trans (e₀.lTensor K)).injective
  exact hinj this

/-- **Noetherian model criterion.** Suppose that, over a noetherian ring `A₀ → A`, the Čech pair
`δ₁, δ₂ : C₀ → C₁` is the base change of a linear map `d : C₀' → C₁'` between a faithfully flat
`A₀`-algebra and a flat `A₀`-algebra (via `e₀` and an injective `e₁`). If every fibre equalizer is
the residue field, then the equalizer of `δ₁, δ₂` is `A`. -/
theorem mem_range_of_model [IsNoetherianRing A₀] [Module.FaithfullyFlat A₀ C₀']
    [Module.Flat A₀ C₁'] (hd : d 1 = 0) (he₀ : ∀ a, e₀ (a ⊗ₜ 1) = algebraMap A C₀ a)
    (he₁ : Function.Injective e₁) (hde : ∀ y, e₁ (d.lTensor A y) = δ₁ (e₀ y) - δ₂ (e₀ y))
    (hfib : ∀ (P : Ideal A) [P.IsPrime] (x : P.ResidueField ⊗[A] C₀),
      Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₁ x =
        Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₂ x →
      x ∈ Set.range (algebraMap P.ResidueField (P.ResidueField ⊗[A] C₀)))
    (c : C₀) (hc : δ₁ c = δ₂ c) : c ∈ Set.range (algebraMap A C₀) := by
  have he₀1 : e₀ (1 ⊗ₜ 1) = 1 := by rw [he₀, map_one]
  have hA : Good d A := by
    refine good_of_associatedPrimes hd fun q _ hq => ?_
    obtain ⟨P, hP, rfl⟩ := exists_comap_eq_of_mem_associatedPrimes q hq
    have hκ := good_residueField he₀1 hde P (hfib P)
    exact good_of_injective
      (f := (Ideal.ResidueField.mapₐ (P.comap (algebraMap A₀ A)) P (Algebra.ofId A₀ A)
        rfl).toLinearMap) (RingHom.injective _) hκ
  obtain ⟨a, ha⟩ := hA (e₀.symm c) (he₁ (by rw [hde, LinearEquiv.apply_symm_apply, hc,
    sub_self, map_zero]))
  exact ⟨a, by rw [← he₀, ha, LinearEquiv.apply_symm_apply]⟩

end Langlands.Algebra.CechEqualizer
