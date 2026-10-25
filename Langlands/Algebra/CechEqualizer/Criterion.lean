import Langlands.Algebra.CechEqualizer.Model
import Langlands.Algebra.CechEqualizer.Descent
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

universe u

open TensorProduct

namespace Langlands.Algebra.CechEqualizer

/-- The map `B₀ → C₀` coming from an identification `C₀ ≃ A ⊗[R₀] B₀` is compatible with the
structure maps from `R₀`. -/
lemma includeRight_comp_algebraMap {R₀ A B₀ C₀ : Type*} [CommRing R₀] [CommRing A] [CommRing B₀]
    [CommRing C₀] [Algebra R₀ A] [Algebra R₀ B₀] [Algebra A C₀] (ε : C₀ ≃ₐ[A] A ⊗[R₀] B₀) :
    (ε.symm.toAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := R₀) (A := A) (B := B₀)).toRingHom).comp
      (algebraMap R₀ B₀) = (algebraMap A C₀).comp (algebraMap R₀ A) := by
  ext r
  have : (1 : A) ⊗ₜ[R₀] algebraMap R₀ B₀ r = algebraMap A (A ⊗[R₀] B₀) (algebraMap R₀ A r) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one (A := B₀), Algebra.algebraMap_eq_smul_one (A := A)]
    exact (TensorProduct.smul_tmul r (1 : A) (1 : B₀)).symm
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  rw [this]
  exact ε.symm.commutes _

section Model

variable {R A₀ A B C : Type*} [CommRing R] [CommRing A₀] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A₀] [Algebra R A] [Algebra A₀ A] [IsScalarTower R A₀ A] [Algebra R B] [Algebra A C]


lemma modelEquiv_tmul (ε : C ≃ₐ[A] A ⊗[R] B) (a : A) (z : A₀ ⊗[R] B) :
    modelEquiv A₀ ε (a ⊗ₜ z) =
      a • ε.symm (Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R B) z) := by
  rw [modelEquiv, AlgEquiv.trans_apply, cancelBaseChange_tmul_eq_smul, map_smul]

lemma modelEquiv_tmul_one (ε : C ≃ₐ[A] A ⊗[R] B) (a : A) :
    (modelEquiv A₀ ε).toLinearEquiv (a ⊗ₜ 1) = algebraMap A C a := by
  have h : (a ⊗ₜ[A₀] (1 : A₀ ⊗[R] B)) = algebraMap A (A ⊗[A₀] (A₀ ⊗[R] B)) a := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [AlgEquiv.toLinearEquiv_apply, h]
  exact (modelEquiv A₀ ε).commutes a

end Model

/-- **Descent step.** Suppose `δ₁, δ₂ : C₀ → C₁` are, after the identifications
`C₀ ≃ A ⊗[R₀] B₀` and `C₁ ≃ A ⊗[R₁] B₁`, the base changes of `A₀`-algebra maps
`φ₁, φ₂ : A₀ ⊗[R₀] B₀ → A₀ ⊗[R₁] B₁` over a noetherian ring `A₀ ⊆ A`. If `A₀ ⊗[R₀] B₀` is
faithfully flat over `A₀`, `B₁` is flat over `R₁` and all fibre equalizers are scalars, then the
equalizer of `δ₁, δ₂` is `A`. -/
lemma mem_range_of_descent {R₀ R₁ A₀ A B₀ B₁ C₀ C₁ : Type*} [CommRing R₀] [CommRing R₁]
    [CommRing A₀] [CommRing A] [CommRing B₀] [CommRing B₁] [CommRing C₀] [CommRing C₁]
    [Algebra R₀ A₀] [Algebra R₀ A] [Algebra A₀ A] [IsScalarTower R₀ A₀ A] [Algebra R₀ B₀]
    [Algebra R₁ A₀] [Algebra R₁ A] [IsScalarTower R₁ A₀ A] [Algebra R₁ B₁]
    [Algebra A C₀] [Algebra A C₁] [IsNoetherianRing A₀] [Module.FaithfullyFlat A₀ (A₀ ⊗[R₀] B₀)]
    [Module.Flat R₁ B₁] (δ₁ δ₂ : C₀ →ₐ[A] C₁) (ε₀ : C₀ ≃ₐ[A] A ⊗[R₀] B₀)
    (ε₁ : C₁ ≃ₐ[A] A ⊗[R₁] B₁) (φ₁ φ₂ : A₀ ⊗[R₀] B₀ →ₐ[A₀] A₀ ⊗[R₁] B₁)
    (hφ₁ : ∀ x, ε₁.symm (Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R₁ B₁) (φ₁ x)) =
      δ₁ (ε₀.symm (Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R₀ B₀) x)))
    (hφ₂ : ∀ x, ε₁.symm (Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R₁ B₁) (φ₂ x)) =
      δ₂ (ε₀.symm (Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R₀ B₀) x)))
    (hfib : ∀ (P : Ideal A) [P.IsPrime] (x : P.ResidueField ⊗[A] C₀),
      Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₁ x =
        Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₂ x →
      x ∈ Set.range (algebraMap P.ResidueField (P.ResidueField ⊗[A] C₀)))
    (c : C₀) (hc : δ₁ c = δ₂ c) : c ∈ Set.range (algebraMap A C₀) := by
  let d : A₀ ⊗[R₀] B₀ →ₗ[A₀] A₀ ⊗[R₁] B₁ := φ₁.toLinearMap - φ₂.toLinearMap
  have hd : d 1 = 0 := by
    change φ₁ 1 - φ₂ 1 = 0
    rw [map_one, map_one, sub_self]
  have hde : ∀ y, (modelEquiv A₀ ε₁).toLinearEquiv.toLinearMap (d.lTensor A y) =
      δ₁ ((modelEquiv A₀ ε₀).toLinearEquiv y) - δ₂ ((modelEquiv A₀ ε₀).toLinearEquiv y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a z =>
      change modelEquiv A₀ ε₁ (a ⊗ₜ (φ₁ z - φ₂ z)) =
        δ₁ (modelEquiv A₀ ε₀ (a ⊗ₜ z)) - δ₂ (modelEquiv A₀ ε₀ (a ⊗ₜ z))
      rw [tmul_sub, map_sub, modelEquiv_tmul, modelEquiv_tmul, modelEquiv_tmul, hφ₁, hφ₂,
        map_smul, map_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, map_add]; abel
  exact mem_range_of_model hd (modelEquiv_tmul_one ε₀) (modelEquiv A₀ ε₁).injective hde hfib c hc

/-- **Fibrewise Čech criterion.** Let `δ₁, δ₂ : C₀ → C₁` be maps of smooth `A`-algebras with `C₀`
faithfully flat over `A`. If, over the residue field of every prime of `A`, the equalizer of the
base-changed maps consists of scalars, then the equalizer of `δ₁` and `δ₂` consists of elements
of `A`. -/
theorem mem_range_of_smooth {A C₀ C₁ : Type u} [CommRing A] [CommRing C₀] [CommRing C₁]
    [Algebra A C₀] [Algebra A C₁] (δ₁ δ₂ : C₀ →ₐ[A] C₁) [Algebra.Smooth A C₀]
    [Algebra.Smooth A C₁] [Module.FaithfullyFlat A C₀]
    (hfib : ∀ (P : Ideal A) [P.IsPrime] (x : P.ResidueField ⊗[A] C₀),
      Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₁ x =
        Algebra.TensorProduct.map (AlgHom.id A P.ResidueField) δ₂ x →
      x ∈ Set.range (algebraMap P.ResidueField (P.ResidueField ⊗[A] C₀)))
    (c : C₀) (hc : δ₁ c = δ₂ c) : c ∈ Set.range (algebraMap A C₀) := by
  classical
  -- Descend `C₀` and `C₁` to smooth algebras over finitely generated subrings `R₀`, `R₁` of `A`.
  obtain ⟨R₀, B₀, _, _, ⟨t₀, ht₀⟩, _, ⟨ε₀⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A C₀
  obtain ⟨R₁, B₁, _, _, ⟨t₁, ht₁⟩, _, ⟨ε₁⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A C₁
  -- The image of `Spec B₀ → Spec R₀` is open and contains the image of `Spec A`.
  have hU : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap R₀ B₀))) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation.isOpen_range
  have hcov : ∀ P : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap R₀ A) P ∈
      Set.range (PrimeSpectrum.comap (algebraMap R₀ B₀)) := by
    intro P
    obtain ⟨Q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := C₀) P
    refine ⟨PrimeSpectrum.comap (ε₀.symm.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R₀) (A := A) (B := B₀)).toRingHom) Q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      includeRight_comp_algebraMap]
  obtain ⟨s, cf, hs, hcf⟩ := exists_sum_eq_one_of_isOpen hU hcov
  -- Generators of `B₀` and the coefficients of their images in `A ⊗[R₁] B₁`.
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R₀) (A := B₀)
  have hex : ∀ (δ : C₀ →ₐ[A] C₁) (g : B₀), ∃ S : Finset (A × B₁),
      ε₁ (δ (ε₀.symm (1 ⊗ₜ g))) = ∑ i ∈ S, i.1 ⊗ₜ[R₁] i.2 :=
    fun δ g => TensorProduct.exists_finset _
  choose S hS using hex
  let T₂ : Finset A := t.biUnion fun g => (S δ₁ g ∪ S δ₂ g).image Prod.fst
  -- The noetherian model `A₀ ⊆ A`.
  let A₀ : Subalgebra ℤ A := Algebra.adjoin ℤ (↑(t₀ ∪ t₁ ∪ s.image cf ∪ T₂) : Set A)
  have hmem : ∀ x ∈ t₀ ∪ t₁ ∪ s.image cf ∪ T₂, x ∈ A₀ := fun x hx =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr hx)
  have h₀ : R₀ ≤ A₀ := by
    rw [← ht₀]
    exact Algebra.adjoin_le fun x hx => hmem x (by simp [Finset.mem_coe.mp hx])
  have h₁ : R₁ ≤ A₀ := by
    rw [← ht₁]
    exact Algebra.adjoin_le fun x hx => hmem x (by simp [Finset.mem_coe.mp hx])
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp ⟨_, rfl⟩
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let _ : Algebra R₀ A₀ := (Subalgebra.inclusion h₀).toRingHom.toAlgebra
  let _ : Algebra R₁ A₀ := (Subalgebra.inclusion h₁).toRingHom.toAlgebra
  have : IsScalarTower R₀ A₀ A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R₁ A₀ A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap A₀ A) := Subtype.val_injective
  -- The maps `δᵢ` descend to `A₀ ⊗[R₀] B₀ → A₀ ⊗[R₁] B₁`.
  let ι₀ := Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R₀ B₀)
  let ι₁ := Algebra.TensorProduct.map (Algebra.ofId A₀ A) (AlgHom.id R₁ B₁)
  let Ψ (δ : C₀ →ₐ[A] C₁) : A₀ ⊗[R₀] B₀ →ₐ[A₀] A ⊗[R₁] B₁ :=
    ((ε₁.toAlgHom.comp (δ.comp ε₀.symm.toAlgHom)).restrictScalars A₀).comp ι₀
  have hΨ : ∀ δ, (δ = δ₁ ∨ δ = δ₂) → ∀ g ∈ (t : Set B₀), Ψ δ (1 ⊗ₜ g) ∈ ι₁.range := by
    intro δ hδ g hg
    have h1 : ι₀ (1 ⊗ₜ g) = 1 ⊗ₜ g := by
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    have : Ψ δ (1 ⊗ₜ g) = ε₁ (δ (ε₀.symm (1 ⊗ₜ g))) := by
      change ε₁ (δ (ε₀.symm (ι₀ (1 ⊗ₜ g)))) = _
      rw [h1]
    rw [this, hS]
    refine sum_tmul_mem_range _ fun i hi => ⟨⟨i.1, hmem _ ?_⟩, rfl⟩
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨g, Finset.mem_coe.mp hg, ?_⟩)
    refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
    rcases hδ with rfl | rfl
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ hi
  have hdesc : ∀ δ, (δ = δ₁ ∨ δ = δ₂) → ∃ φ : A₀ ⊗[R₀] B₀ →ₐ[A₀] A₀ ⊗[R₁] B₁, ∀ x,
      ε₁.symm (ι₁ (φ x)) = δ (ε₀.symm (ι₀ x)) := by
    intro δ hδ
    obtain ⟨φ, hφ⟩ := exists_algHom_comp_eq ι₁ (map_ofId_injective hinj) (Ψ δ) _ ht (hΨ δ hδ)
    refine ⟨φ, fun x => ?_⟩
    rw [hφ]
    exact ε₁.symm_apply_apply _
  obtain ⟨φ₁, hφ₁⟩ := hdesc δ₁ (Or.inl rfl)
  obtain ⟨φ₂, hφ₂⟩ := hdesc δ₂ (Or.inr rfl)
  -- Faithful flatness of the model `A₀ ⊗[R₀] B₀` over `A₀`.
  let cf' : R₀ → A₀ := fun x => if hx : x ∈ s then
    ⟨cf x, hmem _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image_of_mem cf hx)))⟩ else 0
  have : Module.FaithfullyFlat A₀ (A₀ ⊗[R₀] B₀) := by
    refine faithfullyFlat_of_sum_eq_one s cf' hs ?_
    apply hinj
    rw [map_sum, map_one, ← hcf]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply]
    simp [cf', hx]
  exact mem_range_of_descent δ₁ δ₂ ε₀ ε₁ φ₁ φ₂ hφ₁ hφ₂ hfib c hc

end Langlands.Algebra.CechEqualizer
