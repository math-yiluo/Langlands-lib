import Langlands.CommutativeAlgebra.IntegralFibre.Transfer
import Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_exists_fg_subalgebra_flat_tensorProduct
import Mathlib.RingTheory.Extension.Presentation.Core

/-! # Noetherian models of a section with coordinates -/

open TensorProduct

universe u

namespace Langlands.CommutativeAlgebra.IntegralFibre

section ModelMaps

variable {C B B₀ T : Type*} [CommRing C] [CommRing B] [CommRing B₀] [CommRing T] [Algebra C B]
  [Algebra C B₀] [Algebra B T] (eT : B ⊗[C] B₀ ≃ₐ[B] T) (R₁ : Subalgebra C B)

/-- The model isomorphism `B ⊗[R₁] (R₁ ⊗[C] B₀) ≃ T`. -/
noncomputable def modelE : B ⊗[R₁] (R₁ ⊗[C] B₀) ≃ₐ[B] T :=
  (Algebra.TensorProduct.cancelBaseChange C R₁ B B B₀).trans eT

lemma modelMap_modelE_tmul (r : R₁) (w : B₀) :
    modelMap (modelE eT R₁) (r ⊗ₜ w) = eT ((r : B) ⊗ₜ w) := by
  rw [modelMap_apply, modelE, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_tmul,
    Algebra.smul_def, mul_one]
  rfl

lemma exists_modelMap_eq (z : T) {K : ℕ} (b : Fin K → B) (w : Fin K → B₀)
    (hz : eT.symm z = ∑ k, b k ⊗ₜ w k) (hb : ∀ k, b k ∈ R₁) :
    ∃ z₀, modelMap (modelE eT R₁) z₀ = z := by
  refine ⟨∑ k, (⟨b k, hb k⟩ : R₁) ⊗ₜ w k, ?_⟩
  rw [map_sum]
  simp only [modelMap_modelE_tmul]
  rw [← map_sum, ← hz, AlgEquiv.apply_symm_apply]

lemma modelMap_modelE_injective [Module.Flat R₁ (R₁ ⊗[C] B₀)] :
    Function.Injective (modelMap (modelE eT R₁)) := by
  intro x y hxy
  rw [modelMap_apply, modelMap_apply] at hxy
  have h1 := (modelE eT R₁).injective hxy
  have hinj : Function.Injective ((Algebra.linearMap R₁ B).rTensor (R₁ ⊗[C] B₀)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have h2 : (Algebra.linearMap R₁ B).rTensor (R₁ ⊗[C] B₀) (1 ⊗ₜ x) =
      (Algebra.linearMap R₁ B).rTensor (R₁ ⊗[C] B₀) (1 ⊗ₜ y) := by
    simpa using h1
  have h3 := hinj h2
  simpa using congrArg (TensorProduct.lid R₁ _) h3

end ModelMaps

section Kernel

variable {A T : Type*} [CommRing A] [CommRing T] (ι : A →+* T) (ρ : T →+* A)

lemma sub_mem_mul_of (I : Ideal T) {x y : T}
    (hx : x - ι (ρ x) ∈ I) (hy : y - ι (ρ y) ∈ I) : x * y - ι (ρ (x * y)) ∈ I := by
  have : x * y - ι (ρ (x * y)) = (x - ι (ρ x)) * y + ι (ρ x) * (y - ι (ρ y)) := by
    rw [map_mul, map_mul]; ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hx) (Ideal.mul_mem_left _ _ hy)

lemma sub_mem_add_of (I : Ideal T) {x y : T}
    (hx : x - ι (ρ x) ∈ I) (hy : y - ι (ρ y) ∈ I) : x + y - ι (ρ (x + y)) ∈ I := by
  have : x + y - ι (ρ (x + y)) = (x - ι (ρ x)) + (y - ι (ρ y)) := by
    rw [map_add, map_add]; ring
  rw [this]
  exact Ideal.add_mem _ hx hy

lemma sub_mem_of_section (I : Ideal T) (hρι : ∀ a, ρ (ι a) = a) (a : A) :
    ι a - ι (ρ (ι a)) ∈ I := by
  rw [hρι, sub_self]
  exact Ideal.zero_mem _

lemma sub_mem_span_of_adjoin {C A B₀ : Type*} [CommRing C] [CommRing A] [CommRing B₀]
    [Algebra C A] [Algebra C B₀] (ρ : A ⊗[C] B₀ →+* A)
    (hρ : ∀ a, ρ (Algebra.TensorProduct.includeLeftRingHom a) = a) {κ : Type*} (v : κ → B₀)
    (hv : Algebra.adjoin C (Set.range v) = ⊤) (x : A ⊗[C] B₀) :
    x - Algebra.TensorProduct.includeLeftRingHom (ρ x) ∈
      Ideal.span (Set.range fun j ↦ (1 : A) ⊗ₜ[C] v j -
        Algebra.TensorProduct.includeLeftRingHom (ρ ((1 : A) ⊗ₜ[C] v j))) := by
  set ι' : A →+* A ⊗[C] B₀ := Algebra.TensorProduct.includeLeftRingHom
  set I := Ideal.span (Set.range fun j ↦ (1 : A) ⊗ₜ[C] v j - ι' (ρ ((1 : A) ⊗ₜ[C] v j)))
  have h1 : ∀ w : B₀, (1 : A) ⊗ₜ[C] w - ι' (ρ ((1 : A) ⊗ₜ[C] w)) ∈ I := by
    intro w
    have hw : w ∈ Algebra.adjoin C (Set.range v) := hv ▸ Algebra.mem_top
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap c =>
      have : (1 : A) ⊗ₜ[C] algebraMap C B₀ c = ι' (algebraMap C A c) := by
        change _ = algebraMap C A c ⊗ₜ[C] (1 : B₀)
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rw [this]
      exact sub_mem_of_section ι' ρ I hρ _
    | add x y _ _ hx hy =>
      rw [TensorProduct.tmul_add]
      exact sub_mem_add_of ι' ρ I hx hy
    | mul x y _ _ hx hy =>
      rw [show (1 : A) ⊗ₜ[C] (x * y) = ((1 : A) ⊗ₜ[C] x) * ((1 : A) ⊗ₜ[C] y) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]]
      exact sub_mem_mul_of ι' ρ I hx hy
  induction x with
  | tmul a w =>
    rw [show a ⊗ₜ[C] w = ι' a * ((1 : A) ⊗ₜ[C] w) by
      change _ = (a ⊗ₜ[C] (1 : B₀)) * _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    exact sub_mem_mul_of ι' ρ I (sub_mem_of_section ι' ρ I hρ a) (h1 w)
  | add x y hx hy => exact sub_mem_add_of ι' ρ I hx hy

lemma ker_le_of_lifts {S₀ T : Type*} [CommRing S₀] [CommRing T] {κ : Type*} {d : ℕ}
    (φ : S₀ →+* T) (hφ : Function.Injective φ) (J₀ : Ideal S₀) (J : Ideal T)
    (hJJ : ∀ z, φ z ∈ J → z ∈ J₀) (ŷ : κ → S₀) (hgen : J₀ ≤ Ideal.span (Set.range ŷ))
    (t₀ : Fin d → S₀) (â : κ → Fin d → S₀) (L : κ → ℕ) (m₀ m₀' : ∀ j, Fin (L j) → S₀)
    (hm : ∀ j l, φ (m₀ j l) ∈ J) (hm' : ∀ j l, φ (m₀' j l) ∈ J)
    (heq : ∀ j, φ (ŷ j) = ∑ i, φ (â j i) * φ (t₀ i) + ∑ l, φ (m₀ j l) * φ (m₀' j l)) :
    J₀ ≤ Ideal.span (Set.range t₀) ⊔ J₀ * J₀ := by
  refine hgen.trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  have h : ŷ j = ∑ i, â j i * t₀ i + ∑ l, m₀ j l * m₀' j l := by
    apply hφ
    rw [heq j, map_add, map_sum, map_sum]
    simp only [map_mul]
  rw [SetLike.mem_coe, h]
  exact Submodule.add_mem_sup
    (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
    (Ideal.sum_mem _ fun l _ ↦ Ideal.mul_mem_mul (hJJ _ (hm j l)) (hJJ _ (hm' j l)))

lemma ker_le_of_model {C A B₀ T : Type*} [CommRing C] [CommRing A] [CommRing B₀] [CommRing T]
    [Algebra C A] [Algebra C B₀] {κ : Type*} (v : κ → B₀)
    (hv : Algebra.adjoin C (Set.range v) = ⊤) (σ₀ : A ⊗[C] B₀ →ₐ[A] A)
    (hρ : ∀ a, σ₀ (Algebra.TensorProduct.includeLeftRingHom a) = a)
    (φ : A ⊗[C] B₀ →+* T) (hφ : Function.Injective φ) (J : Ideal T)
    (hJJ : ∀ z, φ z ∈ J → z ∈ RingHom.ker σ₀) {d : ℕ} (t₀ : Fin d → A ⊗[C] B₀)
    (â : κ → Fin d → A ⊗[C] B₀) (L : κ → ℕ) (m₀ m₀' : ∀ j, Fin (L j) → A ⊗[C] B₀)
    (hm : ∀ j l, φ (m₀ j l) ∈ J) (hm' : ∀ j l, φ (m₀' j l) ∈ J)
    (heq : ∀ j, φ ((1 : A) ⊗ₜ[C] v j - Algebra.TensorProduct.includeLeftRingHom
      (σ₀ ((1 : A) ⊗ₜ[C] v j))) = ∑ i, φ (â j i) * φ (t₀ i) + ∑ l, φ (m₀ j l) * φ (m₀' j l)) :
    RingHom.ker σ₀ ≤ Ideal.span (Set.range t₀) ⊔ RingHom.ker σ₀ * RingHom.ker σ₀ := by
  refine ker_le_of_lifts φ hφ (RingHom.ker σ₀) J hJJ
    (fun j ↦ (1 : A) ⊗ₜ[C] v j - Algebra.TensorProduct.includeLeftRingHom
      (σ₀.toRingHom ((1 : A) ⊗ₜ[C] v j))) ?_ t₀ â L m₀ m₀' hm hm' heq
  intro x hx
  have h1 := sub_mem_span_of_adjoin σ₀.toRingHom hρ v hv x
  have hx' : σ₀.toRingHom x = 0 := RingHom.mem_ker.mp hx
  rw [hx', map_zero, sub_zero] at h1
  exact h1

end Kernel

section Main

/-- A flat finitely presented algebra with a section and coordinates `t` generating the kernel
modulo its square has a flat Noetherian model over a finitely generated subring of the base. -/
theorem exists_noetherianModel {B T : Type u} [CommRing B] [CommRing T] [Algebra B T]
    [Algebra.FinitePresentation B T] [Module.Flat B T] (σ : T →ₐ[B] B) {d : ℕ} (t : Fin d → T)
    (hJ : RingHom.ker σ ≤ Ideal.span (Set.range t) ⊔ RingHom.ker σ ^ 2) :
    ∃ (R₀ S₀ : Type u) (_ : CommRing R₀) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : Algebra R₀ B)
      (_ : IsNoetherianRing R₀) (_ : IsNoetherianRing S₀) (_ : Module.Flat R₀ S₀)
      (e : B ⊗[R₀] S₀ ≃ₐ[B] T) (σ₀ : S₀ →ₐ[R₀] R₀) (t₀ : Fin d → S₀),
      Function.Injective (algebraMap R₀ B) ∧
      (∀ x, algebraMap R₀ B (σ₀ x) = σ (modelMap e x)) ∧
      (∀ i, modelMap e (t₀ i) = t i) ∧
      RingHom.ker σ₀ ≤ Ideal.span (Set.range t₀) ⊔ RingHom.ker σ₀ * RingHom.ker σ₀ := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation B T
  let eT : B ⊗[P.Core] P.ModelOfHasCoeffs P.Core ≃ₐ[B] T := P.tensorModelOfHasCoeffsEquiv P.Core
  have hflatB : Module.Flat B (B ⊗[P.Core] P.ModelOfHasCoeffs P.Core) :=
    Module.Flat.of_linearEquiv eT.toLinearEquiv
  -- representations of elements of `T` over the model
  have rep : ∀ z : T, ∃ (K : ℕ) (b : Fin K → B) (w : Fin K → P.ModelOfHasCoeffs P.Core),
      eT.symm z = ∑ k, b k ⊗ₜ w k := fun z ↦ TensorProduct.exists_sum_tmul_eq _
  choose K b w hbw using rep
  let coeffs : T → Finset B := fun z ↦ Finset.univ.image (b z)
  -- witnesses for `hJ` on the generators
  let y : Fin (Algebra.Presentation.ofFinitePresentationVars B T) → T :=
    fun j ↦ P.val j - algebraMap B T (σ (P.val j))
  have hy : ∀ j, y j ∈ RingHom.ker σ := fun j ↦ by
    simp [y, RingHom.mem_ker]
  have wit : ∀ j, ∃ (a : Fin d → T) (L : ℕ) (m m' : Fin L → T), (∀ l, m l ∈ RingHom.ker σ) ∧
      (∀ l, m' l ∈ RingHom.ker σ) ∧ y j = ∑ i, a i * t i + ∑ l, m l * m' l := by
    intro j
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (hJ (hy j))
    obtain ⟨a, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
    rw [pow_two] at hv
    have : ∃ (L : ℕ) (m m' : Fin L → T), (∀ l, m l ∈ RingHom.ker σ) ∧
        (∀ l, m' l ∈ RingHom.ker σ) ∧ v = ∑ l, m l * m' l := by
      refine Submodule.mul_induction_on hv ?_ ?_
      · intro p hp q hq
        exact ⟨1, fun _ ↦ p, fun _ ↦ q, fun _ ↦ hp, fun _ ↦ hq, by simp⟩
      · rintro p q ⟨L, m, m', hm, hm', rfl⟩ ⟨L', n, n', hn, hn', rfl⟩
        refine ⟨L + L', Fin.append m n, Fin.append m' n', ?_, ?_, ?_⟩
        · intro l; refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l <;> simp [hm, hn]
        · intro l; refine Fin.addCases (fun l ↦ ?_) (fun l ↦ ?_) l <;> simp [hm', hn']
        · simp [Fin.sum_univ_add]
    obtain ⟨L, m, m', hm, hm', rfl⟩ := this
    exact ⟨a, L, m, m', hm, hm', huv.symm⟩
  choose a L m m' hm hm' hyw using wit
  -- the finite set of coefficients
  let sB : Finset B := Finset.univ.image (fun j ↦ σ (P.val j)) ∪
    Finset.univ.biUnion (fun i ↦ coeffs (t i)) ∪
    Finset.univ.biUnion (fun j ↦ Finset.univ.biUnion (fun i ↦ coeffs (a j i))) ∪
    Finset.univ.biUnion (fun j ↦ Finset.univ.biUnion (fun l ↦ coeffs (m j l) ∪ coeffs (m' j l)))
  obtain ⟨R₁, hR₁fg, hsR₁, hflat⟩ :=
    Module.Flat.exists_fg_subalgebra_flat_tensorProduct (R₀ := P.Core) (R := B)
      (B₀ := P.ModelOfHasCoeffs P.Core) sB
  have lift : ∀ z : T, (∀ k, b z k ∈ R₁) →
      ∃ z₀, modelMap (modelE eT R₁) z₀ = z := fun z hz ↦
    exists_modelMap_eq eT R₁ z (b z) (w z) (hbw z) hz
  have mem_of : ∀ z : T, coeffs z ⊆ sB → ∀ k, b z k ∈ R₁ := fun z hz k ↦
    hsR₁ (hz (Finset.mem_image_of_mem _ (Finset.mem_univ k)))
  -- Noetherianity
  have : Algebra.FiniteType P.Core R₁ := (Subalgebra.fg_iff_finiteType R₁).mp hR₁fg
  have : Algebra.FiniteType ℤ R₁ := Algebra.FiniteType.trans (S := P.Core) inferInstance this
  have hR₁noeth : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  have : Algebra.FiniteType R₁ (R₁ ⊗[P.Core] P.ModelOfHasCoeffs P.Core) := inferInstance
  have hS₀noeth : IsNoetherianRing (R₁ ⊗[P.Core] P.ModelOfHasCoeffs P.Core) :=
    Algebra.FiniteType.isNoetherianRing R₁ (R₁ ⊗[P.Core] P.ModelOfHasCoeffs P.Core)
  -- the section on the model
  have hcmem : ∀ j, σ (P.val j) ∈ R₁ := fun j ↦ hsR₁ (by simp [sB])
  let c : Fin (Algebra.Presentation.ofFinitePresentationVars B T) → R₁ :=
    fun j ↦ ⟨σ (P.val j), hcmem j⟩
  have hcval : ∀ p : MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars B T)) P.Core,
      ((MvPolynomial.aeval c p : R₁) : B) = σ (MvPolynomial.aeval P.val p) := by
    intro p
    have h1 := MvPolynomial.comp_aeval_apply (R := P.Core) (f := c) R₁.val p
    have h2 := MvPolynomial.comp_aeval_apply (R := P.Core) (f := P.val)
      (σ.restrictScalars P.Core) p
    exact h1.trans h2.symm
  let g : P.ModelOfHasCoeffs P.Core →ₐ[P.Core] R₁ :=
    Ideal.Quotient.liftₐ _ (MvPolynomial.aeval c) (by
      intro q hq
      have : Ideal.span (Set.range (P.relationOfHasCoeffs P.Core)) ≤
          RingHom.ker (MvPolynomial.aeval c) := by
        rw [Ideal.span_le]
        rintro _ ⟨r, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker]
        apply Subtype.val_injective
        rw [hcval, P.aeval_val_relationOfHasCoeffs, map_zero]
        rfl
      exact this hq)
  let σ₀ : R₁ ⊗[P.Core] P.ModelOfHasCoeffs P.Core →ₐ[R₁] R₁ :=
    Algebra.TensorProduct.lift (AlgHom.id R₁ R₁) g (fun _ _ ↦ Commute.all _ _)
  have hσ₀ : ∀ x, algebraMap R₁ B (σ₀ x) = σ (modelMap (modelE eT R₁) x) := by
    intro x
    induction x with
    | add x x' hx hx' => rw [map_add, map_add, map_add, hx, hx', map_add]
    | tmul r w0 =>
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective w0
      rw [modelMap_modelE_tmul, P.tensorModelOfHasCoeffsEquiv_tmul]
      simp only [σ₀, g, Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, map_mul,
        AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      rw [← hcval]
      rfl
  -- lifting the needed elements
  have hct : ∀ i, coeffs (t i) ⊆ sB := fun i x hx ↦ by
    simp only [sB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inr ⟨i, hx⟩))
  have hca : ∀ j i, coeffs (a j i) ⊆ sB := fun j i x hx ↦ by
    simp only [sB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inl (Or.inr ⟨j, i, hx⟩)
  have hcm : ∀ j l, coeffs (m j l) ⊆ sB := fun j l x hx ↦ by
    simp only [sB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, l, Or.inl hx⟩
  have hcm' : ∀ j l, coeffs (m' j l) ⊆ sB := fun j l x hx ↦ by
    simp only [sB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr ⟨j, l, Or.inr hx⟩
  choose t₀ ht₀ using fun i ↦ lift (t i) (mem_of _ (hct i))
  choose â hâ using fun j i ↦ lift (a j i) (mem_of _ (hca j i))
  choose m₀ hm₀ using fun j l ↦ lift (m j l) (mem_of _ (hcm j l))
  choose m₀' hm₀' using fun j l ↦ lift (m' j l) (mem_of _ (hcm' j l))
  have hφinj := modelMap_modelE_injective eT R₁
  have hker : ∀ z₀, σ (modelMap (modelE eT R₁) z₀) = 0 → z₀ ∈ RingHom.ker σ₀ := by
    intro z₀ hz
    rw [RingHom.mem_ker]
    apply Subtype.val_injective
    have := hσ₀ z₀
    rw [hz] at this
    exact this
  -- generators of the kernel of the model section
  let ι₀ : ↥R₁ →+* (↥R₁ ⊗[P.Core] P.ModelOfHasCoeffs P.Core) :=
    Algebra.TensorProduct.includeLeftRingHom
  let ρ₀ : (R₁ ⊗[P.Core] P.ModelOfHasCoeffs P.Core) →+* R₁ := σ₀.toRingHom
  have hρι : ∀ a, ρ₀ (ι₀ a) = a := fun a ↦ by
    simp [ι₀, ρ₀, σ₀]
  let v : Fin (Algebra.Presentation.ofFinitePresentationVars B T) → P.ModelOfHasCoeffs P.Core :=
    fun j ↦ Ideal.Quotient.mk _ (MvPolynomial.X j)
  have hv : Algebra.adjoin P.Core (Set.range v) = ⊤ := by
    have : v = (Ideal.Quotient.mkₐ P.Core _) ∘ MvPolynomial.X := by
      funext j; rfl
    rw [this, Set.range_comp, ← AlgHom.map_adjoin, MvPolynomial.adjoin_range_X, Algebra.map_top,
      AlgHom.range_eq_top]
    exact Ideal.Quotient.mkₐ_surjective _ _
  let ŷ : Fin (Algebra.Presentation.ofFinitePresentationVars B T) →
      R₁ ⊗[P.Core] P.ModelOfHasCoeffs P.Core :=
    fun j ↦ (1 : R₁) ⊗ₜ[P.Core] v j - ι₀ (ρ₀ ((1 : R₁) ⊗ₜ[P.Core] v j))
  have hu : ∀ j, modelMap (modelE eT R₁) ((1 : R₁) ⊗ₜ[P.Core] v j) = P.val j := by
    intro j
    rw [modelMap_modelE_tmul, P.tensorModelOfHasCoeffsEquiv_tmul]
    simp
  have hmι : ∀ c : R₁, modelMap (modelE eT R₁) (ι₀ c) = algebraMap B T c := by
    intro c
    change modelMap (modelE eT R₁) (c ⊗ₜ 1) = _
    rw [modelMap_modelE_tmul]
    have : ((c : B) ⊗ₜ[P.Core] (1 : P.ModelOfHasCoeffs P.Core)) =
        (c : B) • (1 : B ⊗[P.Core] P.ModelOfHasCoeffs P.Core) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul, map_one, Algebra.algebraMap_eq_smul_one]
  have hŷ : ∀ j, modelMap (modelE eT R₁) (ŷ j) = y j := by
    intro j
    simp only [ŷ, y, map_sub, hu, hmι]
    congr 2
    rw [← hu j, ← hσ₀]
    rfl
  have hJ₀ := ker_le_of_model v hv σ₀ hρι (modelMap (modelE eT R₁)) hφinj (RingHom.ker σ)
    (fun z hz ↦ hker z hz) t₀ â L m₀ m₀' (fun j l ↦ by rw [hm₀]; exact hm j l)
    (fun j l ↦ by rw [hm₀']; exact hm' j l)
    (fun j ↦ by simp only [hâ, ht₀, hm₀, hm₀']; exact (hŷ j).trans (hyw j))
  exact ⟨R₁, R₁ ⊗[P.Core] P.ModelOfHasCoeffs P.Core, inferInstance, inferInstance,
    inferInstance, inferInstance, hR₁noeth, hS₀noeth, hflat, modelE eT R₁, σ₀, t₀,
    Subtype.val_injective, hσ₀, ht₀, hJ₀⟩

end Main

end Langlands.CommutativeAlgebra.IntegralFibre
