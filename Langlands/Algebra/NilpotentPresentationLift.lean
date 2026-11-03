import Langlands.Algebra.NilpotentQuotientPresentation
import Mathlib.LinearAlgebra.TensorProduct.Pi

universe u v w z

open TensorProduct

namespace Langlands.Algebra

section Reduction

variable (R : Type u) [CommRing R]
variable (P : Type v) [AddCommGroup P] [Module R P]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- The reduction map from a module to its tensor reduction is surjective. -/
theorem quotientTensor_unit_surjective (I : Ideal R) :
    Function.Surjective (TensorProduct.mk R (R ⧸ I) M 1) := by
  intro x
  obtain ⟨m, hm⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective
    (quotientTensorEquiv R M I x)
  refine ⟨m, (quotientTensorEquiv R M I).injective ?_⟩
  change TensorProduct.quotTensorEquivQuotSMul M I (1 ⊗ₜ[R] m) = _
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
  exact hm

/-- A map from the reduction of a projective module lifts to the modules. -/
noncomputable def liftMapOfQuotientTensor [Module.Projective R P] (I : Ideal R)
    (f₀ : (R ⧸ I) ⊗[R] P →ₗ[R ⧸ I] (R ⧸ I) ⊗[R] M) :
    {f : P →ₗ[R] M // f.baseChange (R ⧸ I) = f₀} := by
  let ηP := TensorProduct.mk R (R ⧸ I) P 1
  let ηM := TensorProduct.mk R (R ⧸ I) M 1
  apply Classical.choice
  obtain ⟨f, hf⟩ := Module.projective_lifting_property ηM
    ((f₀.restrictScalars R) ∘ₗ ηP) (quotientTensor_unit_surjective R M I)
  refine ⟨⟨f, ?_⟩⟩
  apply AlgebraTensorModule.ext
  intro a p
  have h := LinearMap.congr_fun hf p
  change (1 : R ⧸ I) ⊗ₜ[R] f p = f₀ (1 ⊗ₜ[R] p) at h
  change a ⊗ₜ[R] f p = f₀ (a ⊗ₜ[R] p)
  calc
    a ⊗ₜ[R] f p = a • ((1 : R ⧸ I) ⊗ₜ[R] f p) :=
      TensorProduct.tmul_eq_smul_one_tmul a (f p)
    _ = a • f₀ (1 ⊗ₜ[R] p) := congrArg (a • ·) h
    _ = f₀ (a ⊗ₜ[R] p) := by
      rw [TensorProduct.tmul_eq_smul_one_tmul a p, map_smul]

/-- Surjectivity can be checked after reduction by a nilpotent ideal. -/
theorem surjective_of_nilpotent_baseChange (I : Ideal R) (hI : IsNilpotent I)
    (f : P →ₗ[R] M) (hf : Function.Surjective (f.baseChange (R ⧸ I))) :
    Function.Surjective f := by
  let Q : Submodule R M := I • ⊤
  have hq : Function.Surjective (Q.mkQ ∘ₗ f) := by
    intro x
    obtain ⟨y, hy⟩ := hf ((quotientTensorEquiv R M I).symm x)
    obtain ⟨p, hp⟩ := quotientTensor_unit_surjective R P I y
    refine ⟨p, ?_⟩
    rw [← hp] at hy
    change (1 : R ⧸ I) ⊗ₜ[R] f p = _ at hy
    have h := congrArg (quotientTensorEquiv R M I) hy
    change TensorProduct.quotTensorEquivQuotSMul M I (1 ⊗ₜ[R] f p) = _ at h
    change Submodule.Quotient.mk (f p) = x
    simpa only [LinearEquiv.apply_symm_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using h
  have hmap : (LinearMap.range f).map Q.mkQ = ⊤ := by
    rw [← LinearMap.range_comp]
    exact LinearMap.range_eq_top.mpr hq
  have hN : LinearMap.range f = ⊤ := by
    apply eq_top_of_sup_smul_eq_top_of_nilpotent I hI
    have hc := congrArg (Submodule.comap Q.mkQ) hmap
    simpa only [Submodule.comap_map_eq, Submodule.ker_mkQ, Submodule.comap_top] using hc
  exact LinearMap.range_eq_top.mp hN

end Reduction

private theorem piScalarRight_quotient_one_tmul
    (R : Type u) [CommRing R] (I : Ideal R) {n : ℕ} (x : Fin n → R) :
    TensorProduct.piScalarRight R (R ⧸ I) (R ⧸ I) (Fin n) (1 ⊗ₜ[R] x) =
      fun i => Ideal.Quotient.mk I (x i) := by
  ext i
  change x i • (1 : R ⧸ I) = _
  rw [Algebra.smul_def, mul_one]
  rfl

section Presentation

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
variable (M : Type w) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- Lift a prescribed finite free presentation of the tensor reduction,
with the same ranks and the exact prescribed reduced maps. -/
noncomputable def liftFiniteFreePresentationOfBaseNilpotent
    [Module.Flat A M] (I : Ideal A) (hI : IsNilpotent I) {n m : ℕ}
    (f₀ : (B ⧸ I.map (algebraMap A B)) ⊗[B] (Fin n → B) →ₗ[B ⧸ I.map (algebraMap A B)]
      (B ⧸ I.map (algebraMap A B)) ⊗[B] M)
    (g₀ : (B ⧸ I.map (algebraMap A B)) ⊗[B] (Fin m → B) →ₗ[B ⧸ I.map (algebraMap A B)]
      (B ⧸ I.map (algebraMap A B)) ⊗[B] (Fin n → B))
    (hf₀ : Function.Surjective f₀) (H₀ : Function.Exact g₀ f₀) :
    {p : ((Fin n → B) →ₗ[B] M) × ((Fin m → B) →ₗ[B] (Fin n → B)) //
      Function.Surjective p.1 ∧ Function.Exact p.2 p.1 ∧
        p.1.baseChange (B ⧸ I.map (algebraMap A B)) = f₀ ∧
        p.2.baseChange (B ⧸ I.map (algebraMap A B)) = g₀} := by
  apply Classical.choice
  let J := I.map (algebraMap A B)
  let C := B ⧸ J
  have hJ : IsNilpotent J := by
    obtain ⟨k, hk⟩ := hI
    refine ⟨k, ?_⟩
    simp only [J, ← Ideal.map_pow, hk, Ideal.zero_eq_bot, Ideal.map_bot]
  obtain ⟨f, hf⟩ := liftMapOfQuotientTensor B (Fin n → B) M J f₀
  have hfs : Function.Surjective f :=
    surjective_of_nilpotent_baseChange B (Fin n → B) M J hJ f (hf ▸ hf₀)
  let K := LinearMap.ker f
  let ι₀ := K.subtype.baseChange C
  have hι : Function.Injective ι₀ :=
    reduction_injective_of_exact_of_base_flat A B I f hfs K.subtype
      K.subtype_injective (LinearMap.exact_subtype_ker_map f)
  have Hι : Function.Exact ι₀ f₀ := by
    have H := lTensor_exact C (LinearMap.exact_subtype_ker_map f) hfs
    change Function.Exact ι₀ (f.baseChange C) at H
    rwa [hf] at H
  let e := LinearEquiv.ofInjective ι₀ hι
  let gK₀ : C ⊗[B] (Fin m → B) →ₗ[C] C ⊗[B] K :=
    e.symm.toLinearMap ∘ₗ g₀.codRestrict (LinearMap.range ι₀) (by
      intro x
      rw [← LinearMap.exact_iff.mp Hι, LinearMap.exact_iff.mp H₀]
      exact LinearMap.mem_range_self g₀ x)
  have hgK₀ : ι₀ ∘ₗ gK₀ = g₀ := by
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply _)
  have hgK₀s : Function.Surjective gK₀ := by
    intro x
    have hx : ι₀ x ∈ LinearMap.range g₀ := by
      rw [← LinearMap.exact_iff.mp H₀, LinearMap.exact_iff.mp Hι]
      exact LinearMap.mem_range_self ι₀ x
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, hι ?_⟩
    exact (LinearMap.congr_fun hgK₀ y).trans hy
  obtain ⟨gK, hgK⟩ := liftMapOfQuotientTensor B (Fin m → B) K J gK₀
  have hgKs : Function.Surjective gK :=
    surjective_of_nilpotent_baseChange B (Fin m → B) K J hJ gK (hgK ▸ hgK₀s)
  let g := K.subtype ∘ₗ gK
  have H : Function.Exact g f := by
    rw [LinearMap.exact_iff, LinearMap.range_comp, LinearMap.range_eq_top.mpr hgKs,
      Submodule.map_top, Submodule.range_subtype]
  have hg : g.baseChange C = g₀ := by
    rw [LinearMap.baseChange_comp, hgK]
    exact hgK₀
  exact ⟨⟨(f, g), hfs, H, hf, hg⟩⟩

/-- Lift a prescribed presentation of the ordinary quotient, with the
same ranks and equality of its actual coordinate reductions. -/
noncomputable def liftFiniteFreePresentationOfNilpotentQuotient
    [Module.Flat A M] (I : Ideal A) (hI : IsNilpotent I) {n m : ℕ}
    (f₀ : (Fin n → B ⧸ I.map (algebraMap A B)) →ₗ[B ⧸ I.map (algebraMap A B)]
      M ⧸ (I.map (algebraMap A B) • (⊤ : Submodule B M)))
    (g₀ : (Fin m → B ⧸ I.map (algebraMap A B)) →ₗ[B ⧸ I.map (algebraMap A B)]
      (Fin n → B ⧸ I.map (algebraMap A B)))
    (hf₀ : Function.Surjective f₀) (H₀ : Function.Exact g₀ f₀) :
    {p : ((Fin n → B) →ₗ[B] M) × ((Fin m → B) →ₗ[B] (Fin n → B)) //
      Function.Surjective p.1 ∧ Function.Exact p.2 p.1 ∧
        (∀ x, Submodule.Quotient.mk (p.1 x) =
          f₀ (fun i => Ideal.Quotient.mk (I.map (algebraMap A B)) (x i))) ∧
        (∀ x, (fun i => Ideal.Quotient.mk (I.map (algebraMap A B)) (p.2 x i)) =
          g₀ (fun i => Ideal.Quotient.mk (I.map (algebraMap A B)) (x i)))} := by
  apply Classical.choice
  let J := I.map (algebraMap A B)
  let C := B ⧸ J
  let eM := quotientTensorEquiv B M J
  let en := TensorProduct.piScalarRight B C C (Fin n)
  let em := TensorProduct.piScalarRight B C C (Fin m)
  let fT := eM.symm.toLinearMap ∘ₗ (f₀ ∘ₗ en.toLinearMap)
  let gT := (en.symm.toLinearMap ∘ₗ g₀) ∘ₗ em.toLinearMap
  have hfT : Function.Surjective fT :=
    eM.symm.surjective.comp (hf₀.comp en.surjective)
  have HT : Function.Exact gT fT := by
    apply LinearEquiv.postcomp_exact_iff_exact.mpr
    apply LinearEquiv.precomp_exact_iff_exact.mpr
    exact (en.conj_symm_exact_iff_exact g₀ f₀).mpr H₀
  obtain ⟨⟨f, g⟩, hfs, H, hf, hg⟩ :=
    liftFiniteFreePresentationOfBaseNilpotent A B M I hI fT gT hfT HT
  refine ⟨⟨(f, g), hfs, H, ?_, ?_⟩⟩
  · intro x
    have h := LinearMap.congr_fun hf (1 ⊗ₜ[B] x)
    change (1 : C) ⊗ₜ[B] f x = eM.symm (f₀ (en (1 ⊗ₜ[B] x))) at h
    have h' := congrArg eM h
    rw [eM.apply_symm_apply] at h'
    change TensorProduct.quotTensorEquivQuotSMul M J (1 ⊗ₜ[B] f x) = _ at h'
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
      piScalarRight_quotient_one_tmul B J x] at h'
    exact h'
  · intro x
    have h := LinearMap.congr_fun hg (1 ⊗ₜ[B] x)
    change (1 : C) ⊗ₜ[B] g x = en.symm (g₀ (em (1 ⊗ₜ[B] x))) at h
    have h' := congrArg en h
    rw [en.apply_symm_apply, piScalarRight_quotient_one_tmul B J (g x),
      piScalarRight_quotient_one_tmul B J x] at h'
    exact h'

end Presentation

end Langlands.Algebra
