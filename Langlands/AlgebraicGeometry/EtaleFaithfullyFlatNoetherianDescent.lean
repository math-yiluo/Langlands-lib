import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-! # Noetherian descent of étale faithfully flat algebras

Let `A` be an `R`-algebra and `B` an étale, faithfully flat `A`-algebra. Then there are an
`R`-subalgebra `A₁ ⊆ A` of finite type and an étale, faithfully flat `A₁`-algebra `B₁` with
`B ≃ₐ[A] A ⊗[A₁] B₁`.

Mathlib's `Algebra.Etale.exists_subalgebra_fg` gives such `A₀` and `B₀` with `B₀` étale over
`A₀`, but not necessarily faithfully flat. The image `U` of `Spec B₀ → Spec A₀` is open (flat and
of finite presentation), say with complement `V(I)`. Every prime of `A` contracts into `U`, since
`B` is faithfully flat over `A`; hence `I A = A`, so `1 = ∑ cᵢ xᵢ` with `xᵢ ∈ I` and `cᵢ ∈ A`.
Over `A₁ = A₀[cᵢ]` every prime contracts into `U`, so `B₁ = A₁ ⊗[A₀] B₀` is faithfully flat
over `A₁`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

/-- Let `A` be an `R`-algebra and `B` an étale, faithfully flat `A`-algebra. Then there are an
`R`-subalgebra `A₁` of `A` of finite type and an étale, faithfully flat `A₁`-algebra `B₁` such
that `B ≃ₐ[A] A ⊗[A₁] B₁`. -/
theorem exists_subalgebra_fg_etale_faithfullyFlat (R : Type*) [CommRing R] {A B : Type u}
    [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra.Etale A B]
    [Module.FaithfullyFlat A B] :
    ∃ (A₁ : Subalgebra R A) (B₁ : Type u) (_ : CommRing B₁) (_ : Algebra A₁ B₁),
      A₁.FG ∧ Algebra.Etale A₁ B₁ ∧ Module.FaithfullyFlat A₁ B₁ ∧
        Nonempty (B ≃ₐ[A] A ⊗[A₁] B₁) := by
  obtain ⟨A₀, B₀, _, _, hA₀, _, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg R A B
  -- The image `U` of `Spec B₀ → Spec A₀` is open, with complement `V(I)`.
  set U := Set.range (PrimeSpectrum.comap (algebraMap A₀ B₀)) with hUdef
  have : Algebra.HasGoingDown A₀ B₀ := Algebra.HasGoingDown.of_flat
  have hUo : IsOpen U :=
    (PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation).isOpen_range
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Uᶜ).mp hUo.isClosed_compl
  -- Every prime of `A` contracts into `U`.
  have hA : ∀ x : PrimeSpectrum A, PrimeSpectrum.comap (algebraMap A₀ A) x ∈ U := by
    intro x
    obtain ⟨y, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) x
    have hcomp : (algebraMap A B).comp (algebraMap A₀ A) =
        ((e.symm : A ⊗[A₀] B₀ →+* B).comp
          (Algebra.TensorProduct.includeRight : B₀ →ₐ[A₀] A ⊗[A₀] B₀).toRingHom).comp
          (algebraMap A₀ B₀) := by
      ext a
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
      rw [← Algebra.TensorProduct.algebraMap_apply', ← AlgEquiv.commutes e.symm]
      rfl
    refine ⟨PrimeSpectrum.comap ((e.symm : A ⊗[A₀] B₀ →+* B).comp
      (Algebra.TensorProduct.includeRight : B₀ →ₐ[A₀] A ⊗[A₀] B₀).toRingHom) y, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, ← hcomp, PrimeSpectrum.comap_comp_apply]
  -- Hence `I A = A`.
  have hItop : I.map (algebraMap A₀ A) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 := hA ⟨m, hm.isPrime⟩
    have h2 : PrimeSpectrum.comap (algebraMap A₀ A) ⟨m, hm.isPrime⟩ ∈ Uᶜ := by
      rw [hI, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
      exact Ideal.map_le_iff_le_comap.mp hle
    exact h2 h1
  -- Write `1 = ∑ cᵢ xᵢ` with `xᵢ ∈ I`.
  have h1mem : (1 : A) ∈ Submodule.span A (algebraMap A₀ A '' (I : Set A₀)) := by
    change (1 : A) ∈ I.map (algebraMap A₀ A)
    rw [hItop]
    trivial
  obtain ⟨t, htI, c, hc⟩ := (Submodule.mem_span_image_iff_exists_fun A).mp h1mem
  -- The subalgebra `A₁ = A₀[cᵢ]`.
  let A₁ : Subalgebra R A := A₀ ⊔ Algebra.adjoin R (Set.range c)
  have hle : A₀ ≤ A₁ := le_sup_left
  have hcA₁ : ∀ i, c i ∈ A₁ := fun i =>
    (le_sup_right : Algebra.adjoin R (Set.range c) ≤ A₁) (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hA₁fg : A₁.FG :=
    hA₀.sup (Subalgebra.fg_def.mpr ⟨Set.range c, Set.finite_range c, rfl⟩)
  let : Algebra A₀ A₁ := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  have : IsScalarTower A₀ A₁ A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Every prime of `A₁` contracts into `U`.
  have hA₁ : ∀ x : PrimeSpectrum A₁, PrimeSpectrum.comap (algebraMap A₀ A₁) x ∈ U := by
    intro x
    by_contra hx
    have hx' : PrimeSpectrum.comap (algebraMap A₀ A₁) x ∈ PrimeSpectrum.zeroLocus (I : Set A₀) :=
      hI ▸ hx
    rw [PrimeSpectrum.mem_zeroLocus] at hx'
    have hsum : (1 : A₁) = ∑ i, (⟨c i, hcA₁ i⟩ : A₁) * algebraMap A₀ A₁ (i : A₀) := by
      apply Subtype.val_injective
      simp only [Subalgebra.coe_one, AddSubmonoidClass.coe_finsetSum, Subalgebra.coe_mul]
      rw [← hc]
      exact Finset.sum_congr rfl fun i _ => rfl
    refine x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
    rw [hsum]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hx' (htI i.2))
  -- `B₁ = A₁ ⊗[A₀] B₀` is étale and faithfully flat over `A₁`.
  have hsurj : Function.Surjective
      (PrimeSpectrum.comap (algebraMap A₁ (A₁ ⊗[A₀] B₀))) := by
    intro x
    have hx : x ∈ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A₁))) ⁻¹'
        Set.range (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) := hA₁ x
    rw [← Scheme.Pullback.range_fst] at hx
    obtain ⟨z, hz⟩ := hx
    refine ⟨(pullbackSpecIso A₀ A₁ B₀).hom z, ?_⟩
    change (Spec.map (CommRingCat.ofHom (algebraMap A₁ (A₁ ⊗[A₀] B₀))))
      ((pullbackSpecIso A₀ A₁ B₀).hom z) = x
    rw [← Scheme.Hom.comp_apply, pullbackSpecIso_hom_fst', hz]
  have : Module.FaithfullyFlat A₁ (A₁ ⊗[A₀] B₀) :=
    Module.FaithfullyFlat.of_comap_surjective hsurj
  exact ⟨A₁, A₁ ⊗[A₀] B₀, inferInstance, inferInstance, hA₁fg, inferInstance, inferInstance,
    ⟨e.trans (Algebra.TensorProduct.cancelBaseChange A₀ A₁ A A B₀).symm⟩⟩

end Langlands.AlgebraicGeometry
