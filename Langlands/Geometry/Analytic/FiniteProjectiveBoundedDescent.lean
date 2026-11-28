import Langlands.Geometry.Analytic.FiniteAffinoidLocalizedHomDescent
import Langlands.Geometry.Analytic.FullRecognitionFiniteMorphisms
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Noetherian
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-! # Bounded descent along finite projective faithfully flat affinoid maps, over every field -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open scoped TensorProduct
open AffinoidPushout

/-- A faithfully flat projective algebra `B` over `A` has an `A`-linear map `B → A` sending
`1` to `1`, so `A` is an `A`-module direct summand of `B`. -/
theorem exists_linearMap_apply_one_eq_one {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.FaithfullyFlat A B] [Module.Projective A B] :
    ∃ r : B →ₗ[A] A, r 1 = 1 := by
  classical
  let J : Ideal A := LinearMap.range (LinearMap.applyₗ (R := A) (M₂ := A) (1 : B))
  by_contra hJ
  have hJtop : J ≠ ⊤ := by
    intro h
    have h1 : (1 : A) ∈ J := h ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := h1
    exact hJ ⟨r, hr⟩
  apply ((Module.FaithfullyFlat.iff_flat_and_proper_ideal A B).1 inferInstance).2 J hJtop
  obtain ⟨s, hs⟩ := Module.projective_def.1 (inferInstance : Module.Projective A B)
  have h1 : (1 : B) ∈ J • (⊤ : Submodule A B) := by
    rw [← hs 1, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun p _ => ?_
    exact Submodule.smul_mem_smul ⟨Finsupp.lapply p ∘ₗ s, rfl⟩ Submodule.mem_top
  rw [Ideal.smul_top_eq_map] at h1 ⊢
  rw [(Ideal.eq_top_iff_one _).2 h1]
  exact Submodule.restrictScalars_top _ _ _

/-- An `A`-linear map out of a finite Banach `A`-algebra `B` is bounded: writing
`y = ∑ f (c i) * b i` with `‖c‖ ≤ C ‖y‖` gives `‖r y‖ ≤ C (∑ ‖r (b i)‖) ‖y‖`. -/
theorem exists_norm_linearMap_le {K : Type*} [NormedField K] {A B : Type*}
    [NormedCommRing A] [NormedCommRing B] [NormedAlgebra K A] [NormedAlgebra K B]
    [Algebra A B] (f : BoundedAlgHom K A B) (hfa : ∀ a, algebraMap A B a = f a)
    (hf : f.IsFiniteBanach) (r : B →ₗ[A] A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : B, ‖r y‖ ≤ M * ‖y‖ := by
  obtain ⟨n, b, C, hC, hb⟩ := hf
  refine ⟨C * ∑ i, ‖r (b i)‖, by positivity, fun y => ?_⟩
  obtain ⟨c, hcy, hcn⟩ := hb y
  have hry : r y = ∑ i, c i * r (b i) := by
    rw [← hcy, BoundedAlgHom.coefficientMap_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hfa, ← Algebra.smul_def, r.map_smul, smul_eq_mul]
  calc
    ‖r y‖ = ‖∑ i, c i * r (b i)‖ := by rw [hry]
    _ ≤ ∑ i, ‖c i * r (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c‖ * ‖r (b i)‖ := Finset.sum_le_sum fun i _ =>
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_le_pi_norm c i) (norm_nonneg _))
    _ = ‖c‖ * ∑ i, ‖r (b i)‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ C * ‖y‖ * ∑ i, ‖r (b i)‖ :=
      mul_le_mul_of_nonneg_right hcn (Finset.sum_nonneg fun i _ => norm_nonneg _)
    _ = (C * ∑ i, ‖r (b i)‖) * ‖y‖ := by ring

private theorem mem_range_algebraMap_of_tensor_eq'
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] {b : B}
    (hb : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) :
    b ∈ LinearMap.range (Algebra.linearMap A B) := by
  let V := LinearMap.range (Algebra.linearMap A B)
  let q : B →ₗ[A] B ⧸ V := V.mkQ
  have h1 : q 1 = 0 := by
    change 1 ∈ LinearMap.ker V.mkQ
    rw [Submodule.ker_mkQ]
    exact ⟨1, map_one (algebraMap A B)⟩
  have h := congrArg (TensorProduct.map (LinearMap.id : B →ₗ[A] B) q) hb
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, h1, TensorProduct.tmul_zero] at h
  have hq : q b = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B)
    simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using h.symm
  change b ∈ LinearMap.ker V.mkQ at hq
  rwa [Submodule.ker_mkQ] at hq

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Unique bounded descent along a finite Banach, faithfully flat map of affinoid algebras,
over every complete ultrametric field: a bounded map into `B` whose two composites into the
completed self-pushout agree factors uniquely through `f`. -/
theorem exists_unique_boundedDescent {A B C : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B) (g : BoundedAlgHom K C B)
    (hfinite : f.IsFiniteBanach) (hflat : f.toAlgHom.toRingHom.FaithfullyFlat)
    (hg : (leftMap f f).comp g = (rightMap f f).comp g) :
    ∃! h : BoundedAlgHom K C A, f.comp h = g := by
  let : Algebra A B := f.toAlgHom.toRingHom.toAlgebra
  let : Module.FaithfullyFlat A B := hflat
  let : Module.Finite A B := hfinite.finite
  have : Algebra.FiniteType A B := hfinite.finite.finiteType
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Module.FinitePresentation A B :=
    Module.FinitePresentation.of_finite_of_finitePresentation A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  obtain ⟨r, hr⟩ := exists_linearMap_apply_one_eq_one (A := A) (B := B)
  obtain ⟨M, hM0, hM⟩ := exists_norm_linearMap_le f (fun _ => rfl) hfinite r
  have hrf (a : A) : r (f a) = a := by
    change r (algebraMap A B a) = a
    rw [Algebra.algebraMap_eq_smul_one, r.map_smul, hr, smul_eq_mul, mul_one]
  have hf : Function.Injective f := fun a a' h => by rw [← hrf a, ← hrf a', h]
  have hcomparison := (finiteTensorComparison A B B f f hfinite).1
  have hRange : Set.range f = {b | leftMap f f b = rightMap f f b} := by
    ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg (fun p : BoundedAlgHom K A (algebra f f) => p a) (condition f f)
    · intro hb
      have htensor : b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b := by
        apply hcomparison
        change tensorComparison f f (tensorLeft f f b) =
          tensorComparison f f (tensorRight f f b)
        rw [tensorComparison_tensorLeft, tensorComparison_tensorRight]
        exact hb.symm
      exact mem_range_algebraMap_of_tensor_eq' htensor
  have hRangeG (c : C) : g c ∈ f.toAlgHom.range := by
    change g c ∈ Set.range f
    rw [hRange]
    exact congrArg (fun p : BoundedAlgHom K C (algebra f f) => p c) hg
  let e := AlgEquiv.ofInjective f.toAlgHom hf
  let lift := e.symm.toAlgHom.comp (g.toAlgHom.codRestrict f.toAlgHom.range hRangeG)
  have hlift (c : C) : f (lift c) = g c :=
    congrArg Subtype.val (e.apply_symm_apply ⟨g c, hRangeG c⟩)
  have hbounded : lift.toRingHom.IsBounded := by
    obtain ⟨N, hN, hbound⟩ := g.bounded
    refine ⟨M * N + 1, by positivity, fun c => ?_⟩
    change ‖lift c‖ ≤ (M * N + 1) * ‖c‖
    calc
      ‖lift c‖ = ‖r (f (lift c))‖ := by rw [hrf]
      _ ≤ M * ‖f (lift c)‖ := hM _
      _ = M * ‖g c‖ := by rw [hlift c]
      _ ≤ M * (N * ‖c‖) := mul_le_mul_of_nonneg_left (hbound c) hM0
      _ = M * N * ‖c‖ := (mul_assoc _ _ _).symm
      _ ≤ (M * N + 1) * ‖c‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg c)
  refine ⟨⟨lift, hbounded⟩, BoundedAlgHom.ext hlift, ?_⟩
  intro h hh
  apply BoundedAlgHom.ext
  intro c
  apply hf
  exact (congrArg (fun p : BoundedAlgHom K C B => p c) hh).trans (hlift c).symm

end Langlands.Analytic.PresentedAffinoidAlgebra

namespace Langlands.Analytic.SmallAffinoidSpectrum

open CategoryTheory PresentedAffinoidAlgebra SaturatedAtlasPresentation AffinoidPushout

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Descent across the localized self-pullback of a single finite Banach, flat affinoid
morphism that is surjective on spectra, with a small affinoid target, over every complete
ultrametric field. -/
theorem exists_unique_localizedHomDescent {A B C : PresentedAffinoidAlgebra K}
    [Small.{v} (BanachSpectrum A)] [Small.{v} (BanachSpectrum B)]
    [Small.{v} (BanachSpectrum C)]
    (f : BoundedAlgHom K A B) (hf : f.IsFiniteBanach)
    (hflat : f.toAlgHom.toRingHom.Flat)
    (hsurj : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom))
    (g : localizationFunctor.obj (saturated.{u, v} B) ⟶
        localizationFunctor.obj (saturated.{u, v} C))
    (hmatch : localizationFunctor.map (finitePushoutFst f f finiteBanachPushout hf) ≫ g =
        localizationFunctor.map (finitePushoutSnd f f finiteBanachPushout hf) ≫ g) :
    ∃! h : localizationFunctor.obj (saturated A) ⟶ localizationFunctor.obj (saturated C),
      localizationFunctor.map (map f) ≫ h = g := by
  let : Small.{v} (BanachSpectrum (algebra f f)) :=
    small_spectrum_of_finiteBanachPushout f f finiteBanachPushout hf
  let g₀ := (localizedMapEquiv.{u, v} C B).symm g
  have hg₀ : localizedMapEquiv.{u, v} C B g₀ = g :=
    (localizedMapEquiv.{u, v} C B).apply_symm_apply g
  have hgMatch : (leftMap f f).comp g₀ = (rightMap f f).comp g₀ := by
    apply (localizedMapEquiv.{u, v} C (algebra f f)).injective
    rw [localizedMapEquiv_comp, localizedMapEquiv_comp, hg₀]
    exact hmatch
  obtain ⟨h, hh, huniq⟩ := exists_unique_boundedDescent f g₀ hf
    (faithfullyFlat_of_flat_of_spectrum_surjective f hflat hsurj) hgMatch
  refine ⟨localizedMapEquiv.{u, v} C A h, ?_, ?_⟩
  · change localizedMapEquiv.{u, v} A B f ≫ localizedMapEquiv.{u, v} C A h = g
    rw [← localizedMapEquiv_comp, hh, hg₀]
  · intro h' hh'
    obtain ⟨h₀', rfl⟩ := (localizedMapEquiv.{u, v} C A).surjective h'
    apply congrArg (localizedMapEquiv.{u, v} C A)
    apply huniq
    apply (localizedMapEquiv.{u, v} C B).injective
    rw [localizedMapEquiv_comp]
    exact hh'.trans hg₀.symm

end Langlands.Analytic.SmallAffinoidSpectrum
