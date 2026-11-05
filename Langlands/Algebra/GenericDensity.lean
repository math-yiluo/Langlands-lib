import Langlands.Algebra.GenericFlatness
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization

/-! # Generic flatness and density over arbitrary domains -/

open TensorProduct

universe u v w

namespace Langlands.Algebra.GenericDensity

open Langlands.Algebra.GenericFlatness

section BaseChange

variable {A : Type u} [CommRing A] {R : Type v} [CommRing R] [Algebra A R]
variable {M : Type w} [AddCommGroup M] [Module A M]

/-- Localization commutes with scalar extension, with its scalar extension module structure. -/
theorem isLocalizedModule_lTensor (S : Submonoid A) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid R S)
      (AlgebraTensorModule.lTensor R R (LocalizedModule.mkLinearMap S M)) := by
  let f := LocalizedModule.mkLinearMap S M
  have h : IsLocalizedModule S
      ((AlgebraTensorModule.lTensor R R f).restrictScalars A) := by
    have h₁ : IsLocalizedModule S (AlgebraTensorModule.rTensor A R f) := inferInstance
    have h₂ := IsLocalizedModule.of_linearEquiv S
      (AlgebraTensorModule.rTensor A R f)
      (TensorProduct.comm A (LocalizedModule S M) R)
    have h₃ := IsLocalizedModule.of_linearEquiv_right S
      ((TensorProduct.comm A (LocalizedModule S M) R).toLinearMap.comp
        (AlgebraTensorModule.rTensor A R f))
      (TensorProduct.comm A R M)
    convert h₃ using 1
    ext r m
    rfl
  exact IsLocalizedModule.of_restrictScalars S _

/-- A flat localized module remains flat after extending its base ring. -/
theorem flat_localizedModule_tensor (a : A)
    [Module.Flat A (LocalizedModule (Submonoid.powers a) M)] :
    Module.Flat R
      (LocalizedModule (Submonoid.powers (algebraMap A R a)) (R ⊗[A] M)) := by
  let f := AlgebraTensorModule.lTensor R R
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
  have : IsLocalizedModule (Submonoid.powers (algebraMap A R a)) f := by
    rw [← Algebra.algebraMapSubmonoid_powers]
    exact isLocalizedModule_lTensor _
  have : Module.Flat R (R ⊗[A] LocalizedModule (Submonoid.powers a) M) := inferInstance
  exact (Module.Flat.equiv_iff
    (IsLocalizedModule.iso (Submonoid.powers (algebraMap A R a)) f)).mpr this

end BaseChange

/-- A finitely presented algebra over any domain is generically flat. -/
theorem genFlat_of_finitePresentation {R : Type u} [CommRing R] [IsDomain R]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.FinitePresentation R B] :
    GenFlat R B := by
  let P := Algebra.Presentation.ofFinitePresentation R B
  let A := P.Core
  let C := P.ModelOfHasCoeffs A
  have : IsDomain A := inferInstanceAs (IsDomain P.core)
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨a, ha, hflat⟩ := genFlat_of_finiteType (A := A) C C
  let b : R := algebraMap A R a
  have hb : b ≠ 0 := by
    exact fun h => ha ((FaithfulSMul.algebraMap_injective A R) (h.trans (map_zero _).symm))
  have : Module.Flat A (LocalizedModule (Submonoid.powers a) C) := hflat a dvd_rfl
  have : Module.Flat R (LocalizedModule (Submonoid.powers b) (R ⊗[A] C)) :=
    flat_localizedModule_tensor a
  have : Module.Flat R (LocalizedModule (Submonoid.powers b) B) :=
    flat_localizedModule_of_equiv _ (P.tensorModelOfHasCoeffsEquiv A).toLinearEquiv
  exact ⟨b, hb, fun c hc => flat_localizedModule_powers_of_dvd hc⟩

/-- Finitely many elements of an ideal suffice to generate its image in a Noetherian ring. -/
theorem exists_fg_le_map_eq {S : Type u} [CommRing S] {T : Type v} [CommRing T]
    [IsNoetherianRing T] (f : S →+* T) (I : Ideal S) :
    ∃ J : Ideal S, J.FG ∧ J ≤ I ∧ J.map f = I.map f := by
  classical
  have hfg : (Submodule.span T (f '' (I : Set S))).FG :=
    (I.map f).fg_of_isNoetherianRing
  obtain ⟨s, hs, heq⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  obtain ⟨t, ht, htfin, hteq⟩ :=
    (Set.exists_subset_image_finite_and (f := f) (s := (I : Set S))
      (p := fun s => Ideal.span (f '' (I : Set S)) = Ideal.span s)).mp
      ⟨s, hs, s.finite_toSet, heq⟩
  refine ⟨Ideal.span t, ⟨htfin.toFinset, by simp⟩, Ideal.span_le.mpr ht, ?_⟩
  rw [Ideal.map_span]
  exact hteq.symm

/-- A surjection with torsion kernel becomes an equivalence wherever its source is flat. -/
theorem flat_localizedModule_of_surjective_torsion_kernel
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (hker : ∀ m, f m = 0 → ∃ r : R, r ≠ 0 ∧ r • m = 0)
    (a : R) (ha : a ≠ 0)
    [Module.Flat R (LocalizedModule (Submonoid.powers a) M)] :
    Module.Flat R (LocalizedModule (Submonoid.powers a) N) := by
  let S := Submonoid.powers a
  let fm := LocalizedModule.mkLinearMap S M
  let fn := LocalizedModule.mkLinearMap S N
  let F := IsLocalizedModule.map S fm fn f
  have hFsurj : Function.Surjective F := IsLocalizedModule.map_surjective S fm fn f hf
  have hFinj : Function.Injective F := by
    apply IsLocalizedModule.injective_of_map_zero S fm
    intro m hm
    change IsLocalizedModule.map S fm fn f (fm m) = 0 at hm
    rw [IsLocalizedModule.map_apply] at hm
    obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff S fn).mp hm
    obtain ⟨r, hr, hrs⟩ := hker ((s : R) • m)
      (by simpa only [map_smul, Submonoid.smul_def] using hs)
    have hsne : (s : R) ≠ 0 := by
      obtain ⟨n, hn⟩ := s.property
      exact hn ▸ pow_ne_zero _ ha
    apply Module.Flat.isSMulRegular_of_nonZeroDivisors
      (M := LocalizedModule S M) (mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero hr hsne))
    simp only [smul_zero, mul_smul, ← fm.map_smul, hrs, map_zero]
  exact (Module.Flat.equiv_iff (LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩)).mp inferInstance

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- A finite type algebra over any domain is generically flat. -/
theorem genFlat_of_finiteType {R : Type u} [CommRing R] [IsDomain R]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B] :
    GenFlat R B := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R B)
  let S := MvPolynomial (Fin n) R
  let T := MvPolynomial (Fin n) (FractionRing R)
  let I := RingHom.ker f.toRingHom
  obtain ⟨J, hJfg, hJI, hJmap⟩ := exists_fg_le_map_eq (algebraMap S T) I
  let P := S ⧸ J
  let p : P →ₐ[R] B := Ideal.Quotient.liftₐ J f (fun q hq => hJI hq)
  have hp : Function.Surjective p :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hf
  have hker : ∀ x, p.toLinearMap x = 0 → ∃ r : R, r ≠ 0 ∧ r • x = 0 := by
    intro x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    intro hq
    have hqI : q ∈ I := hq
    have hqmap : algebraMap S T q ∈ J.map (algebraMap S T) := by
      rw [hJmap]
      exact Ideal.mem_map_of_mem _ hqI
    obtain ⟨c, hc, hcq⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff
        ((nonZeroDivisors R).map (MvPolynomial.C (σ := Fin n))) T J q).mp hqmap
    obtain ⟨r, hr, rfl⟩ := hc
    refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, ?_⟩
    change r • (Ideal.Quotient.mkₐ R J).toLinearMap q = 0
    rw [← (Ideal.Quotient.mkₐ R J).toLinearMap.map_smul]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change (r • q : MvPolynomial (Fin n) R) ∈ J
    rw [MvPolynomial.smul_eq_C_mul]
    exact hcq
  have : Algebra.FinitePresentation R P := Algebra.FinitePresentation.quotient hJfg
  obtain ⟨a, ha, hflat⟩ := genFlat_of_finitePresentation (R := R) P
  have : Module.Flat R (LocalizedModule (Submonoid.powers a) P) := hflat a dvd_rfl
  have : Module.Flat R (LocalizedModule (Submonoid.powers a) B) :=
    flat_localizedModule_of_surjective_torsion_kernel p.toLinearMap hp hker a ha
  exact ⟨a, ha, fun b hb => flat_localizedModule_powers_of_dvd hb⟩

/-- Tensoring a localization map is injective when the new scalar ring inverts the denominator. -/
theorem lTensor_mkLinearMap_injective_of_isUnit
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (a : R) (K : Type w) [CommRing K] [Algebra R K]
    (ha : IsUnit (algebraMap R K a)) :
    Function.Injective ((LocalizedModule.mkLinearMap (Submonoid.powers a) M).lTensor K) := by
  let L := AlgebraTensorModule.lTensor K K
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
  have : IsLocalizedModule (Submonoid.powers (algebraMap R K a)) L := by
    rw [← Algebra.algebraMapSubmonoid_powers]
    exact isLocalizedModule_lTensor _
  change Function.Injective L
  apply (IsLocalizedModule.injective_iff_isRegular
    (Submonoid.powers (algebraMap R K a)) L).mpr
  intro s
  obtain ⟨n, hn⟩ := s.property
  change IsSMulRegular (K ⊗[R] M) (s : K)
  rw [← hn]
  exact (ha.pow n).isSMulRegular (K ⊗[R] M)

/-- Flatness of a localized cokernel makes a short exact sequence universally left exact
over any scalar algebra inverting the localization element. -/
theorem lTensor_injective_of_localized_cokernel_flat
    {R : Type u} [CommRing R]
    {M N P : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) (a : R)
    [Module.Flat R (LocalizedModule (Submonoid.powers a) P)]
    (K : Type w) [CommRing K] [Algebra R K] (ha : IsUnit (algebraMap R K a)) :
    Function.Injective (f.lTensor K) := by
  let S := Submonoid.powers a
  let mM := LocalizedModule.mkLinearMap S M
  let mN := LocalizedModule.mkLinearMap S N
  let mP := LocalizedModule.mkLinearMap S P
  let F := IsLocalizedModule.map S mM mN f
  let G := IsLocalizedModule.map S mN mP g
  have hFinj : Function.Injective F := IsLocalizedModule.map_injective S mM mN f hf
  have hGsurj : Function.Surjective G := IsLocalizedModule.map_surjective S mN mP g hg
  have hFG : Function.Exact F G := LocalizedModule.map_exact S f g hfg
  have hTF : Function.Injective (F.lTensor K) :=
    LinearMap.lTensor_injective_of_exact_of_flat G hGsurj F hFinj hFG K
  have hTm : Function.Injective (mM.lTensor K) :=
    lTensor_mkLinearMap_injective_of_isUnit a K ha
  have hnat : (F.lTensor K).comp (mM.lTensor K) =
      (mN.lTensor K).comp (f.lTensor K) := by
    rw [← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp]
    exact congrArg (LinearMap.lTensor K) (IsLocalizedModule.map_comp S mM mN f)
  intro x y hxy
  apply hTm
  apply hTF
  change ((F.lTensor K).comp (mM.lTensor K)) x =
    ((F.lTensor K).comp (mM.lTensor K)) y
  rw [hnat]
  exact congrArg (mN.lTensor K) hxy

/-- Multiplication by a nonzero element of a finite type domain stays injective
after any scalar extension inverting a suitable nonzero base element. -/
theorem exists_ne_zero_lTensor_mulLeft_injective
    {R : Type u} [CommRing R] [IsDomain R]
    (C : Type v) [CommRing C] [IsDomain C] [Algebra R C] [Algebra.FiniteType R C]
    (g : C) (hg : g ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [CommRing K] [Algebra R K],
      IsUnit (algebraMap R K a) →
        Function.Injective ((LinearMap.mulLeft R g).lTensor K) := by
  let I := Ideal.span ({g} : Set C)
  let Q := C ⧸ I
  let f := LinearMap.mulLeft R g
  let q := (Ideal.Quotient.mkₐ R I).toLinearMap
  have hf : Function.Injective f := fun x y hxy => mul_left_cancel₀ hg hxy
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hfq : Function.Exact f q := by
    intro c
    change Ideal.Quotient.mk I c = 0 ↔ ∃ x, g * x = c
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    simp only [mul_comm]
  obtain ⟨a, ha, hflat⟩ := genFlat_of_finiteType (R := R) Q
  have : Module.Flat R (LocalizedModule (Submonoid.powers a) Q) := hflat a dvd_rfl
  exact ⟨a, ha, fun K _ _ hK =>
    lTensor_injective_of_localized_cokernel_flat f q hf hq hfq a K hK⟩

/-- Uniform fibrewise regularity of a fixed nonzero element of a finite type domain. -/
theorem exists_ne_zero_tensor_mul_injective
    {R : Type u} [CommRing R] [IsDomain R]
    (C : Type v) [CommRing C] [IsDomain C] [Algebra R C] [Algebra.FiniteType R C]
    (g : C) (hg : g ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ ∀ (K : Type w) [Field K] [Algebra R K],
      algebraMap R K a ≠ 0 →
        Function.Injective (fun x : K ⊗[R] C => (1 ⊗ₜ[R] g) * x) := by
  obtain ⟨a, ha, h⟩ := exists_ne_zero_lTensor_mulLeft_injective (R := R) C g hg
  refine ⟨a, ha, fun K _ _ hK => ?_⟩
  have heq : (LinearMap.mulLeft R g).lTensor K =
      (LinearMap.mulLeft K (1 ⊗ₜ[R] g)).restrictScalars R := by
    ext k c
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  have hi := h K (isUnit_iff_ne_zero.mpr hK)
  rw [heq] at hi
  exact hi

end Langlands.Algebra.GenericDensity
