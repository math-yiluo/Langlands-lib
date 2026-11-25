import Langlands.MathlibBase

/-! # Principal regular ideals descend along flat local base changes of a flat family -/

universe u

open TensorProduct

noncomputable section

namespace Langlands.CommutativeAlgebra.CartierLocusDescent

section TorInj

variable {A R A' S : Type u} [CommRing A] [CommRing R] [CommRing A'] [CommRing S]
  [Algebra A R] [Algebra A A'] [Algebra R S] [Algebra A' S] [Algebra A S]
  [IsScalarTower A R S] [IsScalarTower A A' S] [hP : Algebra.IsPushout A R A' S]

variable (A R A' S) in
/-- For a pushout `S = R ⊗[A] A'`, base change of an `R`-module to `S` is base change of the
underlying `A`-module to `A'`. -/
def baseChangeEquiv (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower A R N] : A' ⊗[A] N ≃ₗ[A] S ⊗[R] N :=
  (TensorProduct.comm A A' N ≪≫ₗ
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange A R R N A').symm ≪≫ₗ
    TensorProduct.comm R N (R ⊗[A] A') ≪≫ₗ
    LinearEquiv.rTensor N hP.out.equiv).restrictScalars A)

lemma baseChangeEquiv_tmul (N : Type u) [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower A R N] (a : A') (n : N) :
    baseChangeEquiv A R A' S N (a ⊗ₜ n) = algebraMap A' S a ⊗ₜ n := by
  simp [baseChangeEquiv, IsBaseChange.equiv_tmul]

include hP in
/-- **Tor vanishing along the pushout.** If `0 → N → M → C → 0` is exact and `C` is flat over
`A`, then `S ⊗[R] N → S ⊗[R] M` is injective. -/
theorem lTensor_injective_pushout {N M C : Type u} [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower A R N] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
    [AddCommGroup C] [Module R C] [Module A C] [IsScalarTower A R C] [Module.Flat A C]
    (g : N →ₗ[R] M) (hg : Function.Injective g) (f : M →ₗ[R] C) (hf : Function.Surjective f)
    (hex : Function.Exact g f) : Function.Injective (g.lTensor S) := by
  have hA : Function.Injective ((g.restrictScalars A).lTensor A') :=
    LinearMap.lTensor_injective_of_exact_of_flat (f.restrictScalars A) hf (g.restrictScalars A)
      hg hex A'
  have hcomp : (g.lTensor S).restrictScalars A ∘ₗ (baseChangeEquiv A R A' S N).toLinearMap =
      (baseChangeEquiv A R A' S M).toLinearMap ∘ₗ (g.restrictScalars A).lTensor A' := by
    ext a n
    simp [baseChangeEquiv_tmul]
  have h2 : Function.Injective ((g.lTensor S).restrictScalars A ∘ₗ
      (baseChangeEquiv A R A' S N).toLinearMap) := by
    rw [hcomp]
    exact (baseChangeEquiv A R A' S M).injective.comp hA
  intro x y hxy
  obtain ⟨x', rfl⟩ := (baseChangeEquiv A R A' S N).surjective x
  obtain ⟨y', rfl⟩ := (baseChangeEquiv A R A' S N).surjective y
  exact congrArg _ (h2 hxy)

include hP in
/-- **Tor vanishing along a flat extension of the pushout.** -/
theorem lTensor_injective_of_flat {N M C : Type u} [AddCommGroup N] [Module R N] [Module A N]
    [IsScalarTower A R N] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower A R M]
    [AddCommGroup C] [Module R C] [Module A C] [IsScalarTower A R C] [Module.Flat A C]
    (g : N →ₗ[R] M) (hg : Function.Injective g) (f : M →ₗ[R] C) (hf : Function.Surjective f)
    (hex : Function.Exact g f) (T : Type u) [CommRing T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Module.Flat S T] : Function.Injective (g.lTensor T) := by
  have hS : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor S S g) :=
    lTensor_injective_pushout (A := A) (A' := A') g hg f hf hex
  have hT := Module.Flat.lTensor_preserves_injective_linearMap (M := T) _ hS
  have hcomp (x : T ⊗[S] (S ⊗[R] N)) :
      g.lTensor T (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N x) =
      TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M
        ((TensorProduct.AlgebraTensorModule.lTensor S S g).lTensor T x) := by
    have H := congrArg DFunLike.coe
      (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange (R := R) (A := S)
        (B := T) (M := T) (N := N) (Q := M) g)
    have H' := congrFun H x
    simpa [TensorProduct.AlgebraTensorModule.coe_lTensor] using H'
  intro x y hxy
  obtain ⟨x', rfl⟩ := (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N).surjective x
  obtain ⟨y', rfl⟩ := (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T N).surjective y
  rw [hcomp, hcomp] at hxy
  have := (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).injective hxy
  rw [hT this]

end TorInj

section Nakayama

/-- **Nakayama along a local homomorphism.** If a finite `R`-module dies after base change to a
local `R`-algebra `T`, it is killed by an element of `R` that becomes a unit in `T`. -/
theorem exists_smul_eq_zero_of_subsingleton {R T M : Type u} [CommRing R] [CommRing T]
    [IsLocalRing T] [Algebra R T] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Subsingleton (T ⊗[R] M)) :
    ∃ g : R, IsUnit (algebraMap R T g) ∧ ∀ m : M, g • m = 0 := by
  classical
  let p : Ideal R := (IsLocalRing.maximalIdeal T).comap (algebraMap R T)
  have hpp : p.IsPrime := Ideal.comap_isPrime _ _
  by_contra hcon
  push Not at hcon
  have hann : Module.annihilator R M ≤ p := by
    intro g hg
    by_contra hgp
    have hu : IsUnit (algebraMap R T g) := by
      by_contra hn
      exact hgp ((IsLocalRing.mem_maximalIdeal _).mpr hn)
    obtain ⟨m, hm⟩ := hcon g hu
    exact hm (Module.mem_annihilator.mp hg m)
  have hsupp : (⟨p, hpp⟩ : PrimeSpectrum R) ∈ Module.support R M :=
    Module.mem_support_iff_of_finite.mpr hann
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hsupp
  let K := IsLocalRing.ResidueField T
  let φ : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap R K)
    (fun r hr => by
      rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R T K,
        IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff]
      exact hr)
    (fun r hr => by
      change IsUnit (algebraMap R K r)
      rw [IsScalarTower.algebraMap_apply R T K]
      have : algebraMap R T r ∉ IsLocalRing.maximalIdeal T := hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at this
      exact this.map _)
  let _ : Algebra p.ResidueField K := φ.toAlgebra
  have : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R K r = φ (algebraMap R p.ResidueField r)
    exact (Ideal.ResidueField.lift_algebraMap _ _ _ _ r).symm)
  have : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[R] M)) := inferInstance
  have e1 := TensorProduct.AlgebraTensorModule.cancelBaseChange R p.ResidueField K K M
  have e2 := TensorProduct.AlgebraTensorModule.cancelBaseChange R T K K M
  have hsub : Subsingleton (K ⊗[T] (T ⊗[R] M)) := by
    refine ⟨fun x y => ?_⟩
    have h0 : ∀ z : K ⊗[T] (T ⊗[R] M), z = 0 := by
      intro z
      have hid : (LinearMap.id : (T ⊗[R] M) →ₗ[T] (T ⊗[R] M)) = 0 :=
        LinearMap.ext fun n => Subsingleton.elim _ _
      have := congrArg (fun F => F z) (congrArg (LinearMap.lTensor K) hid)
      rw [LinearMap.lTensor_id, LinearMap.id_apply] at this
      rw [this]
      simp
    rw [h0 x, h0 y]
  have : Subsingleton (K ⊗[R] M) := e2.symm.toEquiv.subsingleton
  have : Subsingleton (K ⊗[p.ResidueField] (p.ResidueField ⊗[R] M)) :=
    e1.toEquiv.subsingleton
  exact not_subsingleton _ this

end Nakayama

section Ideals

variable {A R : Type u} [CommRing A] [CommRing R] [Algebra A R]

/-- If `R` and `R ⧸ I` are flat over `A`, so is `I`. -/
theorem flat_ideal [Module.Flat A R] (I : Ideal R) [Module.Flat A (R ⧸ I)] :
    Module.Flat A I := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ L hL
  have h1 : Function.Injective ((I.subtype.restrictScalars A).rTensor N) := by
    rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
    exact LinearMap.lTensor_injective_of_exact_of_flat
      ((I.mkQ).restrictScalars A) (Submodule.mkQ_surjective _) (I.subtype.restrictScalars A)
      (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ I) N
  have key : L.lTensor R ∘ₗ (I.subtype.restrictScalars A).rTensor N =
      (I.subtype.restrictScalars A).rTensor N' ∘ₗ L.lTensor I := by
    rw [LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  have h2 : Function.Injective (L.lTensor R ∘ₗ (I.subtype.restrictScalars A).rTensor N) :=
    (Module.Flat.lTensor_preserves_injective_linearMap L hL).comp h1
  rw [key, LinearMap.coe_comp] at h2
  exact h2.of_comp

end Ideals

section Generators

/-- If `s` is regular and lies in the principal ideal generated by `a`, then `a` is regular. -/
theorem isSMulRegular_of_mem_span {T : Type u} [CommRing T] {a s : T}
    (hs : s ∈ Ideal.span {a}) (hreg : IsSMulRegular T s) : IsSMulRegular T a := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul] at hreg ⊢
  intro x hx
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hs
  apply hreg
  rw [smul_eq_mul] at hx ⊢
  rw [mul_assoc, hx, mul_zero]

/-- In a local ring, an ideal generated by a family is the unit ideal only if some member of the
family is a unit. -/
theorem exists_isUnit_of_span_eq_top {T : Type u} [CommRing T] [IsLocalRing T] {X : Set T}
    (hX : Ideal.span X = ⊤) : ∃ b ∈ X, IsUnit b := by
  by_contra hcon
  push Not at hcon
  have hle : Ideal.span X ≤ IsLocalRing.maximalIdeal T := by
    rw [Ideal.span_le]
    intro b hb
    exact (IsLocalRing.mem_maximalIdeal b).mpr (hcon b hb)
  rw [hX] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top (top_le_iff.mp hle)

/-- **A generator coming from the ideal.** Let `φ : R → T` be a ring map to a local ring. If the
extension of `I` is generated by a regular element `s`, then it is generated by the image of an
element of `I`, and this image is again regular. -/
theorem exists_mem_map_eq_span {R T : Type u} [CommRing R] [CommRing T] [IsLocalRing T]
    (φ : R →+* T) (I : Ideal R) {s : T} (hs : I.map φ = Ideal.span {s})
    (hreg : IsSMulRegular T s) :
    ∃ f ∈ I, I.map φ = Ideal.span {φ f} ∧ IsSMulRegular T (φ f) := by
  classical
  let J : Ideal T := Ideal.span {b | ∃ x ∈ I, φ x = b * s}
  have hle : I.map φ ≤ J * Ideal.span {s} := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have hx' : φ x ∈ Ideal.span {s} := hs ▸ Ideal.mem_map_of_mem φ hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hx'
    rw [Ideal.mem_comap, Ideal.mem_mul_span_singleton]
    exact ⟨b, Ideal.subset_span ⟨x, hx, hb.symm⟩, hb⟩
  have hsm : s ∈ J * Ideal.span {s} := hle (hs ▸ Ideal.mem_span_singleton_self s)
  obtain ⟨z, hz, hzs⟩ := Ideal.mem_mul_span_singleton.mp hsm
  have hz1 : z = 1 := by
    apply hreg
    change s * z = s * 1
    rw [mul_one, mul_comm, hzs]
  rw [hz1, ← Ideal.eq_top_iff_one] at hz
  obtain ⟨b, ⟨x, hx, hxb⟩, hb⟩ := exists_isUnit_of_span_eq_top hz
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hxb, Ideal.span_singleton_mul_left_unit hb, hs]
  · rw [hxb]
    exact hb.isSMulRegular T |>.mul hreg

end Generators

section Lift

variable {A R A' S : Type u} [CommRing A] [CommRing R] [CommRing A'] [CommRing S]
  [Algebra A R] [Algebra A A'] [Algebra R S] [Algebra A' S] [Algebra A S]
  [IsScalarTower A R S] [IsScalarTower A A' S] [hP : Algebra.IsPushout A R A' S]
  (T : Type u) [CommRing T] [IsLocalRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Module.Flat S T]

include hP in
/-- **Generators near the point (Kleiman, Lemma 3.4, the module `I` step).** Let `R` be noetherian
and flat over `A`, with `R ⧸ I` flat over `A`. If `f ∈ I` generates the extension of `I` to the
local ring `T` (flat over the pushout `S = R ⊗[A] A'`), then some `g ∈ R` that becomes a unit in
`T` satisfies `g • I ⊆ R • f`. -/
theorem exists_mul_eq_of_map_eq_span [IsNoetherianRing R] (I : Ideal R) [Module.Flat A (R ⧸ I)]
    {f : R} (hf : f ∈ I) (hgen : I.map (algebraMap R T) = Ideal.span {algebraMap R T f}) :
    ∃ g : R, IsUnit (algebraMap R T g) ∧ ∀ x ∈ I, ∃ r : R, g * x = r * f := by
  classical
  let ι : T ⊗[R] I →ₗ[R] T := (TensorProduct.rid R T).toLinearMap ∘ₗ (I.subtype.lTensor T)
  have hinj : Function.Injective ι := (TensorProduct.rid R T).injective.comp
    (lTensor_injective_of_flat (A := A) (A' := A') (S := S) I.subtype
      (Submodule.injective_subtype _) I.mkQ (Submodule.mkQ_surjective _)
      (LinearMap.exact_subtype_mkQ I) T)
  let f' : I := ⟨f, hf⟩
  have hι : ∀ z, ι z ∈ I.map (algebraMap R T) := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul t x =>
      simp only [ι, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearMap.lTensor_tmul, Submodule.coe_subtype, TensorProduct.rid_tmul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ x.2)
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  have hall : ∀ z : T ⊗[R] I, ∃ c : T, z = c ⊗ₜ f' := by
    intro z
    have := hι z
    rw [hgen, Ideal.mem_span_singleton'] at this
    obtain ⟨c, hc⟩ := this
    refine ⟨c, hinj ?_⟩
    rw [← hc]
    simp [ι, f', Algebra.smul_def, mul_comm]
  have hsub : Subsingleton (T ⊗[R] (I ⧸ Submodule.span R {f'})) := by
    refine ⟨fun a b => ?_⟩
    suffices h0 : ∀ w : T ⊗[R] (I ⧸ Submodule.span R {f'}), w = 0 by rw [h0 a, h0 b]
    intro w
    obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective T (Submodule.mkQ_surjective _) w
    obtain ⟨c, rfl⟩ := hall z
    rw [LinearMap.lTensor_tmul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self f'),
      TensorProduct.tmul_zero]
  obtain ⟨g, hg, hg0⟩ := exists_smul_eq_zero_of_subsingleton hsub
  refine ⟨g, hg, fun x hx => ?_⟩
  have h1 := hg0 (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_span_singleton] at h1
  obtain ⟨r, hr⟩ := h1
  exact ⟨r, by simpa [f', smul_eq_mul] using (congrArg Subtype.val hr).symm⟩

include hP in
/-- **The annihilator near the point (Kleiman, Lemma 3.4, regularity step).** Let `R` be
noetherian and flat over `A`, and let `R ⧸ (f)` be flat over `A`. If the image of `f` in the
local ring `T` (flat over the pushout `S = R ⊗[A] A'`) is regular, then the annihilator of `f`
is killed by some `g ∈ R` that becomes a unit in `T`. -/
theorem exists_mul_eq_zero_of_isSMulRegular [IsNoetherianRing R] [Module.Flat A R] (f : R)
    [Module.Flat A (R ⧸ Ideal.span {f})] (hreg : IsSMulRegular T (algebraMap R T f)) :
    ∃ g : R, IsUnit (algebraMap R T g) ∧ ∀ r : R, r * f = 0 → g * r = 0 := by
  classical
  have : Module.Flat A (Ideal.span {f}) := flat_ideal (Ideal.span {f})
  let f' : Ideal.span {f} := ⟨f, Ideal.mem_span_singleton_self f⟩
  let μ : R →ₗ[R] Ideal.span {f} := LinearMap.toSpanSingleton R _ f'
  have hμ : Function.Surjective μ := by
    rintro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    exact ⟨r, Subtype.ext (by simp [μ, f', smul_eq_mul])⟩
  have hinj := lTensor_injective_of_flat (A := A) (A' := A') (S := S) (LinearMap.ker μ).subtype
    (LinearMap.ker μ).injective_subtype μ hμ (LinearMap.exact_subtype_ker_map μ) T
  have h2 : ∀ z : T ⊗[R] R, TensorProduct.rid R T
      ((Ideal.span {f}).subtype.lTensor T (μ.lTensor T z)) =
        algebraMap R T f * TensorProduct.rid R T z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul t r =>
      simp [μ, f', Algebra.smul_def, mul_comm, mul_left_comm]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add, mul_add]
  have hsub : Subsingleton (T ⊗[R] LinearMap.ker μ) := by
    refine ⟨fun a b => ?_⟩
    suffices h0 : ∀ w : T ⊗[R] LinearMap.ker μ, w = 0 by rw [h0 a, h0 b]
    intro w
    apply hinj
    rw [map_zero]
    set z := (LinearMap.ker μ).subtype.lTensor T w
    have h1 : μ.lTensor T z = 0 := by
      have hc : μ ∘ₗ (LinearMap.ker μ).subtype = 0 :=
        LinearMap.ext fun x => LinearMap.mem_ker.mp x.2
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hc, LinearMap.lTensor_zero,
        LinearMap.zero_apply]
    have h3 := h2 z
    rw [h1, map_zero, map_zero] at h3
    have h4 : TensorProduct.rid R T z = 0 :=
      (isSMulRegular_iff_right_eq_zero_of_smul.mp hreg) _ (by rw [smul_eq_mul]; exact h3.symm)
    exact (TensorProduct.rid R T).injective (h4.trans (map_zero _).symm)
  obtain ⟨g, hg, hg0⟩ := exists_smul_eq_zero_of_subsingleton hsub
  refine ⟨g, hg, fun r hr => ?_⟩
  have hrJ : r ∈ LinearMap.ker μ := by
    rw [LinearMap.mem_ker]
    exact Subtype.ext (by simpa [μ, f', smul_eq_mul] using hr)
  simpa [smul_eq_mul] using congrArg Subtype.val (hg0 ⟨r, hrJ⟩)

end Lift

section Away

variable {R Rg : Type u} [CommRing R] [CommRing Rg] [Algebra R Rg] (g : R)
  [IsLocalization.Away g Rg]

/-- If `g • I ⊆ R • f` with `f ∈ I`, then `I` becomes principal, generated by `f`, after
inverting `g`. -/
theorem map_eq_span_of_mul_eq (I : Ideal R) {f : R} (hf : f ∈ I)
    (h : ∀ x ∈ I, ∃ r : R, g * x = r * f) :
    I.map (algebraMap R Rg) = Ideal.span {algebraMap R Rg f} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨r, hr⟩ := h x hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    have hu : IsUnit (algebraMap R Rg g) := IsLocalization.Away.algebraMap_isUnit g
    refine ⟨(hu.unit⁻¹ : Rgˣ) * algebraMap R Rg r, ?_⟩
    rw [mul_assoc, ← map_mul, ← hr, map_mul, ← mul_assoc, hu.val_inv_mul, one_mul]
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ hf

/-- If `g` kills the annihilator of `f`, then `f` becomes regular after inverting `g`. -/
theorem isSMulRegular_of_mul_eq_zero {f : R} (h : ∀ r : R, r * f = 0 → g * r = 0) :
    IsSMulRegular Rg (algebraMap R Rg f) := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro a ha
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers g) a
  rw [smul_eq_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at ha
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := ha
  have hm' : g ^ n * (f * r) = 0 := hm
  have h1 : g * (g ^ n * r) = 0 := h _ (by linear_combination hm')
  rw [IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨g * g ^ n, n + 1, show g ^ (n + 1) = g * g ^ n from pow_succ' g n⟩, by rw [mul_assoc]; exact h1⟩

end Away

end Langlands.CommutativeAlgebra.CartierLocusDescent
