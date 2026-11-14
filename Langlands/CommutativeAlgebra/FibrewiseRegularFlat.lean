import Mathlib

/-! # Fibrewise regular elements of flat local extensions -/

universe u

open TensorProduct IsLocalRing

namespace Langlands.CommutativeAlgebra.FibrewiseRegular

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Multiplication by `b` on `B`, as an `A`-linear map. -/
abbrev mulB (b : B) : B →ₗ[A] B := LinearMap.mulLeft A b

section VectorSpace

variable [IsLocalRing A]

/-- If `b` is regular on the closed fibre `B ⊗ k`, it is regular on `B ⊗ V` for every `A`-module
`V` killed by the maximal ideal. -/
theorem injective_rTensor_of_isTorsionBySet (b : B)
    (hb : Function.Injective ((mulB (A := A) b).rTensor (A ⧸ maximalIdeal A)))
    (V : Type u) [AddCommGroup V] [Module A V]
    (hV : Module.IsTorsionBySet A V (maximalIdeal A)) :
    Function.Injective ((mulB (A := A) b).rTensor V) := by
  classical
  let k := A ⧸ maximalIdeal A
  let _ : Field k := Ideal.Quotient.field _
  let _ : Module k V := hV.module
  have _ : IsScalarTower A k V := hV.isScalarTower
  let ι := Module.Free.ChooseBasisIndex k V
  let e : V ≃ₗ[A] (ι →₀ k) := (Module.Free.chooseBasis k V).repr.restrictScalars A
  let E : B ⊗[A] V ≃ₗ[A] (ι →₀ B ⊗[A] k) :=
    (LinearEquiv.lTensor B e).trans (TensorProduct.finsuppRight A A B k ι)
  have hcomm : E.toLinearMap ∘ₗ (mulB (A := A) b).rTensor V =
      (Finsupp.mapRange.linearMap ((mulB (A := A) b).rTensor k)) ∘ₗ E.toLinearMap := by
    apply TensorProduct.ext'
    intro c v
    ext i
    simp [E, LinearMap.rTensor_tmul]
  intro x y hxy
  apply E.injective
  have h := congrArg E hxy
  have h2 := congrArg (fun f => f x) hcomm
  have h3 := congrArg (fun f => f y) hcomm
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h2 h3
  rw [h2, h3] at h
  ext i
  have hi := congrArg (fun f => f i) h
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply] at hi
  exact hb hi

end VectorSpace

section Commute

/-- Multiplication by `b` commutes with `B ⊗ f`. -/
lemma rTensor_mulB_lTensor (b : B) {N P : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (f : N →ₗ[A] P) (x : B ⊗[A] N) :
    (mulB (A := A) b).rTensor P (f.lTensor B x) = f.lTensor B ((mulB (A := A) b).rTensor N x) := by
  rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

end Commute

section Power

variable [IsLocalRing A] [Module.Flat A B]

/-- If `b` is regular on the closed fibre, it is regular on `B ⊗ P` for every `A`-module `P`
killed by a power of the maximal ideal. -/
theorem injective_rTensor_of_isTorsionBySet_pow (b : B)
    (hb : Function.Injective ((mulB (A := A) b).rTensor (A ⧸ maximalIdeal A))) :
    ∀ (n : ℕ) (P : Type u) [AddCommGroup P] [Module A P],
      Module.IsTorsionBySet A P ((maximalIdeal A) ^ n : Ideal A) →
        Function.Injective ((mulB (A := A) b).rTensor P)
  | 0, P, _, _, hP => by
    have : Subsingleton P := ⟨fun x y => by
      have hx := hP (x := x) (a := ⟨1, by simp⟩)
      have hy := hP (x := y) (a := ⟨1, by simp⟩)
      simp only [one_smul] at hx hy
      rw [hx, hy]⟩
    intro x y _
    exact Subsingleton.elim _ _
  | n + 1, P, _, _, hP => by
    let N₁ : Submodule A P := (maximalIdeal A) ^ n • ⊤
    have hzero : ∀ x ∈ ((maximalIdeal A) ^ (n + 1) : Ideal A) • (⊤ : Submodule A P), x = 0 := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun a ha y _ => hP (x := y) (a := ⟨a, ha⟩)) ?_
      intro x y hx hy
      rw [hx, hy, add_zero]
    have hN₁ : Module.IsTorsionBySet A N₁ (maximalIdeal A) := by
      intro x a
      apply Subtype.ext
      apply hzero
      rw [pow_succ', Submodule.mul_smul]
      exact Submodule.smul_mem_smul a.2 x.2
    have hQ : Module.IsTorsionBySet A (P ⧸ N₁) ((maximalIdeal A) ^ n : Ideal A) := by
      intro x a
      induction x using Submodule.Quotient.induction_on with
      | H y =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul a.2 trivial
    have h₁ := injective_rTensor_of_isTorsionBySet b hb N₁ hN₁
    have h₃ := injective_rTensor_of_isTorsionBySet_pow b hb n (P ⧸ N₁) hQ
    have hι : Function.Injective (N₁.subtype.lTensor B) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ N₁.injective_subtype
    have hex : Function.Exact (N₁.subtype.lTensor B) (N₁.mkQ.lTensor B) :=
      _root_.lTensor_exact B (LinearMap.exact_subtype_mkQ N₁) (Submodule.mkQ_surjective N₁)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hq : (mulB (A := A) b).rTensor (P ⧸ N₁) (N₁.mkQ.lTensor B x) = 0 := by
      rw [rTensor_mulB_lTensor, hx, map_zero]
    have hq' : N₁.mkQ.lTensor B x = 0 := h₃ (by rw [hq, map_zero])
    obtain ⟨y, rfl⟩ := (hex x).1 hq'
    have hy : (mulB (A := A) b).rTensor N₁ y = 0 := by
      apply hι
      rw [← rTensor_mulB_lTensor, hx, map_zero]
    rw [h₁ (hy.trans (map_zero _).symm), map_zero]

end Power

section Krull

variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
  [Module.Flat A B]

omit [IsNoetherianRing B] [Module.Flat A B] in
/-- The extension of the maximal ideal of `A` lies in the maximal ideal of `B`. -/
lemma map_maximalIdeal_le : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact (IsLocalRing.mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu)

/-- **Fibrewise regularity.** If `b` is regular on the closed fibre `B ⊗ k`, it is regular on
`B ⊗ P` for every finite `A`-module `P`: by the case of modules killed by a power of the maximal
ideal and Krull's intersection theorem. -/
theorem injective_rTensor_of_finite (b : B)
    (hb : Function.Injective ((mulB (A := A) b).rTensor (A ⧸ maximalIdeal A)))
    (P : Type u) [AddCommGroup P] [Module A P] [Module.Finite A P] :
    Function.Injective ((mulB (A := A) b).rTensor P) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  let I : Ideal B := (maximalIdeal A).map (algebraMap A B)
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    map_maximalIdeal_le
  have hmem : ∀ n : ℕ, x ∈ (I ^ n • ⊤ : Submodule B (B ⊗[A] P)) := by
    intro n
    let Nn : Submodule A P := (maximalIdeal A) ^ n • ⊤
    have hQ : Module.IsTorsionBySet A (P ⧸ Nn) ((maximalIdeal A) ^ n : Ideal A) := by
      intro y a
      induction y using Submodule.Quotient.induction_on with
      | H y =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul a.2 trivial
    have h₃ := injective_rTensor_of_isTorsionBySet_pow b hb n (P ⧸ Nn) hQ
    have hex : Function.Exact (Nn.subtype.lTensor B) (Nn.mkQ.lTensor B) :=
      _root_.lTensor_exact B (LinearMap.exact_subtype_mkQ Nn) (Submodule.mkQ_surjective Nn)
    have hq : Nn.mkQ.lTensor B x = 0 :=
      h₃ (by rw [rTensor_mulB_lTensor, hx, map_zero, map_zero])
    obtain ⟨y, rfl⟩ := (hex x).1 hq
    clear hx hq
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add]; exact add_mem hy hz
    | tmul c p =>
      obtain ⟨p, hp⟩ := p
      simp only [LinearMap.lTensor_tmul, Submodule.subtype_apply]
      refine Submodule.smul_induction_on (p := fun p => c ⊗ₜ[A] p ∈
        (I ^ n • ⊤ : Submodule B (B ⊗[A] P))) hp ?_ ?_
      · intro a ha q _
        have hcq : c ⊗ₜ[A] (a • q) = (algebraMap A B a) • (c ⊗ₜ[A] q) := by
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
            Algebra.smul_def, smul_eq_mul]
        rw [hcq]
        refine Submodule.smul_mem_smul ?_ trivial
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ha
      · intro p p' hp hp'
        rw [TensorProduct.tmul_add]
        exact add_mem hp hp'
  have hK : (⨅ n : ℕ, I ^ n • ⊤ : Submodule B (B ⊗[A] P)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing I hI
  have hx' : x ∈ (⨅ n : ℕ, I ^ n • ⊤ : Submodule B (B ⊗[A] P)) := Submodule.mem_iInf _ |>.2 hmem
  rw [hK] at hx'
  exact hx'

end Krull

section Flat

variable [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
  [Module.Flat A B]

/-- A fibrewise regular element is regular. -/
theorem isSMulRegular_of_fibre (b : B)
    (hb : Function.Injective ((mulB (A := A) b).rTensor (A ⧸ maximalIdeal A))) :
    IsSMulRegular B b := by
  have h := injective_rTensor_of_finite b hb A
  intro x y hxy
  have hx : (mulB (A := A) b).rTensor A (x ⊗ₜ[A] 1) = (mulB (A := A) b).rTensor A (y ⊗ₜ[A] 1) := by
    simp only [LinearMap.rTensor_tmul, LinearMap.mulLeft_apply]
    exact congrArg (· ⊗ₜ[A] (1 : A)) hxy
  have := congrArg (TensorProduct.rid A B) (h hx)
  simpa using this

/-- **Flatness of the divisor.** For a fibrewise regular element `b`, the quotient `B ⧸ (b)` is flat
over `A`. -/
theorem flat_quotient_of_fibre (b : B)
    (hb : Function.Injective ((mulB (A := A) b).rTensor (A ⧸ maximalIdeal A))) :
    Module.Flat A (B ⧸ Ideal.span {b}) := by
  let μ := mulB (A := A) b
  let π : B →ₗ[A] B ⧸ Ideal.span {b} := (Ideal.Quotient.mkₐ A (Ideal.span {b})).toLinearMap
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective A _
  have hμπ : Function.Exact μ π := by
    intro y
    simp only [π, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton', μ]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, mul_comm _ _⟩
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  let q := (Submodule.mkQ I : A →ₗ[A] A ⧸ I)
  have hreg := injective_rTensor_of_finite b hb (A ⧸ I)
  have hι : Function.Injective (I.subtype.lTensor B) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ I.injective_subtype
  have hex₁ : Function.Exact (μ.rTensor A) (π.rTensor A) := _root_.rTensor_exact A hμπ hπ
  have hexq : Function.Exact (I.subtype.lTensor B) (q.lTensor B) :=
    _root_.lTensor_exact B (LinearMap.exact_subtype_mkQ I) (Submodule.mkQ_surjective I)
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective I hπ x
  -- the image of `y` in `B ⊗ A` lies in the image of multiplication by `b`
  have hy : π.rTensor A (I.subtype.lTensor B y) = 0 := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply]
    simpa using hx
  obtain ⟨z, hz⟩ := (hex₁ _).1 hy
  have hqz : q.lTensor B z = 0 := by
    apply hreg
    rw [map_zero, rTensor_mulB_lTensor, hz, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero, LinearMap.lTensor_zero,
      LinearMap.zero_apply]
  obtain ⟨w, rfl⟩ := (hexq z).1 hqz
  have hyw : y = μ.rTensor I w := by
    apply hι
    rw [← rTensor_mulB_lTensor, hz]
  rw [hyw, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hμπ.linearMap_comp_eq_zero,
    LinearMap.rTensor_zero, LinearMap.zero_apply]

end Flat

section Quotient

/-- Regularity on `B ⊗ (A ⧸ I)` is regularity on `B ⧸ I B`. -/
lemma injective_rTensor_quotient_iff (b : B) (I : Ideal A) :
    Function.Injective ((mulB (A := A) b).rTensor (A ⧸ I)) ↔
      IsSMulRegular (B ⧸ I.map (algebraMap A B)) b := by
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv
  have hsmul : ∀ y : B ⊗[A] (A ⧸ I), (mulB (A := A) b).rTensor (A ⧸ I) y = b • y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul c a => simp [TensorProduct.smul_tmul']
    | add y z hy hz => rw [map_add, hy, hz, smul_add]
  have he : ∀ x, (mulB (A := A) b).rTensor (A ⧸ I) (e x) = e (b • x) := by
    intro x
    rw [hsmul, map_smul]
  constructor
  · intro h x y hxy
    apply e.injective
    apply h
    rw [he, he]
    exact congrArg e hxy
  · intro h x y hxy
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := e.surjective y
    rw [he, he] at hxy
    rw [h (e.injective hxy)]

end Quotient

section Affine

variable {R : Type u} [CommRing R] [Algebra A R]

/-- **Local step.** At a prime `P` of a flat `A`-algebra `R`, an element `s` regular on the fibre
local ring `R_P ⧸ p R_P` (with `p = P ∩ A`) is regular on `R_P`, and `R_P ⧸ (s)` is flat over
`A`. -/
theorem localStep [Module.Flat A R] [IsNoetherianRing R] (s : R) (P : Ideal R) [P.IsPrime]
    (hs : IsSMulRegular (Localization.AtPrime P ⧸ (P.comap (algebraMap A R)).map
      (algebraMap A (Localization.AtPrime P))) (algebraMap R (Localization.AtPrime P) s)) :
    IsSMulRegular (Localization.AtPrime P) (algebraMap R (Localization.AtPrime P) s) ∧
      Module.Flat A (Localization.AtPrime P ⧸
        Ideal.span {algebraMap R (Localization.AtPrime P) s}) := by
  let p := P.comap (algebraMap A R)
  let Ap := Localization.AtPrime p
  let RP := Localization.AtPrime P
  let φ : Ap →+* RP := Localization.localRingHom p P (algebraMap A R) rfl
  let _ : Algebra Ap RP := φ.toAlgebra
  have hφA : ∀ a : A, φ (algebraMap A Ap a) = algebraMap A RP a := by
    intro a
    rw [Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply A R RP]
  have : IsScalarTower A Ap RP := .of_algebraMap_eq (fun a => (hφA a).symm)
  have : IsLocalHom (algebraMap Ap RP) :=
    Localization.isLocalHom_localRingHom p P (algebraMap A R) rfl
  have : Module.Flat Ap RP :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr inferInstance) P p rfl
  have hb : Function.Injective
      ((mulB (A := Ap) (algebraMap R RP s)).rTensor (Ap ⧸ maximalIdeal Ap)) := by
    rw [injective_rTensor_quotient_iff, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact hs
  refine ⟨isSMulRegular_of_fibre _ hb, ?_⟩
  have := flat_quotient_of_fibre (A := Ap) _ hb
  exact Module.Flat.trans A Ap _

/-- **Affine relative divisor criterion.** Let `R` be a noetherian flat `A`-algebra and `s ∈ R`
regular in every fibre local ring `R_P ⧸ (P ∩ A) R_P` at maximal ideals `P`. Then `s` is regular
in `R` and `R ⧸ (s)` is flat over `A`. -/
theorem regular_and_flat_quotient [Module.Flat A R] [IsNoetherianRing R] (s : R)
    (hs : ∀ (P : Ideal R) [P.IsMaximal], IsSMulRegular (Localization.AtPrime P ⧸
      (P.comap (algebraMap A R)).map (algebraMap A (Localization.AtPrime P)))
        (algebraMap R (Localization.AtPrime P) s)) :
    IsSMulRegular R s ∧ Module.Flat A (R ⧸ Ideal.span {s}) := by
  constructor
  · intro x y hxy
    rw [← sub_eq_zero]
    by_contra hne
    have hann : (Submodule.span R {x - y}).annihilator ≠ ⊤ := by
      intro h
      apply hne
      have h1 : (1 : R) ∈ (Submodule.span R {x - y}).annihilator := h ▸ Submodule.mem_top
      rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
      exact h1
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hann
    have hreg := (localStep s P (hs P)).1
    have h0 : algebraMap R (Localization.AtPrime P) (x - y) = 0 := by
      apply hreg
      simp only [smul_eq_mul, mul_zero, ← map_mul, mul_sub]
      change algebraMap R _ (s * x - s * y) = 0
      rw [show s * x = s * y from hxy, sub_self, map_zero]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl _ _).1 h0
    apply m.2
    apply hle
    rw [Submodule.mem_annihilator_span_singleton]
    exact hm
  · let I : Ideal R := Ideal.span {s}
    let Mₚ := fun (P : Ideal R) [P.IsMaximal] => Localization.AtPrime P ⧸
      I.map (algebraMap R (Localization.AtPrime P))
    let f := fun (P : Ideal R) [P.IsMaximal] =>
      ((IsScalarTower.toAlgHom R (R ⧸ I) (Mₚ P)).toLinearMap)
    have : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P) := by
      intro P _
      exact (isLocalizedModule_iff_isLocalization (S := P.primeCompl)).mpr inferInstance
    refine Module.flat_of_isLocalized_maximal (R := A) (S := R) (M := R ⧸ I) (Mₚ := Mₚ) (f := f)
      (fun P _ => ?_)
    have hI : I.map (algebraMap R (Localization.AtPrime P)) =
        Ideal.span {algebraMap R (Localization.AtPrime P) s} := by
      rw [Ideal.map_span, Set.image_singleton]
    have := (localStep s P (hs P)).2
    change Module.Flat A (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))
    rw [hI]
    exact this

end Affine

end Langlands.CommutativeAlgebra.FibrewiseRegular
