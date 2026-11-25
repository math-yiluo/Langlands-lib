/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Free
import Mathlib.RingTheory.TensorProduct.Free
import WeilConjectures.Algebra.Homology.MinimalComplex

/-! # Spreading local contractions with free complementary kernels

Source: Stacks Project, More on Algebra, Tag 068U, `lemma-cut-complex-in-two`,
and Algebra, Tag 00NX, finite projective modules and local freeness.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u v
open TensorProduct CategoryTheory
open scoped ChangeOfRings
private theorem spread_mid
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {X Y Z : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    [Module.Free R X] [Module.Free R Y] [Module.Free R Z]
    [Module.Finite R X] [Module.Finite R Y] [Module.Finite R Z]
    (a : X →ₗ[R] Y) (b : Y →ₗ[R] Z)
    (s : TensorProduct R (Localization.AtPrime p) Y →ₗ[Localization.AtPrime p]
      TensorProduct R (Localization.AtPrime p) X)
    (t : TensorProduct R (Localization.AtPrime p) Z →ₗ[Localization.AtPrime p]
      TensorProduct R (Localization.AtPrime p) Y)
    (hmid : (a.baseChange (Localization.AtPrime p)).comp s +
      t.comp (b.baseChange (Localization.AtPrime p)) = LinearMap.id) :
    ∃ (f : R) (_ : f ∉ p) (s₀ : Y →ₗ[R] X) (t₀ : Z →ₗ[R] Y),
      a.comp s₀ + t₀.comp b = f • LinearMap.id := by
  let L := Localization.AtPrime p
  let lX := TensorProduct.mk R L X 1
  let lY := TensorProduct.mk R L Y 1
  let lZ := TensorProduct.mk R L Z 1
  have : Module.FinitePresentation R Y := Module.finitePresentation_of_projective R Y
  have : Module.FinitePresentation R Z := Module.finitePresentation_of_projective R Z
  obtain ⟨ψs, cs, hψs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    p.primeCompl lX (s.restrictScalars R ∘ₗ lY)
  obtain ⟨ψt, ct, hψt⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule
    p.primeCompl lY (t.restrictScalars R ∘ₗ lZ)
  let c : p.primeCompl := cs * ct
  let s₀ := ct.1 • ψs
  let t₀ := cs.1 • ψt
  have hs (y : Y) : lX (s₀ y) = c.1 • s (lY y) := by
    have hh := LinearMap.congr_fun hψs y
    change lX (ψs y) = cs.1 • s (lY y) at hh
    simp only [s₀, LinearMap.smul_apply, map_smul, hh, c, Submonoid.coe_mul,
      ← mul_smul, mul_comm ct.1 cs.1]
  have ht (z : Z) : lY (t₀ z) = c.1 • t (lZ z) := by
    have hh := LinearMap.congr_fun hψt z
    change lY (ψt z) = ct.1 • t (lZ z) at hh
    simp only [t₀, LinearMap.smul_apply, map_smul, hh, c, Submonoid.coe_mul, ← mul_smul]
  have heq : lY.comp (a.comp s₀ + t₀.comp b) = lY.comp (c.1 • LinearMap.id) := by
    ext y
    change lY (a (s₀ y) + t₀ (b y)) = lY (c.1 • y)
    rw [map_smul]
    calc
      _ = a.baseChange L (lX (s₀ y)) + lY (t₀ (b y)) := by simp [lX, lY, TensorProduct.tmul_add]
      _ = a.baseChange L (c.1 • s (lY y)) + c.1 • t (lZ (b y)) := by rw [hs, ht]
      _ = c.1 • (a.baseChange L (s (lY y)) + t (b.baseChange L (lY y))) := by
        simp [lY, lZ, smul_add]
      _ = c.1 • lY y := by
        exact congrArg (c.1 • ·) (LinearMap.congr_fun hmid (lY y))
  obtain ⟨d, hd⟩ := Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule
    p.primeCompl lY (a.comp s₀ + t₀.comp b) (c.1 • LinearMap.id) heq
  change d.1 • (a.comp s₀ + t₀.comp b) = d.1 • (c.1 • LinearMap.id) at hd
  refine ⟨d.1 * c.1, p.primeCompl.mul_mem d.2 c.2, d.1 • s₀, d.1 • t₀, ?_⟩
  simpa only [LinearMap.comp_smul, LinearMap.smul_comp, smul_add, mul_smul] using hd

set_option backward.isDefEq.respectTransparency false in
private theorem coker_equiv_ker_scaled
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {X : Type v} [AddCommGroup X] [Module R X]
    (q : X →ₗ[R] X) (f : R) (hq : q.comp q = f • q)
    (hf : IsUnit (algebraMap R A f)) :
    Nonempty (TensorProduct R A (X ⧸ LinearMap.range q) ≃ₗ[A]
      LinearMap.ker (q.baseChange A)) := by
  let Q := q.baseChange A
  let u : A := ↑(hf.unit⁻¹)
  have hu : u * algebraMap R A f = 1 := IsUnit.val_inv_mul hf
  have hQ : Q.comp Q = (algebraMap R A f) • Q := by
    have h := congrArg (LinearMap.baseChange A) hq
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_smul, algebraMap_smul]
      using h
  have hQx (x : TensorProduct R A X) : Q (Q x) = algebraMap R A f • Q x :=
    LinearMap.congr_fun hQ x
  let p : TensorProduct R A X →ₗ[A] LinearMap.ker Q :=
    (LinearMap.id - u • Q).codRestrict _ (by
      intro x
      change Q (x - u • Q x) = 0
      rw [map_sub, map_smul, hQx, smul_smul, hu, one_smul, sub_self])
  have hpker : LinearMap.ker p = LinearMap.range Q := by
    ext x
    constructor
    · intro hx
      have hh : x - u • Q x = 0 := congrArg Subtype.val hx
      refine ⟨u • x, ?_⟩
      rw [map_smul]
      exact (sub_eq_zero.mp hh).symm
    · rintro ⟨x, rfl⟩
      apply Subtype.ext
      change Q x - u • Q (Q x) = 0
      rw [hQx, smul_smul, hu, one_smul, sub_self]
  have hpsurj : Function.Surjective p := by
    intro x
    refine ⟨x.val, ?_⟩
    apply Subtype.ext
    change x.val - u • Q x.val = x.val
    rw [LinearMap.mem_ker.mp x.property, smul_zero, sub_zero]
  let π := (LinearMap.range q).mkQ.baseChange A
  have hπsurj : Function.Surjective π :=
    LinearMap.baseChange_surjective A (Submodule.mkQ_surjective _)
  have hExact : Function.Exact Q π :=
    lTensor_exact A (LinearMap.exact_map_mkQ_range q) (Submodule.mkQ_surjective _)
  have hπker : LinearMap.ker π = LinearMap.range Q := LinearMap.exact_iff.mp hExact
  exact ⟨(π.quotKerEquivOfSurjective hπsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ (hπker.trans hpker.symm)).trans
      (p.quotKerEquivOfSurjective hpsurj))⟩

set_option backward.isDefEq.respectTransparency false in
private theorem free_baseChange_of_unit
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {M : Type v} [AddCommGroup M] [Module R M]
    (g : R) (hg : IsUnit (algebraMap R A g))
    (hfree : Module.Free (Localization.Away g) (LocalizedModule.Away g M)) :
    Module.Free A (TensorProduct R A M) := by
  have := hfree
  let B := Localization.Away g
  let : Algebra B A := (IsLocalization.Away.lift g hg).toAlgebra
  have : IsScalarTower R B A := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (IsLocalization.Away.lift_eq g hg r).symm)
  have : Module.Free B (TensorProduct R B M) :=
    Module.Free.of_equiv (LocalizedModule.equivTensorProduct (.powers g) M)
  exact Module.Free.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B A A M)

set_option backward.isDefEq.respectTransparency false in
private theorem free_coker_atPrime_scaled
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {X : Type v} [AddCommGroup X] [Module R X]
    [Module.Free R X] [Module.Finite R X]
    (q : X →ₗ[R] X) (f : R) (hf : f ∉ p) (hq : q.comp q = f • q) :
    Module.Free (Localization.AtPrime p)
      (TensorProduct R (Localization.AtPrime p) (X ⧸ LinearMap.range q)) := by
  let L := Localization.AtPrime p
  have hunit : IsUnit (algebraMap R L f) := IsLocalization.map_units L (⟨f, hf⟩ : p.primeCompl)
  let u : L := ↑(hunit.unit⁻¹)
  have hu : IsUnit u := (hunit.unit⁻¹).isUnit
  have huf : u * algebraMap R L f = 1 := IsUnit.val_inv_mul hunit
  let Q := q.baseChange L
  have hQ : Q.comp Q = algebraMap R L f • Q := by
    have h := congrArg (LinearMap.baseChange L) hq
    simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_smul, algebraMap_smul]
      using h
  let e : TensorProduct R L X →ₗ[L] TensorProduct R L X := u • Q
  have he : IsIdempotentElem e := by
    change (u • Q).comp (u • Q) = u • Q
    rw [LinearMap.smul_comp, LinearMap.comp_smul, hQ]
    simp only [smul_smul]
    have hcoef : u * (u * algebraMap R L f) = u := by
      rw [huf, mul_one]
    rw [hcoef]
  have heker : LinearMap.ker e = LinearMap.ker Q := by
    ext x
    simp only [e, LinearMap.mem_ker, LinearMap.smul_apply, hu.smul_eq_zero]
  have hker : Module.Free L (LinearMap.ker Q) := by
    rw [← heker]
    exact (LinearMap.free_and_finite_ker_of_isIdempotentElem he).1
  obtain ⟨iso⟩ := coker_equiv_ker_scaled q f hq hunit
  exact Module.Free.of_equiv iso.symm

set_option backward.isDefEq.respectTransparency false in
private theorem one_kernel_basis_near
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {X : Type v} [AddCommGroup X] [Module R X]
    [Module.Free R X] [Module.Finite R X]
    (q : X →ₗ[R] X) (f : R) (hf : f ∉ p) (hq : q.comp q = f • q) :
    ∃ g : R, g ∉ p ∧ ∀ (A : Type u) [CommRing A] [Algebra R A],
      IsUnit (algebraMap R A g) → IsUnit (algebraMap R A f) →
        Module.Free A (LinearMap.ker (q.baseChange A)) := by
  let C := X ⧸ LinearMap.range q
  have : Module.FinitePresentation R C :=
    Module.finitePresentation_of_free_of_surjective (LinearMap.range q).mkQ
      (Submodule.mkQ_surjective _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.fg_range q)
  let L := Localization.AtPrime p
  let lC := TensorProduct.mk R L C 1
  have : Module.Free L (TensorProduct R L C) := free_coker_atPrime_scaled p q f hf hq
  obtain ⟨g, hg, hgfree, _⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl lC L
  refine ⟨g, hg, ?_⟩
  intro A _ _ hgunit hfunit
  have : Module.Free A (TensorProduct R A C) := free_baseChange_of_unit g hgunit hgfree
  obtain ⟨iso⟩ := coker_equiv_ker_scaled q f hq hfunit
  exact Module.Free.of_equiv iso

/-- Two scaled idempotents have free kernels on a common principal neighborhood. -/
private theorem free_scaled_kernels
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] (f : R) (hf : f ∉ p)
    {X Z : Type v} [AddCommGroup X] [Module R X] [AddCommGroup Z] [Module R Z]
    [Module.Free R X] [Module.Free R Z] [Module.Finite R X] [Module.Finite R Z]
    (q : X →ₗ[R] X) (r : Z →ₗ[R] Z)
    (hq : q.comp q = f • q) (hr : r.comp r = f • r) :
    ∃ g : R, g ∉ p ∧
      Module.Free (Localization.Away (f * g))
        (LinearMap.ker (q.baseChange (Localization.Away (f * g)))) ∧
      Module.Free (Localization.Away (f * g))
        (LinearMap.ker (r.baseChange (Localization.Away (f * g)))) := by
  obtain ⟨g₁, hg₁, hqnear⟩ := one_kernel_basis_near p q f hf hq
  obtain ⟨g₂, hg₂, hrnear⟩ := one_kernel_basis_near p r f hf hr
  let g := g₁ * g₂
  let A := Localization.Away (f * g)
  have hunit : IsUnit (algebraMap R A (f * g)) :=
    IsLocalization.Away.algebraMap_isUnit (f * g)
  have hfunit : IsUnit (algebraMap R A f) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R A) ⟨g, rfl⟩) hunit
  have hg₁unit : IsUnit (algebraMap R A g₁) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R A) ⟨f * g₂, by dsimp [g]; ac_rfl⟩) hunit
  have hg₂unit : IsUnit (algebraMap R A g₂) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R A) ⟨f * g₁, by dsimp [g]; ac_rfl⟩) hunit
  exact ⟨g, p.primeCompl.mul_mem hg₁ hg₂,
    hqnear A hg₁unit hfunit, hrnear A hg₂unit hfunit⟩

private theorem spread_pair
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    {X Y Z : Type v} [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
    [Module.Free R X] [Module.Free R Y] [Module.Free R Z]
    [Module.Finite R X] [Module.Finite R Y] [Module.Finite R Z]
    (a : X →ₗ[R] Y) (b : Y →ₗ[R] Z) (hab : b.comp a = 0)
    (s : TensorProduct R (Localization.AtPrime p) Y →ₗ[Localization.AtPrime p]
      TensorProduct R (Localization.AtPrime p) X)
    (t : TensorProduct R (Localization.AtPrime p) Z →ₗ[Localization.AtPrime p]
      TensorProduct R (Localization.AtPrime p) Y)
    (hmid : (a.baseChange (Localization.AtPrime p)).comp s +
      t.comp (b.baseChange (Localization.AtPrime p)) = LinearMap.id) :
    ∃ F : R, F ∉ p ∧
      ∃ (s : TensorProduct R (Localization.Away F) Y →ₗ[Localization.Away F]
          TensorProduct R (Localization.Away F) X)
        (t : TensorProduct R (Localization.Away F) Z →ₗ[Localization.Away F]
          TensorProduct R (Localization.Away F) Y),
      (a.baseChange (Localization.Away F)).comp (s.comp (a.baseChange
        (Localization.Away F))) = a.baseChange (Localization.Away F) ∧
      t.comp ((b.baseChange (Localization.Away F)).comp t) = t ∧
      (a.baseChange (Localization.Away F)).comp s +
        t.comp (b.baseChange (Localization.Away F)) = LinearMap.id ∧
      Module.Free (Localization.Away F)
        (LinearMap.ker (s.comp (a.baseChange (Localization.Away F)))) ∧
      Module.Free (Localization.Away F)
        (LinearMap.ker ((b.baseChange (Localization.Away F)).comp t)) := by
  obtain ⟨f, hf, s₀, t₀, h₀⟩ := spread_mid p a b s t hmid
  have has₀ : a.comp (s₀.comp a) = f • a := by
    have h := congrArg (fun h : Y →ₗ[R] Y ↦ h.comp a) h₀
    simpa only [LinearMap.add_comp, LinearMap.comp_assoc, hab, LinearMap.comp_zero,
      add_zero, LinearMap.smul_comp, LinearMap.id_comp] using h
  have hbt₀ : b.comp (t₀.comp b) = f • b := by
    have h := congrArg (fun h : Y →ₗ[R] Y ↦ b.comp h) h₀
    simpa only [LinearMap.comp_add, ← LinearMap.comp_assoc, hab, LinearMap.zero_comp,
      zero_add, LinearMap.comp_smul, LinearMap.comp_id] using h
  let q := s₀.comp a
  let r := b.comp t₀
  have hq : q.comp q = f • q := by
    change (s₀.comp a).comp (s₀.comp a) = f • (s₀.comp a)
    rw [LinearMap.comp_assoc, has₀, LinearMap.comp_smul]
  have hr : r.comp r = f • r := by
    change (b.comp t₀).comp (b.comp t₀) = f • (b.comp t₀)
    simpa only [LinearMap.comp_assoc, LinearMap.smul_comp] using
      congrArg (fun h : Y →ₗ[R] Z ↦ h.comp t₀) hbt₀
  obtain ⟨g, hg, hqfree, hrfree⟩ := free_scaled_kernels p f hf q r hq hr
  let F := f * g
  let A := Localization.Away F
  have huF : IsUnit (algebraMap R A F) := IsLocalization.Away.algebraMap_isUnit F
  have huf : IsUnit (algebraMap R A f) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap R A) ⟨g, rfl⟩) huF
  let u : A := ↑(huf.unit⁻¹)
  have hufinv : u * algebraMap R A f = 1 := IsUnit.val_inv_mul huf
  have hu : IsUnit u := (huf.unit⁻¹).isUnit
  let a₁ := a.baseChange A
  let b₁ := b.baseChange A
  let s₁ := u • s₀.baseChange A
  let t₁ := u • t₀.baseChange A
  have hab₁ : b₁.comp a₁ = 0 := by
    rw [← LinearMap.baseChange_comp, hab, LinearMap.baseChange_zero]
  have hmid₁ : a₁.comp s₁ + t₁.comp b₁ = LinearMap.id := by
    change a₁.comp (u • s₀.baseChange A) + (u • t₀.baseChange A).comp b₁ = _
    rw [LinearMap.comp_smul, LinearMap.smul_comp, ← smul_add]
    change u • ((a.baseChange A).comp (s₀.baseChange A) +
      (t₀.baseChange A).comp (b.baseChange A)) = _
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_add, h₀, LinearMap.baseChange_smul,
      LinearMap.baseChange_id, ← algebraMap_smul A f, smul_smul, hufinv, one_smul]
  have has₁ : a₁.comp (s₁.comp a₁) = a₁ := by
    have h := congrArg (fun h ↦ h.comp a₁) hmid₁
    simpa only [LinearMap.add_comp, LinearMap.comp_assoc, hab₁, LinearMap.comp_zero,
      add_zero, LinearMap.id_comp] using h
  have hbt₁ : b₁.comp (t₁.comp b₁) = b₁ := by
    have h := congrArg (fun h ↦ b₁.comp h) hmid₁
    simpa only [LinearMap.comp_add, ← LinearMap.comp_assoc, hab₁,
      LinearMap.zero_comp, zero_add, LinearMap.comp_id] using h
  let t₂ := t₁.comp (b₁.comp t₁)
  have hbt_apply (y : TensorProduct R A Y) : b₁ (t₁ (b₁ y)) = b₁ y :=
    LinearMap.congr_fun hbt₁ y
  have htb₂ : t₂.comp (b₁.comp t₂) = t₂ := by
    apply LinearMap.ext
    intro x
    simp only [t₂, LinearMap.comp_apply, hbt_apply]
  have hmid₂ : a₁.comp s₁ + t₂.comp b₁ = LinearMap.id := by
    apply LinearMap.ext
    intro y
    have h := LinearMap.congr_fun hmid₁ y
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      t₂, hbt_apply] using h
  have hkerq : LinearMap.ker (s₁.comp a₁) = LinearMap.ker (q.baseChange A) := by
    ext x
    simp only [s₁, LinearMap.smul_comp, LinearMap.mem_ker, LinearMap.smul_apply,
      hu.smul_eq_zero, q, a₁, LinearMap.baseChange_comp]
  have hkerr : LinearMap.ker (b₁.comp t₂) = LinearMap.ker (r.baseChange A) := by
    have heq : b₁.comp t₂ = u • r.baseChange A := by
      simp only [t₂, ← LinearMap.comp_assoc, hbt₁,
        t₁, LinearMap.comp_smul, r, LinearMap.baseChange_comp, b₁]
    rw [heq]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, hu.smul_eq_zero]
  refine ⟨F, p.primeCompl.mul_mem hf hg, s₁, t₂, has₁, htb₂, hmid₂, ?_, ?_⟩
  · rw [hkerq]
    exact hqfree
  · rw [hkerr]
    exact hrfree

private theorem free_kernel_transport
    {A : Type u} [CommRing A] {M N : Type v}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (q : M →ₗ[A] M) (r : N →ₗ[A] N)
    (h : ∀ x, r (e x) = e (q x)) (hf : Module.Free A (LinearMap.ker q)) :
    Module.Free A (LinearMap.ker r) := by
  have := hf
  have heq : LinearMap.ker q = (LinearMap.ker r).comap e.toLinearMap := by
    ext x
    change q x = 0 ↔ r (e x) = 0
    rw [h]
    constructor
    · intro hx
      rw [hx, map_zero]
    · intro hx
      exact e.injective (hx.trans (map_zero e).symm)
  exact Module.Free.of_equiv ((LinearEquiv.ofEq _ _ heq).trans
    (e.ofSubmodule' (LinearMap.ker r)))

private theorem pair_transport
    {A : Type u} [CommRing A] {X Y Z X' Y' Z' : Type v}
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    [AddCommGroup Z] [Module A Z] [AddCommGroup X'] [Module A X']
    [AddCommGroup Y'] [Module A Y'] [AddCommGroup Z'] [Module A Z']
    (eX : X ≃ₗ[A] X') (eY : Y ≃ₗ[A] Y') (eZ : Z ≃ₗ[A] Z')
    (a : X →ₗ[A] Y) (b : Y →ₗ[A] Z) (a' : X' →ₗ[A] Y') (b' : Y' →ₗ[A] Z')
    (ha : ∀ x, a' (eX x) = eY (a x)) (hb : ∀ y, b' (eY y) = eZ (b y))
    (s : Y →ₗ[A] X) (t : Z →ₗ[A] Y)
    (has : a.comp (s.comp a) = a) (htb : t.comp (b.comp t) = t)
    (hm : a.comp s + t.comp b = LinearMap.id)
    (hfX : Module.Free A (LinearMap.ker (s.comp a)))
    (hfZ : Module.Free A (LinearMap.ker (b.comp t))) :
    ∃ (s' : Y' →ₗ[A] X') (t' : Z' →ₗ[A] Y'),
      a'.comp (s'.comp a') = a' ∧ t'.comp (b'.comp t') = t' ∧
      a'.comp s' + t'.comp b' = LinearMap.id ∧
      Module.Free A (LinearMap.ker (s'.comp a')) ∧
      Module.Free A (LinearMap.ker (b'.comp t')) := by
  let s' := eX.toLinearMap.comp (s.comp eY.symm.toLinearMap)
  let t' := eY.toLinearMap.comp (t.comp eZ.symm.toLinearMap)
  have hs (y : Y) : s' (eY y) = eX (s y) := by simp [s']
  have ht (z : Z) : t' (eZ z) = eY (t z) := by simp [t']
  refine ⟨s', t', ?_, ?_, ?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro x'
    obtain ⟨x, rfl⟩ := eX.surjective x'
    change a' (s' (a' (eX x))) = a' (eX x)
    rw [ha, hs, ha]
    exact congrArg eY (LinearMap.congr_fun has x)
  · apply LinearMap.ext
    intro z'
    obtain ⟨z, rfl⟩ := eZ.surjective z'
    change t' (b' (t' (eZ z))) = t' (eZ z)
    rw [ht, hb, ht]
    exact congrArg eY (LinearMap.congr_fun htb z)
  · apply LinearMap.ext
    intro y'
    obtain ⟨y, rfl⟩ := eY.surjective y'
    change a' (s' (eY y)) + t' (b' (eY y)) = eY y
    rw [hs, ha, hb, ht, ← map_add]
    exact congrArg eY (LinearMap.congr_fun hm y)
  · exact free_kernel_transport eX (s.comp a) (s'.comp a')
      (fun x ↦ by change s' (a' (eX x)) = eX (s (a x)); rw [ha, hs]) hfX
  · exact free_kernel_transport eZ (b.comp t) (b'.comp t')
      (fun z ↦ by change b' (t' (eZ z)) = eZ (b (t z)); rw [ht, hb]) hfZ

private noncomputable def tensorExtendEquiv (R : Type u) (S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{max u v} R) :
    TensorProduct R S N ≃ₗ[S] (ModuleCat.extendScalars (algebraMap R S)).obj N := by
  let T := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let toFun : TensorProduct R S N →ₗ[R] TensorProduct R S' N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S' N s
        map_add' s s' := (TensorProduct.mk R S' N).map_add s s'
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S' N) (Algebra.smul_def r s)).trans
            ((TensorProduct.mk R S' N).map_smul r (s : S')) }
  let invFun : TensorProduct R S' N →ₗ[R] TensorProduct R S N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S N (show S from s)
        map_add' s s' := (TensorProduct.mk R S N).map_add (show S from s) (show S from s')
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S N) (Algebra.smul_def r (show S from s)).symm).trans
            ((TensorProduct.mk R S N).map_smul r (show S from s)) }
  have h₁ : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add
      map_smul' s x := by
        induction x using TensorProduct.inductionOn with
        | tmul s' n => rfl
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add]
          exact (smul_add s _ _).symm
      left_inv := h₁
      right_inv := h₂ }

set_option backward.isDefEq.respectTransparency false in
private theorem tensorExtend_naturality
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (X Y : ModuleCat.{max u v} R) (a : X ⟶ Y) (x : TensorProduct R S X) :
    ((ModuleCat.extendScalars (algebraMap R S)).map a).hom (tensorExtendEquiv R S X x) =
      tensorExtendEquiv R S Y (a.hom.baseChange S x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

namespace ModuleCat

set_option backward.isDefEq.respectTransparency false in
/-- A local middle contraction spreads to a principal open with free complements.

Source: Stacks Project, More on Algebra, Tag 068U, `lemma-cut-complex-in-two`,
and Algebra, Tag 00NX, `lemma-finite-projective`.
(auxiliary; not a blueprint node)

Proof: Finite presentation lifts the local s,t after multiplying them by a
common denominator outside p. Finiteness clears the error in their middle
identity. Thus there are actual R-linear s0,t0 and f outside p with
A s0+t0 B=f. The equation BA=0 makes q=s0 A and r=B t0 satisfy q²=fq and r²=fr.
For either scaled projector q, its finitely presented cokernel becomes its
kernel after f is inverted: the map 1-q/f induces this equivalence explicitly.
At p the normalized projector is idempotent, so its kernel is finite free over
the local ring. Spread a basis of the cokernel to a principal neighborhood by
Module.FinitePresentation.exists_free_localizedModule_powers, and base change
it to the product of f and the two resulting elements. The cokernel-kernel
equivalence makes both desired kernels free there. Divide s0,t0 by f, and
replace t by tBt. The middle identity and BA=0 give AsA=A, BtB=B, tBt=t,
and unchanged kernel of Bt. Transport all maps and free kernels through the
explicit comparison of tensor products with categorical extension of scalars.
Empty bases and zero cokernels are included in these constructions. -/
theorem exists_principal_contraction_of_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (X Y Z : ModuleCat.{max u v} R) (a : X ⟶ Y) (b : Y ⟶ Z) (hab : a ≫ b = 0)
    (hX : Module.Free R X) (hY : Module.Free R Y) (hZ : Module.Free R Z)
    (hfX : Module.Finite R X) (hfY : Module.Finite R Y) (hfZ : Module.Finite R Z)
    (s : (ModuleCat.extendScalars.{u, u, max u v}
        (algebraMap R (Localization.AtPrime p))).obj Y ⟶
      (ModuleCat.extendScalars.{u, u, max u v}
        (algebraMap R (Localization.AtPrime p))).obj X)
    (t : (ModuleCat.extendScalars.{u, u, max u v}
        (algebraMap R (Localization.AtPrime p))).obj Z ⟶
      (ModuleCat.extendScalars.{u, u, max u v}
        (algebraMap R (Localization.AtPrime p))).obj Y)
    (hmid : s ≫ (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))).map a +
      (ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))).map b ≫ t =
        𝟙 ((ModuleCat.extendScalars (algebraMap R (Localization.AtPrime p))).obj Y)) :
    ∃ f : R, f ∉ p ∧
      let E := ModuleCat.extendScalars.{u, u, max u v} (algebraMap R (Localization.Away f))
      ∃ (s : E.obj Y ⟶ E.obj X) (t : E.obj Z ⟶ E.obj Y),
        E.map a ≫ s ≫ E.map a = E.map a ∧
        t ≫ E.map b ≫ t = t ∧
        s ≫ E.map a + E.map b ≫ t = 𝟙 (E.obj Y) ∧
        Module.Free (Localization.Away f) (LinearMap.ker (E.map a ≫ s).hom) ∧
        Module.Free (Localization.Away f) (LinearMap.ker (t ≫ E.map b).hom) := by
  have := hX
  have := hY
  have := hZ
  have := hfX
  have := hfY
  have := hfZ
  let L := Localization.AtPrime p
  let eX := tensorExtendEquiv R L X
  let eY := tensorExtendEquiv R L Y
  let eZ := tensorExtendEquiv R L Z
  let sL := eX.symm.toLinearMap.comp (s.hom.comp eY.toLinearMap)
  let tL := eY.symm.toLinearMap.comp (t.hom.comp eZ.toLinearMap)
  have hsL (y : TensorProduct R L Y) : eX (sL y) = s.hom (eY y) := by
    simp only [sL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have htL (z : TensorProduct R L Z) : eY (tL z) = t.hom (eZ z) := by
    simp only [tL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rfl
  have hmL : (a.hom.baseChange L).comp sL + tL.comp (b.hom.baseChange L) =
      LinearMap.id := by
    apply LinearMap.ext
    intro y
    apply eY.injective
    change eY (a.hom.baseChange L (sL y) + tL (b.hom.baseChange L y)) = eY y
    rw [map_add, ← tensorExtend_naturality R L X Y a, hsL, htL,
      ← tensorExtend_naturality R L Y Z b]
    exact congrArg (fun g ↦ g.hom (eY y)) hmid
  have hba : b.hom.comp a.hom = 0 := congrArg ModuleCat.Hom.hom hab
  obtain ⟨F, hF, sF, tF, hsF, htF, hmF, hfXF, hfZF⟩ :=
    spread_pair p a.hom b.hom hba sL tL hmL
  let A := Localization.Away F
  let E := ModuleCat.extendScalars.{u, u, max u v} (algebraMap R A)
  obtain ⟨s', t', hs', ht', hm', hfX', hfZ'⟩ := pair_transport
    (tensorExtendEquiv R A X) (tensorExtendEquiv R A Y) (tensorExtendEquiv R A Z)
    (a.hom.baseChange A) (b.hom.baseChange A) (E.map a).hom (E.map b).hom
    (tensorExtend_naturality R A X Y a) (tensorExtend_naturality R A Y Z b)
    sF tF hsF htF hmF hfXF hfZF
  exact ⟨F, hF, ModuleCat.ofHom s', ModuleCat.ofHom t',
    ModuleCat.hom_ext hs', ModuleCat.hom_ext ht', ModuleCat.hom_ext hm', hfX', hfZ'⟩

end ModuleCat
