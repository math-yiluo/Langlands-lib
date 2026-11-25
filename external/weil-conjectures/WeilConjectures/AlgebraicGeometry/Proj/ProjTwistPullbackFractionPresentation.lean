/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
public import WeilConjectures.AlgebraicGeometry.Proj.ProjTwistFractionTensor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.Proj.ProjTwistQuasicoherent
import WeilConjectures.AlgebraicGeometry.ProjTwistFractionDescent
import WeilConjectures.AlgebraicGeometry.ProjTwistFractionRealization
import WeilConjectures.AlgebraicGeometry.ProjBasicOpenLocalizationDetection

/-! # A fraction presentation of pullback sections on a Proj chart

## References

* Stacks Project, Tags 01MY and 01N2, the standard-open calculation, and Tag 01M7 for the associated
  graded-module sheaf
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

private theorem fraction_mem_shifted
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
    {n : ℕ} {f : A} (hf : f ∈ 𝒜 n) (hn : 0 < n) (j : ℤ)
    (z : twistChartFractionSubmodule 𝒜 n f j) :
    (z : Localization.Away f) ∈ LocalizedModule.degreeZeroFractions
      (fun k : ℕ ↦ (𝒜 k : Set A))
      (fun k : ℕ ↦ {a : A | if 0 ≤ j + k then a ∈ 𝒜 (j + k).toNat else a = 0})
      (Submonoid.powers f) := by
  obtain ⟨m, i, a, hi, ha, hz⟩ := twistChartFraction_representative 𝒜 hf hn j z
  refine ⟨m * n, a, ⟨f ^ m, ⟨m, rfl⟩⟩, ?_, ?_, hz⟩
  · have hj : 0 ≤ j + (m * n : ℕ) := by omega
    have he : (j + (m * n : ℕ)).toNat = i := by omega
    simpa only [Set.mem_ofPred_eq, ite_eq_left hj, he] using ha
  · simpa using SetLike.pow_mem_graded m hf

private theorem exists_fraction_section_map
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]
    {n : ℕ} {f : A} (hf : f ∈ 𝒜 n) (hn : 0 < n) (j : ℤ) :
    ∃ e : twistChartFractionSubmodule 𝒜 n f j →+ Γ(twist 𝒜 j, basicOpen 𝒜 f),
      Function.Surjective e ∧
      (∀ (z : twistChartFractionSubmodule 𝒜 n f j) (y : basicOpen 𝒜 f),
        IsLocalization.map (M := Submonoid.powers f)
          (T := y.1.asHomogeneousIdeal.toIdeal.primeCompl)
          (Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
          (Submonoid.powers_le.mpr y.2) (z : Localization.Away f) = ((e z).1 y).val) ∧
      ∀ (r : R) (z : twistChartFractionSubmodule 𝒜 n f j),
        e (r • z) = awayToSection 𝒜 f
          (algebraMap R (HomogeneousLocalization.Away 𝒜 f) r) • e z := by
  classical
  let ev (y : basicOpen 𝒜 f) : Localization.Away f →+*
      Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal :=
    IsLocalization.map (M := Submonoid.powers f)
      (T := y.1.asHomogeneousIdeal.toIdeal.primeCompl) _ (RingHom.id A)
      (Submonoid.powers_le.mpr y.2)
  have ex (z : twistChartFractionSubmodule 𝒜 n f j) :=
    twist_fraction_realization 𝒜 j f z (fraction_mem_shifted 𝒜 hf hn j z)
  let t (z : twistChartFractionSubmodule 𝒜 n f j) := (ex z).choose
  have ht (z : twistChartFractionSubmodule 𝒜 n f j) (y : basicOpen 𝒜 f) :
      ev y z = ((t z).1 y).val := (ex z).choose_spec y
  let e : twistChartFractionSubmodule 𝒜 n f j →+ Γ(twist 𝒜 j, basicOpen 𝒜 f) :=
    { toFun := t
      map_zero' := by
        apply Subtype.ext
        funext y
        apply Subtype.ext
        exact (ht 0 y).symm.trans (map_zero (ev y))
      map_add' := by
        intro z w
        apply Subtype.ext
        funext y
        apply Subtype.ext
        exact (ht (z + w) y).symm.trans
          ((map_add (ev y) (z : Localization.Away f) (w : Localization.Away f)).trans
            (congrArg₂ (· + ·) (ht z y) (ht w y))) }
  refine ⟨e, ?_, ht, ?_⟩
  · intro s
    obtain ⟨z, hz, hs⟩ := twist_fraction_descent 𝒜 j f n hn hf s
    have hz' : z ∈ twistChartFractionSubmodule 𝒜 n f j := by
      by_cases hU : Nonempty (basicOpen 𝒜 f)
      · obtain ⟨d, a, den, ha, hd, rfl⟩ := hz
        obtain ⟨m, hm⟩ := den.2
        have hden : (den : A) ≠ 0 := by
          intro hzero
          obtain ⟨y⟩ := hU
          have hy := (Submonoid.powers_le.mpr y.2 : Submonoid.powers f ≤
            y.1.asHomogeneousIdeal.toIdeal.primeCompl) den.2
          exact hy (hzero ▸ y.1.asHomogeneousIdeal.toIdeal.zero_mem)
        have hdegree : d = m * n := DirectSum.degree_eq_of_mem_mem 𝒜 hd
          (by simpa [← hm] using SetLike.pow_mem_graded m hf) hden
        subst d
        by_cases hj : 0 ≤ j + (m * n : ℕ)
        · apply Submodule.subset_span
          refine ⟨m, (j + (m * n : ℕ)).toNat, a, ?_, ?_, ?_⟩
          · simpa only [Nat.cast_mul] using Int.toNat_of_nonneg hj
          · simpa only [Set.mem_ofPred_eq, ite_eq_left hj] using ha
          · change Localization.mk a _ = Localization.mk a den
            congr 1
            exact Subtype.ext hm
        · have ha0 : a = 0 := by simpa only [Set.mem_ofPred_eq, ite_eq_right hj] using ha
          rw [ha0, LocalizedModule.zero_mk]
          exact Submodule.zero_mem _
      · have hz0 : z = 0 := by
          apply basicOpen_localization_detection 𝒜 f n hn hf
          intro y
          exact (hU ⟨y⟩).elim
        rw [hz0]
        exact Submodule.zero_mem _
    refine ⟨⟨z, hz'⟩, Subtype.ext (funext fun y ↦ Subtype.ext ?_)⟩
    exact (ht ⟨z, hz'⟩ y).symm.trans (hs y)
  · intro r z
    apply Subtype.ext
    funext y
    apply Subtype.ext
    change ((t (r • z)).1 y).val =
      ((awayToSection 𝒜 f (algebraMap R (HomogeneousLocalization.Away 𝒜 f) r)).1 y).val *
        ((t z).1 y).val
    rw [← ht, ← ht]
    change ev y (r • (z : Localization.Away f)) = _
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact (ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 f
      (algebraMap R (HomogeneousLocalization.Away 𝒜 f) r) y).symm

private theorem tensor_coefficient_presentation
    {R S C D H M : Type u} [CommRing R] [CommRing S] [CommRing C] [CommRing D]
    [Algebra R S] [Algebra C D] [AddCommGroup H] [Module R H]
    [AddCommGroup M] [Module C M]
    (a : R →+* C) (b : S →+* D)
    (hab : ∀ r : R, b (algebraMap R S r) = algebraMap C D (a r))
    (e : H →+ M) (hes : Function.Surjective e)
    (her : ∀ r z, e (r • z) = a r • e z)
    (hspan : Submodule.span C (Set.range b) = ⊤) :
    ∃ q : TensorProduct R S H →+ TensorProduct C M D,
      Function.Surjective q ∧ ∀ s z, q (TensorProduct.tmul R s z) =
        TensorProduct.tmul C (e z) (b s) := by
  let bi : S →+ H →+ TensorProduct C M D :=
    { toFun := fun s ↦
        { toFun := fun z ↦ TensorProduct.tmul C (e z) (b s)
          map_zero' := by simp
          map_add' := by intros; simp [TensorProduct.add_tmul] }
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp [TensorProduct.tmul_add] }
  have hbi (r : R) (s : S) (z : H) : bi (r • s) z = bi s (r • z) := by
    change TensorProduct.tmul C (e z) (b (r • s)) =
      TensorProduct.tmul C (e (r • z)) (b s)
    rw [Algebra.smul_def, map_mul, hab, her, TensorProduct.smul_tmul, Algebra.smul_def]
  let q := TensorProduct.liftAddHom bi hbi
  have hq (s : S) (z : H) : q (TensorProduct.tmul R s z) =
      TensorProduct.tmul C (e z) (b s) := rfl
  refine ⟨q, ?_, hq⟩
  have ht (d : D) : ∀ t : M, ∃ x, q x = TensorProduct.tmul C t d := by
    have hd : d ∈ Submodule.span C (Set.range b) := by rw [hspan]; trivial
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨s, rfl⟩ := hd
      intro t
      obtain ⟨z, rfl⟩ := hes t
      exact ⟨TensorProduct.tmul R s z, hq s z⟩
    | zero => intro t; exact ⟨0, by simp⟩
    | add d d' hd hd' ih ih' =>
      intro t
      obtain ⟨x, hx⟩ := ih t
      obtain ⟨x', hx'⟩ := ih' t
      exact ⟨x + x', by rw [map_add, hx, hx', TensorProduct.tmul_add]⟩
    | smul c d hd ih =>
      intro t
      obtain ⟨x, hx⟩ := ih (c • t)
      exact ⟨x, by rw [hx, TensorProduct.smul_tmul, TensorProduct.tmul_smul]⟩
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul t d => exact ht d t
  | add x y hx hy =>
    obtain ⟨z, rfl⟩ := hx
    obtain ⟨z', rfl⟩ := hy
    exact ⟨z + z', map_add q z z'⟩

private theorem chart_coefficients_span
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hgraded : ∀ k : ℕ, ℬ k = Submodule.span S (ψ '' (𝒜 k : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ
      (HomogeneousIdeal.irrelevant 𝒜))
    {n : ℕ} {f : A} (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    let U := basicOpen 𝒜 f
    let V := basicOpen ℬ (ψ f)
    let : Algebra Γ(Proj 𝒜, U) Γ(Proj ℬ, V) :=
      ((map ψ hψ).appLE U V le_rfl).hom.toAlgebra
    Submodule.span Γ(Proj 𝒜, U)
      (Set.range ((awayToSection ℬ (ψ f)).hom.comp
        (algebraMap S (HomogeneousLocalization.Away ℬ (ψ f))))) = ⊤ := by
  classical
  let U := basicOpen 𝒜 f
  let V := basicOpen ℬ (ψ f)
  let C := Γ(Proj 𝒜, U)
  let D := Γ(Proj ℬ, V)
  let : Algebra C D := ((map ψ hψ).appLE U V le_rfl).hom.toAlgebra
  let b : S →+* D := (awayToSection ℬ (ψ f)).hom.comp
    (algebraMap S (HomogeneousLocalization.Away ℬ (ψ f)))
  let p : Submodule C D := Submodule.span C (Set.range b)
  have h1 : (1 : D) ∈ p := Submodule.subset_span ⟨1, map_one b⟩
  have hmul (s : S) (d : D) (hd : d ∈ p) : b s * d ∈ p := by
    change d ∈ Submodule.span C (Set.range b) at hd
    induction hd using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨s', rfl⟩ := hd
      rw [← map_mul]
      exact Submodule.subset_span ⟨s * s', rfl⟩
    | zero => simpa only [mul_zero] using p.zero_mem
    | add x y hx hy ih ih' => simpa only [mul_add] using p.add_mem ih ih'
    | smul c d hd ih =>
      change b s * (algebraMap C D c * d) ∈ p
      rw [← mul_assoc, mul_comm (b s), mul_assoc]
      exact p.smul_mem c ih
  let num (m : ℕ) : ℬ (m • n) →ₗ[S] HomogeneousLocalization.Away ℬ (ψ f) :=
    { toFun := fun a ↦ HomogeneousLocalization.Away.mk ℬ (ψ.map_mem hf) m a a.property
      map_add' := by
        intro x y
        apply HomogeneousLocalization.val_injective
        simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_add,
          Submodule.coe_add]
        exact (Localization.add_mk_self _ _ _).symm
      map_smul' := by
        intro s a
        apply HomogeneousLocalization.val_injective
        simp only [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_smul,
          Submodule.coe_smul]
        exact (Localization.smul_mk s (a : B) _).symm }
  let l (m : ℕ) : ℬ (m • n) →+ D :=
    (awayToSection ℬ (ψ f)).hom.toAddMonoidHom.comp (num m).toAddMonoidHom
  have hl (m : ℕ) (s : S) (a : ℬ (m • n)) : l m (s • a) = b s * l m a := by
    change (awayToSection ℬ (ψ f))
      (num m (s • a)) = _
    rw [(num m).map_smul, Algebra.smul_def, map_mul]
    rfl
  have hfrac (m : ℕ) (a : B) (ha : a ∈ ℬ (m • n)) : l m ⟨a, ha⟩ ∈ p := by
    rw [hgraded] at ha
    induction ha using Submodule.span_induction with
    | mem a hgen =>
      obtain ⟨a, hsource, rfl⟩ := hgen
      let q := HomogeneousLocalization.Away.mk 𝒜 hf m a hsource
      have he : l m ⟨ψ a, ψ.map_mem hsource⟩ =
          algebraMap C D (awayToSection 𝒜 f q) := by
        change (awayToSection ℬ (ψ f)).hom
            (HomogeneousLocalization.Away.mk ℬ (ψ.map_mem hf) m (ψ a)
              (ψ.map_mem hsource)) =
          ((map ψ hψ).appLE U V le_rfl).hom ((awayToSection 𝒜 f).hom q)
        have he := congrArg (fun h ↦ h.hom q) (awayToSection_comp_appLE ψ hψ hf)
        simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
          q, HomogeneousLocalization.Away.map_mk] using he.symm
      rw [he]
      simpa only [Algebra.smul_def, mul_one] using
        p.smul_mem (awayToSection 𝒜 f q) h1
    | zero => simpa only [show (⟨0, _⟩ : ℬ _) = 0 from rfl, map_zero] using p.zero_mem
    | add x y hx hy ih ih' =>
      have hx' : x ∈ ℬ (m • n) := by rw [hgraded]; exact hx
      have hy' : y ∈ ℬ (m • n) := by rw [hgraded]; exact hy
      exact (show l m (⟨x, hx'⟩ + ⟨y, hy'⟩) ∈ p by
        rw [map_add]; exact p.add_mem (ih hx') (ih' hy'))
    | smul s x hx ih =>
      have hx' : x ∈ ℬ (m • n) := by rw [hgraded]; exact hx
      rw [show (⟨s • x, _⟩ : ℬ _) = s • ⟨x, hx'⟩ from rfl, hl]
      exact hmul s _ (ih hx')
  apply top_unique
  intro d _
  obtain ⟨q, rfl⟩ :=
    (ConcreteCategory.bijective_of_isIso (basicOpenIsoAway ℬ (ψ f) (ψ.map_mem hf) hn).hom).2 d
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective ℬ (ψ.map_mem hf) q
  exact hfrac m a ha

/-- Pullback chart sections are generated by coefficient tensors of homogeneous fractions.
The assertion is a surjective presentation, with no assertion about its kernel and no
morphism from the pullback to the target twist. -/
theorem exists_twistPullback_fraction_presentation
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ
      (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ) (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    let U := basicOpen 𝒜 f
    let V := basicOpen ℬ (ψ f)
    let hVU : V ≤ map ψ hψ ⁻¹ᵁ U :=
      le_of_eq (map_preimage_basicOpen ψ hψ f).symm
    ∃ c : TensorProduct R S (twistChartFractionSubmodule 𝒜 n f j) →+
        Γ((tensorPullback (map ψ hψ)).obj (twist 𝒜 j), V),
      Function.Surjective c ∧
      ∀ z : twistChartFractionSubmodule 𝒜 n f j,
        ∃ t : Γ(twist 𝒜 j, U),
          (∀ y : U,
            IsLocalization.map (M := Submonoid.powers f)
              (T := y.1.asHomogeneousIdeal.toIdeal.primeCompl)
              (Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) (RingHom.id A)
              (Submonoid.powers_le.mpr y.2) (z : Localization.Away f) = (t.1 y).val) ∧
          ∀ s : S,
            c (TensorProduct.tmul R s z) =
              awayToSection ℬ (ψ f)
                  (algebraMap S (HomogeneousLocalization.Away ℬ (ψ f)) s) •
                ((tensorPullback (map ψ hψ)).obj (twist 𝒜 j)).presheaf.map
                  (homOfLE hVU).op
                  (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U t) := by
  classical
  dsimp only
  let U := basicOpen 𝒜 f
  let V := basicOpen ℬ (ψ f)
  let r := map ψ hψ
  have hVU : V ≤ r ⁻¹ᵁ U := le_rfl
  let C := Γ(Proj 𝒜, U)
  let D := Γ(Proj ℬ, V)
  let : Algebra C D := (r.appLE U V hVU).hom.toAlgebra
  let a : R →+* C := (awayToSection 𝒜 f).hom.comp
    (algebraMap R (HomogeneousLocalization.Away 𝒜 f))
  let b : S →+* D := (awayToSection ℬ (ψ f)).hom.comp
    (algebraMap S (HomogeneousLocalization.Away ℬ (ψ f)))
  have hψR (x : R) : ψ (algebraMap R A x) =
      algebraMap S B (algebraMap R S x) := by
    rw [← hβψ, ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact β.commutes (algebraMap R S x)
  have hcoef (x : R) :
      HomogeneousLocalization.Away.map ψ f
        (algebraMap R (HomogeneousLocalization.Away 𝒜 f) x) =
      algebraMap S (HomogeneousLocalization.Away ℬ (ψ f)) (algebraMap R S x) := by
    change HomogeneousLocalization.Away.map ψ f
      (HomogeneousLocalization.fromZeroRingHom 𝒜 _ (algebraMap R (𝒜 0) x)) = _
    rw [← RingHom.comp_apply, HomogeneousLocalization.Away.map_comp_fromZeroRingHom]
    apply HomogeneousLocalization.val_injective
    simp only [RingHom.comp_apply, HomogeneousLocalization.val_fromZeroRingHom,
      GradedRingHom.coe_gradeZeroRingHom_apply, SetLike.GradeZero.coe_algebraMap,
      HomogeneousLocalization.val_algebraMap, hψR]
  have hab (x : R) : b (algebraMap R S x) = algebraMap C D (a x) := by
    have he := congrArg (fun h ↦ h.hom
      (algebraMap R (HomogeneousLocalization.Away 𝒜 f) x))
      (awayToSection_comp_appLE ψ hψ hf)
    change (awayToSection ℬ (ψ f)).hom
        (algebraMap S (HomogeneousLocalization.Away ℬ (ψ f)) (algebraMap R S x)) =
      (r.appLE U V hVU).hom ((awayToSection 𝒜 f).hom
        (algebraMap R (HomogeneousLocalization.Away 𝒜 f) x))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, hcoef]
      using he.symm
  obtain ⟨e, hes, he, her⟩ := exists_fraction_section_map 𝒜 hf hn j
  obtain ⟨q, hqs, hq⟩ := tensor_coefficient_presentation a b hab e hes her
    (chart_coefficients_span 𝒜 ℬ ψ hgraded hψ hf hn)
  let G := twist 𝒜 j
  have hG : G.IsQuasicoherent := isQuasicoherent_twist 𝒜 j
  let : ∀ F : (Proj 𝒜).Modules, Module C Γ((tensorPullback r).obj F, V) :=
    fun F ↦ Module.compHom _ (r.appLE U V hVU).hom
  obtain ⟨c, hc, _, hct, _⟩ := exists_tensorPullback_affine_sections r
    ⟨U, isAffineOpen_basicOpen 𝒜 f hf hn⟩
    ⟨V, isAffineOpen_basicOpen ℬ (ψ f) (ψ.map_mem hf) hn⟩ hVU
  refine ⟨(c G hG).toAddMonoidHom.comp q, (hc G hG).2.comp hqs, ?_⟩
  intro z
  refine ⟨e z, he z, ?_⟩
  intro s
  change c G hG (q (TensorProduct.tmul R s z)) =
    b s • ((tensorPullback r).obj G).presheaf.map (homOfLE hVU).op
      (tensorPullbackSection r G U (e z))
  rw [hq, hct]
  have hu : ((Classical.choose (exists_tensorPullbackAdjunction r)).unit.app G).val.app
      (op U) (e z) = tensorPullbackSection r G U (e z) :=
    (Classical.choose_spec (exists_tensorPullbackAdjunction r)) G (op U) (e z)
  rw [hu]

end AlgebraicGeometry.Proj
