/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.Abel
import all WeilConjectures.CategoryTheory.Abelian.HorseshoeDefectFactorization

/-!
# Horseshoe morphism lifts from exact augmented source complexes

Source: the classical horseshoe comparison argument, using Stacks Project, Tags 0136 and
013R; the Cartan--Eilenberg construction of Tag 015I motivates its application
(blueprint: lem-weil-pbc-horseshoe-morphism-lift-exact-source).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

private theorem source_zero
    {C : Type u} [Category.{v} C] [Abelian C] {U : C} {X : CochainComplex C ℕ}
    (s : (CochainComplex.single₀ C).obj U ⟶ X) : s.f 0 ≫ X.d 0 1 = 0 := by
  simp

set_option backward.isDefEq.respectTransparency false in
private theorem exact_source_defect
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (_hT : T.ShortExact) (F : S ⟶ T)
    (XA XB XC : CochainComplex C ℕ)
    (sA : (CochainComplex.single₀ C).obj S.X₁ ⟶ XA)
    (sB : (CochainComplex.single₀ C).obj S.X₂ ⟶ XB)
    (sC : (CochainComplex.single₀ C).obj S.X₃ ⟶ XC)
    [QuasiIso sA] [QuasiIso sB] [QuasiIso sC]
    (i : XA ⟶ XB) (p : XB ⟶ XC) (hip : i ≫ p = 0)
    (hi : sA ≫ i = (CochainComplex.single₀ C).map S.f ≫ sB)
    (hp : sB ≫ p = (CochainComplex.single₀ C).map S.g ≫ sC)
    (hexact : ∀ n : ℕ,
      ((ShortComplex.mk i p hip).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (JA : InjectiveResolution T.X₁) (JB : InjectiveResolution T.X₂)
    (JC : InjectiveResolution T.X₃)
    (α' : JA.cocomplex ⟶ JB.cocomplex) (β' : JB.cocomplex ⟶ JC.cocomplex)
    (hiβ' : α' ≫ β' = 0)
    (hα' : JA.ι ≫ α' = (CochainComplex.single₀ C).map T.f ≫ JB.ι)
    (hβ' : JB.ι ≫ β' = (CochainComplex.single₀ C).map T.g ≫ JC.ι)
    (hexact' : ∀ n : ℕ,
      ((ShortComplex.mk α' β' hiβ').map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (φA : XA ⟶ JA.cocomplex) (φC : XC ⟶ JC.cocomplex)
    (hφA : sA ≫ φA = (CochainComplex.single₀ C).map F.τ₁ ≫ JA.ι)
    (hφC : sC ≫ φC = (CochainComplex.single₀ C).map F.τ₃ ≫ JC.ι)
    (t : ∀ n, XB.X n ⟶ JB.cocomplex.X n)
    (hti : ∀ n, i.f n ≫ t n = φA.f n ≫ α'.f n)
    (htp : ∀ n, t n ≫ β'.f n = p.f n ≫ φC.f n) :
    ∃ (E : ∀ n, XC.X n ⟶ JA.cocomplex.X (n + 1))
      (e : S.X₃ ⟶ JA.cocomplex.X 0),
      (∀ n, p.f n ≫ E n ≫ α'.f (n + 1) =
        t n ≫ JB.cocomplex.d n (n + 1) - XB.d n (n + 1) ≫ t (n + 1)) ∧
      S.g ≫ e ≫ α'.f 0 =
        sB.f 0 ≫ t 0 - ((CochainComplex.single₀ C).map F.τ₂ ≫ JB.ι).f 0 ∧
      sC.f 0 ≫ E 0 = e ≫ JA.cocomplex.d 0 1 ∧
      ∀ n, XC.d n (n + 1) ≫ E (n + 1) =
        -(E n ≫ JA.cocomplex.d (n + 1) (n + 2)) := by
  classical
  let R (n : ℕ) : ShortComplex C := ShortComplex.mk (i.f n) (p.f n)
    (by simpa using HomologicalComplex.congr_hom hip n)
  let R' (n : ℕ) : ShortComplex C := ShortComplex.mk (α'.f n) (β'.f n)
    (by simpa using HomologicalComplex.congr_hom hiβ' n)
  have hr (n : ℕ) : (R n).ShortExact := hexact n
  have hr' (n : ℕ) : (R' n).ShortExact := hexact' n
  let D (n : ℕ) := t n ≫ JB.cocomplex.d n (n + 1) -
    XB.d n (n + 1) ≫ t (n + 1)
  have hDi (n : ℕ) : i.f n ≫ D n = 0 := by
    dsimp [D]
    rw [Preadditive.comp_sub, ← Category.assoc, hti, Category.assoc,
      α'.comm, ← Category.assoc, φA.comm, Category.assoc,
      ← Category.assoc (i.f n), i.comm, Category.assoc, hti, sub_self]
  have hDp (n : ℕ) : D n ≫ β'.f (n + 1) = 0 := by
    dsimp [D]
    rw [Preadditive.sub_comp, Category.assoc, ← β'.comm,
      ← Category.assoc, htp, Category.assoc, φC.comm,
      ← Category.assoc, p.comm]
    simp only [Category.assoc, htp, sub_self]
  have hfac (n : ℕ) := factor_through_rows (R n) (R' (n + 1))
    (hr n) (hr' (n + 1)) (D n) (hDi n) (hDp n)
  choose E hEfac using hfac
  dsimp only [R, R'] at hEfac
  have hEcoc (n : ℕ) : XC.d n (n + 1) ≫ E (n + 1) =
      -(E n ≫ JA.cocomplex.d (n + 1) (n + 2)) := by
    have : Epi (p.f n) := (hr n).epi_g
    have : Mono (α'.f (n + 2)) := (hr' (n + 2)).mono_f
    rw [← cancel_epi (p.f n), ← cancel_mono (α'.f (n + 2))]
    simp only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp]
    rw [reassoc_of% (p.comm n (n + 1)), ← α'.comm,
      ← Category.assoc (E n), ← Category.assoc (p.f n), hEfac]
    simp only [Category.assoc]
    rw [← Category.assoc (p.f n) (E n),
      ← Category.assoc (p.f n ≫ E n)]
    have hEfac' : (p.f n ≫ E n) ≫ α'.f (n + 1) = D n := by
      simpa only [Category.assoc] using hEfac n
    rw [hEfac']
    simp only [D, Preadditive.comp_sub, Preadditive.sub_comp, ← Category.assoc,
      HomologicalComplex.d_comp_d, zero_comp, sub_zero]
    rw [Category.assoc (t n), HomologicalComplex.d_comp_d, comp_zero, zero_sub,
      neg_neg]
  let a₀ : S.X₁ ⟶ XA.X 0 := sA.f 0
  let b₀ : S.X₂ ⟶ XB.X 0 := sB.f 0
  let c₀ : S.X₃ ⟶ XC.X 0 := sC.f 0
  let a₀' : T.X₁ ⟶ JA.cocomplex.X 0 := JA.ι.f 0
  let b₀' : T.X₂ ⟶ JB.cocomplex.X 0 := JB.ι.f 0
  let c₀' : T.X₃ ⟶ JC.cocomplex.X 0 := JC.ι.f 0
  have hsi : a₀ ≫ i.f 0 = S.f ≫ b₀ := by
    simpa using HomologicalComplex.congr_hom hi 0
  have hsp : b₀ ≫ p.f 0 = S.g ≫ c₀ := by
    simpa using HomologicalComplex.congr_hom hp 0
  have hsα' : a₀' ≫ α'.f 0 = T.f ≫ b₀' := by
    simpa using HomologicalComplex.congr_hom hα' 0
  have hsβ' : b₀' ≫ β'.f 0 = T.g ≫ c₀' := by
    simpa using HomologicalComplex.congr_hom hβ' 0
  have hsφA : a₀ ≫ φA.f 0 = F.τ₁ ≫ a₀' := by
    simpa using HomologicalComplex.congr_hom hφA 0
  have hsφC : c₀ ≫ φC.f 0 = F.τ₃ ≫ c₀' := by
    simpa using HomologicalComplex.congr_hom hφC 0
  let w : S.X₂ ⟶ JB.cocomplex.X 0 := b₀ ≫ t 0 - F.τ₂ ≫ b₀'
  have hwf : S.f ≫ w = 0 := by
    dsimp [w]
    rw [Preadditive.comp_sub, ← Category.assoc, ← hsi, Category.assoc,
      hti, ← Category.assoc, hsφA, Category.assoc, hsα',
      ← Category.assoc, F.comm₁₂, Category.assoc, sub_self]
  have hwp : w ≫ β'.f 0 = 0 := by
    dsimp [w]
    rw [Preadditive.sub_comp, Category.assoc, htp,
      ← Category.assoc, hsp, Category.assoc, hsφC,
      Category.assoc, hsβ', ← Category.assoc, ← F.comm₂₃, Category.assoc, sub_self]
  obtain ⟨e, hef⟩ := factor_through_rows S (R' 0) hS (hr' 0) w hwf hwp
  have heaug : c₀ ≫ E 0 = e ≫ JA.cocomplex.d 0 1 := by
    have := hS.epi_g
    have : Mono (α'.f 1) := (hr' 1).mono_f
    rw [← cancel_epi S.g, ← cancel_mono (α'.f 1)]
    simp only [Category.assoc]
    rw [← reassoc_of% hsp, hEfac]
    dsimp [D]
    rw [Preadditive.comp_sub]
    rw [reassoc_of% (show b₀ ≫ XB.d 0 1 = 0 from
      source_zero sB), zero_comp, sub_zero, ← α'.comm]
    dsimp only [R'] at hef
    rw [reassoc_of% hef]
    dsimp [w]
    simp only [Preadditive.sub_comp, Category.assoc,
      show b₀' ≫ JB.cocomplex.d 0 1 = 0 from JB.ι_f_zero_comp_complex_d,
      comp_zero, sub_zero]
  refine ⟨E, e, hEfac, ?_, heaug, hEcoc⟩
  simpa [w, b₀, b₀'] using hef

private theorem signed_primitive
    {C : Type u} [Category.{v} C] [Abelian C] {U V : C}
    (X : CochainComplex C ℕ)
    (s : (CochainComplex.single₀ C).obj U ⟶ X)
    [Mono (s.f 0)]
    (hex₀ : (ShortComplex.mk (s.f 0) (X.d 0 1) (source_zero s)).Exact)
    (hex : ∀ n, (X.sc' n (n + 1) (n + 2)).Exact)
    (J : InjectiveResolution V)
    (e : U ⟶ J.cocomplex.X 0)
    (E : ∀ n, X.X n ⟶ J.cocomplex.X (n + 1))
    (he : s.f 0 ≫ E 0 = e ≫ J.cocomplex.d 0 1)
    (hE : ∀ n, X.d n (n + 1) ≫ E (n + 1) =
      -(E n ≫ J.cocomplex.d (n + 1) (n + 2))) :
    ∃ k : ∀ n, X.X n ⟶ J.cocomplex.X n,
      s.f 0 ≫ k 0 = e ∧
      ∀ n, X.d n (n + 1) ≫ k (n + 1) =
        k n ≫ J.cocomplex.d n (n + 1) - E n := by
  classical
  let k₀ : X.X 0 ⟶ J.cocomplex.X 0 :=
    Injective.factorThru e (s.f 0)
  have hk₀ : s.f 0 ≫ k₀ = e := Injective.comp_factorThru _ _
  have hzero : s.f 0 ≫ (k₀ ≫ J.cocomplex.d 0 1 - E 0) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hk₀, he, sub_self]
  let k₁ : X.X 1 ⟶ J.cocomplex.X 1 :=
    hex₀.descToInjective (k₀ ≫ J.cocomplex.d 0 1 - E 0) hzero
  have hk₁ : X.d 0 1 ≫ k₁ = k₀ ≫ J.cocomplex.d 0 1 - E 0 :=
    hex₀.comp_descToInjective _ _
  have step (n : ℕ)
      (a : X.X n ⟶ J.cocomplex.X n)
      (b : X.X (n + 1) ⟶ J.cocomplex.X (n + 1))
      (hab : X.d n (n + 1) ≫ b =
        a ≫ J.cocomplex.d n (n + 1) - E n) :
      ∃ c : X.X (n + 2) ⟶ J.cocomplex.X (n + 2),
        X.d (n + 1) (n + 2) ≫ c =
          b ≫ J.cocomplex.d (n + 1) (n + 2) - E (n + 1) := by
    have hz : X.d n (n + 1) ≫
        (b ≫ J.cocomplex.d (n + 1) (n + 2) - E (n + 1)) = 0 := by
      rw [Preadditive.comp_sub, ← Category.assoc, hab, Preadditive.sub_comp,
        Category.assoc, HomologicalComplex.d_comp_d, comp_zero, zero_sub, hE,
        sub_self]
    exact ⟨(hex n).descToInjective _ hz,
      (hex n).comp_descToInjective _ hz⟩
  choose next hnext using step
  let pairs : ∀ n, Σ' (a : X.X n ⟶ J.cocomplex.X n)
      (b : X.X (n + 1) ⟶ J.cocomplex.X (n + 1)),
      X.d n (n + 1) ≫ b = a ≫ J.cocomplex.d n (n + 1) - E n :=
    fun n ↦ Nat.rec ⟨k₀, k₁, hk₁⟩ (fun n p ↦
      ⟨p.2.1, next n p.1 p.2.1 p.2.2, hnext n p.1 p.2.1 p.2.2⟩) n
  refine ⟨fun n ↦ (pairs n).1, hk₀, ?_⟩
  intro n
  exact (pairs n).2.2


/-- Prescribed endpoint maps from exact augmented complexes into a target horseshoe
extend to a compatible middle map. The source terms need not be injective.
Augmentations are chain maps from `single₀`; their quasi-isomorphism conditions mean
exactness of the augmented sequences, including monicity of the degree-zero augmentation.
Natural-number indexing represents the displayed nonnegative-degree complexes.
The target horseshoe data use the same declarations and equations as
`exists_horseshoe_morphism_lift`.

Source: the classical horseshoe comparison calculation, using Stacks Project, Tags 0136
and 013R, in the setting of the Cartan--Eilenberg construction of Tag 015I
(blueprint: lem-weil-pbc-horseshoe-morphism-lift-exact-source).

Proof:
1. By lem-weil-pbc-ses-injective-kernel-splits, split the target row in each degree,
   choosing a section sigma' of beta'. Extend phiA^n across the source monomorphism
   i^n into JA^n by injectivity (def-sp-injective-resolutions), obtaining t^n.
   Set chi^n = alpha'^n t^n + sigma'^n phiC^n p^n in ordinary composition order.
   Then chi i = alpha' phiA and beta' chi = phiC p.
2. By row exactness in the abelian category (def-sp-abelian), the differential defect
   D = d' chi - chi d factors uniquely as D^n = alpha'^{n+1} E^n p^n.
   The identity d' D = -D d gives d' E + E d = 0. Likewise the augmentation defect
   w = chi^0 sB - sB' b factors as alpha'^0 e g, with E^0 sC = d' e.
3. The quasi-isomorphism sC gives monicity of sC^0, exactness of (sC^0, dC^0),
   and exactness of XC in every positive degree. Extend e along sC^0 into JA^0
   to obtain k^0. The augmentation identity gives sC^0 (d' k^0 - E^0) = 0,
   so exactness and injectivity give k^1 with k^1 dC^0 = d' k^0 - E^0.
   Inductively, dC^n annihilates d' k^{n+1} - E^{n+1}, by d'^2 = 0 and
   d' E^n = -E^{n+1} dC^n. Exactness and injectivity give k^{n+2}.
   Recursion on consecutive pairs constructs all k^n, with e = k^0 sC and
   E^n = d' k^n - k^{n+1} d. This is the successive-extension argument of Tag 013R.
4. Set phiB^n = chi^n - alpha'^n k^n p^n. These identities kill the differential
   and augmentation defects. The zero composites beta' alpha' and p i preserve
   both outer squares. Thus phiB is the required augmented middle chain map. -/
theorem exists_horseshoe_morphism_lift_exact_source
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact) (F : S ⟶ T)
    (XA XB XC : CochainComplex C ℕ)
    (sA : (CochainComplex.single₀ C).obj S.X₁ ⟶ XA)
    (sB : (CochainComplex.single₀ C).obj S.X₂ ⟶ XB)
    (sC : (CochainComplex.single₀ C).obj S.X₃ ⟶ XC)
    [QuasiIso sA] [QuasiIso sB] [QuasiIso sC]
    (i : XA ⟶ XB) (p : XB ⟶ XC) (hip : i ≫ p = 0)
    (hi : sA ≫ i = (CochainComplex.single₀ C).map S.f ≫ sB)
    (hp : sB ≫ p = (CochainComplex.single₀ C).map S.g ≫ sC)
    (hexact : ∀ n : ℕ,
      ((ShortComplex.mk i p hip).map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (JA : InjectiveResolution T.X₁) (JB : InjectiveResolution T.X₂)
    (JC : InjectiveResolution T.X₃)
    (α' : JA.cocomplex ⟶ JB.cocomplex) (β' : JB.cocomplex ⟶ JC.cocomplex)
    (hαβ' : α' ≫ β' = 0)
    (hα' : JA.ι ≫ α' = (CochainComplex.single₀ C).map T.f ≫ JB.ι)
    (hβ' : JB.ι ≫ β' = (CochainComplex.single₀ C).map T.g ≫ JC.ι)
    (hexact' : ∀ n : ℕ,
      ((ShortComplex.mk α' β' hαβ').map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (φA : XA ⟶ JA.cocomplex) (φC : XC ⟶ JC.cocomplex)
    (hφA : sA ≫ φA = (CochainComplex.single₀ C).map F.τ₁ ≫ JA.ι)
    (hφC : sC ≫ φC = (CochainComplex.single₀ C).map F.τ₃ ≫ JC.ι) :
    ∃ φB : XB ⟶ JB.cocomplex,
      sB ≫ φB = (CochainComplex.single₀ C).map F.τ₂ ≫ JB.ι ∧
      i ≫ φB = φA ≫ α' ∧ φB ≫ β' = p ≫ φC := by
  classical
  have hzero := source_zero sC
  have hex₀ : (ShortComplex.mk (sC.f 0) (XC.d 0 1) hzero).Exact ∧ Mono (sC.f 0) := by
    have h : ShortComplex.QuasiIso
        ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ) 0 0 1).map sC) :=
      (CochainComplex.quasiIsoAt₀_iff sC).mp (inferInstance : QuasiIsoAt sC 0)
    exact (ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp) (by simp)).mp h
  have : Mono (sC.f 0) := hex₀.2
  have hex (n : ℕ) : (XC.sc' n (n + 1) (n + 2)).Exact := by
    have h : XC.ExactAt (n + 1) :=
      (exactAt_iff_of_quasiIsoAt sC (n + 1)).mp
        (CochainComplex.exactAt_succ_single_obj S.X₃ n)
    exact (HomologicalComplex.exactAt_iff' XC n (n + 1) (n + 2)
      (by simp) (by simp)).mp h
  let r' : ∀ n, ((ShortComplex.mk α' β' hαβ').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).Splitting := fun n ↦ by
    have : Injective (((ShortComplex.mk α' β' hαβ').map
        (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).X₁) := JA.injective n
    exact (hexact' n).splittingOfInjective
  let R : ∀ n, XB.X n ⟶ JA.cocomplex.X n := fun n ↦ by
    have : Mono (i.f n) := (hexact n).mono_f
    exact Injective.factorThru (φA.f n) (i.f n)
  let Q : ∀ n, JC.cocomplex.X n ⟶ JB.cocomplex.X n := fun n ↦ (r' n).s
  let t : ∀ n, XB.X n ⟶ JB.cocomplex.X n := fun n ↦
    R n ≫ α'.f n + p.f n ≫ φC.f n ≫ Q n
  have hti (n : ℕ) : i.f n ≫ t n = φA.f n ≫ α'.f n := by
    have : Mono (i.f n) := (hexact n).mono_f
    have hr : i.f n ≫ R n = φA.f n := Injective.comp_factorThru _ _
    have hz := HomologicalComplex.congr_hom hip n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
    dsimp only [t]
    rw [Preadditive.comp_add, ← Category.assoc, hr,
      ← Category.assoc, ← Category.assoc, hz, zero_comp, zero_comp, add_zero]
  have htβ (n : ℕ) : t n ≫ β'.f n = p.f n ≫ φC.f n := by
    have hs : Q n ≫ β'.f n = 𝟙 _ := (r' n).s_g
    have hz := HomologicalComplex.congr_hom hαβ' n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
    dsimp only [t]
    rw [Preadditive.add_comp, Category.assoc, hz, comp_zero,
      zero_add, Category.assoc, Category.assoc, hs, Category.comp_id]
  obtain ⟨E, e, hD, hw, he, hE⟩ := exact_source_defect
    S T hS hT F XA XB XC sA sB sC i p hip hi hp hexact
    JA JB JC α' β' hαβ' hα' hβ' hexact' φA φC hφA hφC t hti htβ
  obtain ⟨k, hk₀, hk⟩ := signed_primitive XC sC hex₀.1 hex JA e E he hE
  have hcomm (n : ℕ) :
      (t n - p.f n ≫ k n ≫ α'.f n) ≫ JB.cocomplex.d n (n + 1) =
        XB.d n (n + 1) ≫
          (t (n + 1) - p.f (n + 1) ≫ k (n + 1) ≫ α'.f (n + 1)) := by
    have hk' : k n ≫ JA.cocomplex.d n (n + 1) =
        XC.d n (n + 1) ≫ k (n + 1) + E n := by
      exact (eq_sub_iff_add_eq.mp (hk n)).symm
    rw [Preadditive.sub_comp, Category.assoc, Category.assoc, α'.comm,
      ← Category.assoc (k n), hk',
      Preadditive.add_comp _ _ _ (XC.d n (n + 1) ≫ k (n + 1)) (E n) (α'.f (n + 1)),
      Preadditive.comp_add _ _ _ (p.f n) _ _, Preadditive.comp_sub]
    simp only [Category.assoc]
    rw [reassoc_of% (p.comm n (n + 1))]
    have hd := hD n
    rw [eq_sub_iff_add_eq] at hd
    rw [← hd]
    abel
  let ψ : XB ⟶ JB.cocomplex :=
    CochainComplex.ofHom (fun n ↦ t n - p.f n ≫ k n ≫ α'.f n) hcomm
  refine ⟨ψ, ?_, ?_, ?_⟩
  · ext
    change sB.f 0 ≫ (t 0 - p.f 0 ≫ k 0 ≫ α'.f 0) = _
    have hb : sB.f 0 ≫ p.f 0 = S.g ≫ sC.f 0 := by
      simpa using HomologicalComplex.congr_hom hp 0
    rw [Preadditive.comp_sub, ← Category.assoc, ← Category.assoc, hb,
      Category.assoc (S.g)]
    simp only [Category.assoc, reassoc_of% hk₀]
    rw [hw, sub_sub_cancel]
  · ext n
    have hz := HomologicalComplex.congr_hom hip n
    change i.f n ≫ (t n - p.f n ≫ k n ≫ α'.f n) = φA.f n ≫ α'.f n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
    rw [Preadditive.comp_sub, hti, ← Category.assoc, ← Category.assoc,
      hz, zero_comp, zero_comp, sub_zero]
  · ext n
    have hz := HomologicalComplex.congr_hom hαβ' n
    change (t n - p.f n ≫ k n ≫ α'.f n) ≫ β'.f n = p.f n ≫ φC.f n
    simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f] at hz
    rw [Preadditive.sub_comp, htβ, Category.assoc, Category.assoc, hz,
      comp_zero, comp_zero, sub_zero]

end CategoryTheory.InjectiveResolution
