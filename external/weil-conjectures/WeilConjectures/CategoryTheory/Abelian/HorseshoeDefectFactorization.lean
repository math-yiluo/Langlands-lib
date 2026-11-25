/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Factorization of horseshoe comparison defects

Source: the classical horseshoe naturality argument of Weibel, Theorem 2.4.6,
using Stacks Project, Tags 0136, 013R, 013P and 013T
(blueprint: lem-weil-pbc-horseshoe-defect-factorization).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.InjectiveResolution

private theorem factor_through_rows
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (hT : T.ShortExact)
    (x : S.X₂ ⟶ T.X₂) (hx : S.f ≫ x = 0) (hx' : x ≫ T.g = 0) :
    ∃ e : S.X₃ ⟶ T.X₁, S.g ≫ e ≫ T.f = x := by
  have := hS.epi_g
  have := hT.mono_f
  let y := hS.exact.desc x hx
  have hy : S.g ≫ y = x := hS.exact.g_desc _ _
  have hy' : y ≫ T.g = 0 := by
    rw [← cancel_epi S.g, ← Category.assoc, hy, hx', comp_zero]
  exact ⟨hT.exact.lift y hy', by rw [hT.exact.lift_f, hy]⟩

/-- The differential and augmentation defects factor through the outer rows.
Source: classical horseshoe naturality, Weibel Theorem 2.4.6, Step 2; the row
factorizations use the abelian-category kernel/cokernel argument of Stacks Tag 013T.
(blueprint: lem-weil-pbc-horseshoe-defect-factorization).

Proof: Put D_n = t_n d'_n - d_n t_{n+1}. The two outer squares for t and the
chain-map identities for α, β, α', β', φA and φC give α_n D_n = 0 and
D_n β'_{n+1} = 0. Descend D_n along the epic β_n, then lift through the monic
α'_{n+1}; exactness gives the unique E_n in the first equation. Distributing
compositions and using d² = 0 gives d_n D_{n+1} = -D_n d'_{n+1}.
Cancel the epic β_n and monic α'_{n+2}, using their chain-map identities,
to get the displayed signed cocycle identity.
Put w = ιB_0 t_0 - b ιB'_0. The augmentation identities and the two squares
for F give f w = 0 and w β'_0 = 0. Descend along the epic g and lift through
the monic α'_0, obtaining e with w = g e α'_0. Compute ιB_0 D_0 in two ways:
its factorization gives g ιC_0 E_0 α'_1, whereas ιB_0 d_0 = 0 and
ιB'_0 d'_0 = 0 give w d'_0 = g e dA'_0 α'_1. Cancel g and α'_1.
The resulting equality is precisely ιC_0 E_0 = e dA'_0. -/
theorem horseshoe_defect_factorization
    {C : Type u} [Category.{v} C] [Abelian C]
    (S T : ShortComplex C) (hS : S.ShortExact) (_hT : T.ShortExact) (F : S ⟶ T)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃) (JA : InjectiveResolution T.X₁)
    (JB : InjectiveResolution T.X₂) (JC : InjectiveResolution T.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (α' : JA.cocomplex ⟶ JB.cocomplex) (β' : JB.cocomplex ⟶ JC.cocomplex)
    (hαβ : α ≫ β = 0) (hαβ' : α' ≫ β' = 0)
    (hα : IA.ι ≫ α = (CochainComplex.single₀ C).map S.f ≫ IB.ι)
    (hβ : IB.ι ≫ β = (CochainComplex.single₀ C).map S.g ≫ IC.ι)
    (hα' : JA.ι ≫ α' = (CochainComplex.single₀ C).map T.f ≫ JB.ι)
    (hβ' : JB.ι ≫ β' = (CochainComplex.single₀ C).map T.g ≫ JC.ι)
    (hexact : ∀ n : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (hexact' : ∀ n : ℕ, ((ShortComplex.mk α' β' hαβ').map
      (HomologicalComplex.eval C (ComplexShape.up ℕ) n)).ShortExact)
    (φA : IA.cocomplex ⟶ JA.cocomplex) (φC : IC.cocomplex ⟶ JC.cocomplex)
    (hφA : IA.ι ≫ φA = (CochainComplex.single₀ C).map F.τ₁ ≫ JA.ι)
    (hφC : IC.ι ≫ φC = (CochainComplex.single₀ C).map F.τ₃ ≫ JC.ι)
    (t : ∀ n, IB.cocomplex.X n ⟶ JB.cocomplex.X n)
    (htα : ∀ n, α.f n ≫ t n = φA.f n ≫ α'.f n)
    (htβ : ∀ n, t n ≫ β'.f n = β.f n ≫ φC.f n) :
    ∃ (E : ∀ n, IC.cocomplex.X n ⟶ JA.cocomplex.X (n + 1))
      (e : S.X₃ ⟶ JA.cocomplex.X 0),
      (∀ n, β.f n ≫ E n ≫ α'.f (n + 1) =
        t n ≫ JB.cocomplex.d n (n + 1) - IB.cocomplex.d n (n + 1) ≫ t (n + 1)) ∧
      S.g ≫ e ≫ α'.f 0 =
        IB.ι.f 0 ≫ t 0 - ((CochainComplex.single₀ C).map F.τ₂ ≫ JB.ι).f 0 ∧
      IC.ι.f 0 ≫ E 0 = e ≫ JA.cocomplex.d 0 1 ∧
      ∀ n, IC.cocomplex.d n (n + 1) ≫ E (n + 1) =
        -(E n ≫ JA.cocomplex.d (n + 1) (n + 2)) := by
  classical
  let R (n : ℕ) : ShortComplex C := ShortComplex.mk (α.f n) (β.f n)
    (by simpa using HomologicalComplex.congr_hom hαβ n)
  let R' (n : ℕ) : ShortComplex C := ShortComplex.mk (α'.f n) (β'.f n)
    (by simpa using HomologicalComplex.congr_hom hαβ' n)
  have hr (n : ℕ) : (R n).ShortExact := hexact n
  have hr' (n : ℕ) : (R' n).ShortExact := hexact' n
  let D (n : ℕ) := t n ≫ JB.cocomplex.d n (n + 1) -
    IB.cocomplex.d n (n + 1) ≫ t (n + 1)
  have hDα (n : ℕ) : α.f n ≫ D n = 0 := by
    dsimp [D]
    rw [Preadditive.comp_sub, ← Category.assoc, htα, Category.assoc,
      α'.comm, ← Category.assoc, φA.comm, Category.assoc,
      ← Category.assoc (α.f n), α.comm, Category.assoc, htα, sub_self]
  have hDβ (n : ℕ) : D n ≫ β'.f (n + 1) = 0 := by
    dsimp [D]
    rw [Preadditive.sub_comp, Category.assoc, ← β'.comm,
      ← Category.assoc, htβ, Category.assoc, φC.comm,
      ← Category.assoc, β.comm]
    simp only [Category.assoc, htβ, sub_self]
  have hfac (n : ℕ) := factor_through_rows (R n) (R' (n + 1))
    (hr n) (hr' (n + 1)) (D n) (hDα n) (hDβ n)
  choose E hEfac using hfac
  dsimp only [R, R'] at hEfac
  have hEcoc (n : ℕ) : IC.cocomplex.d n (n + 1) ≫ E (n + 1) =
      -(E n ≫ JA.cocomplex.d (n + 1) (n + 2)) := by
    have : Epi (β.f n) := (hr n).epi_g
    have : Mono (α'.f (n + 2)) := (hr' (n + 2)).mono_f
    rw [← cancel_epi (β.f n), ← cancel_mono (α'.f (n + 2))]
    simp only [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp]
    rw [reassoc_of% (β.comm n (n + 1)), ← α'.comm,
      ← Category.assoc (E n), ← Category.assoc (β.f n), hEfac]
    simp only [Category.assoc]
    rw [← Category.assoc (β.f n) (E n),
      ← Category.assoc (β.f n ≫ E n)]
    have hEfac' : (β.f n ≫ E n) ≫ α'.f (n + 1) = D n := by
      simpa only [Category.assoc] using hEfac n
    rw [hEfac']
    simp only [D, Preadditive.comp_sub, Preadditive.sub_comp, ← Category.assoc,
      HomologicalComplex.d_comp_d, zero_comp, sub_zero]
    rw [Category.assoc (t n), HomologicalComplex.d_comp_d, comp_zero, zero_sub,
      neg_neg]
  let sA : S.X₁ ⟶ IA.cocomplex.X 0 := IA.ι.f 0
  let sB : S.X₂ ⟶ IB.cocomplex.X 0 := IB.ι.f 0
  let sC : S.X₃ ⟶ IC.cocomplex.X 0 := IC.ι.f 0
  let sA' : T.X₁ ⟶ JA.cocomplex.X 0 := JA.ι.f 0
  let sB' : T.X₂ ⟶ JB.cocomplex.X 0 := JB.ι.f 0
  let sC' : T.X₃ ⟶ JC.cocomplex.X 0 := JC.ι.f 0
  have hsα : sA ≫ α.f 0 = S.f ≫ sB := by
    simpa using HomologicalComplex.congr_hom hα 0
  have hsβ : sB ≫ β.f 0 = S.g ≫ sC := by
    simpa using HomologicalComplex.congr_hom hβ 0
  have hsα' : sA' ≫ α'.f 0 = T.f ≫ sB' := by
    simpa using HomologicalComplex.congr_hom hα' 0
  have hsβ' : sB' ≫ β'.f 0 = T.g ≫ sC' := by
    simpa using HomologicalComplex.congr_hom hβ' 0
  have hsφA : sA ≫ φA.f 0 = F.τ₁ ≫ sA' := by
    simpa using HomologicalComplex.congr_hom hφA 0
  have hsφC : sC ≫ φC.f 0 = F.τ₃ ≫ sC' := by
    simpa using HomologicalComplex.congr_hom hφC 0
  let w : S.X₂ ⟶ JB.cocomplex.X 0 := sB ≫ t 0 - F.τ₂ ≫ sB'
  have hwf : S.f ≫ w = 0 := by
    dsimp [w]
    rw [Preadditive.comp_sub, ← Category.assoc, ← hsα, Category.assoc,
      htα, ← Category.assoc, hsφA, Category.assoc, hsα',
      ← Category.assoc, F.comm₁₂, Category.assoc, sub_self]
  have hwβ : w ≫ β'.f 0 = 0 := by
    dsimp [w]
    rw [Preadditive.sub_comp, Category.assoc, htβ,
      ← Category.assoc, hsβ, Category.assoc, hsφC,
      Category.assoc, hsβ', ← Category.assoc, ← F.comm₂₃, Category.assoc, sub_self]
  obtain ⟨e, hef⟩ := factor_through_rows S (R' 0) hS (hr' 0) w hwf hwβ
  have heaug : sC ≫ E 0 = e ≫ JA.cocomplex.d 0 1 := by
    have := hS.epi_g
    have : Mono (α'.f 1) := (hr' 1).mono_f
    rw [← cancel_epi S.g, ← cancel_mono (α'.f 1)]
    simp only [Category.assoc]
    rw [← reassoc_of% hsβ, hEfac]
    dsimp [D]
    rw [Preadditive.comp_sub]
    rw [reassoc_of% (show sB ≫ IB.cocomplex.d 0 1 = 0 from
      IB.ι_f_zero_comp_complex_d), zero_comp, sub_zero, ← α'.comm]
    dsimp only [R'] at hef
    rw [reassoc_of% hef]
    dsimp [w]
    simp only [Preadditive.sub_comp, Category.assoc,
      show sB' ≫ JB.cocomplex.d 0 1 = 0 from JB.ι_f_zero_comp_complex_d,
      comp_zero, sub_zero]
  refine ⟨E, e, hEfac, ?_, heaug, hEcoc⟩
  simpa [w, sB, sB'] using hef

end CategoryTheory.InjectiveResolution
