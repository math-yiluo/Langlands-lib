/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
import WeilConjectures.AlgebraicGeometry.DerivedTotalResolutionColumnZero
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

private theorem toCycles_naturality
    (A B : CochainComplex (ModuleCat R) ℤ) (f : A ⟶ B)
    [∀ i, A.HasHomology i] [∀ i, B.HasHomology i] (n : ℤ) :
    A.toCycles (n - 1) n ≫ HomologicalComplex.cyclesMap f n =
      f.f (n - 1) ≫ B.toCycles (n - 1) n := by
  rw [← cancel_mono (B.iCycles n)]
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.toCycles_i, HomologicalComplex.toCycles_i_assoc,
    HomologicalComplex.Hom.comm]

private theorem lift_boundary
    (A B C D : CochainComplex (ModuleCat R) ℤ)
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    [∀ i, A.HasHomology i] [∀ i, B.HasHomology i]
    [∀ i, C.HasHomology i] [∀ i, D.HasHomology i]
    (n : ℤ) (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)
    (he : Function.Exact (f.f (n - 1)).hom (g.f (n - 1)).hom)
    (hc : Function.Exact (HomologicalComplex.cyclesMap g (n - 1)).hom
      (HomologicalComplex.cyclesMap h (n - 1)).hom)
    (z : A.cycles n) (w : B.X (n - 1))
    (hw : (B.toCycles (n - 1) n).hom w =
      (HomologicalComplex.cyclesMap f n).hom z) :
    ∃ t : A.X (n - 1), (B.toCycles (n - 1) n).hom w =
      (HomologicalComplex.cyclesMap f n).hom ((A.toCycles (n - 1) n).hom t) := by
  have hfgc : HomologicalComplex.cyclesMap f n ≫
      HomologicalComplex.cyclesMap g n = 0 := by
    rw [← HomologicalComplex.cyclesMap_comp, hfg, HomologicalComplex.cyclesMap_zero]
  have hgw : (C.toCycles (n - 1) n).hom ((g.f (n - 1)).hom w) = 0 := by
    have e := congr($(toCycles_naturality B C g n) w)
    change (HomologicalComplex.cyclesMap g n).hom ((B.toCycles (n - 1) n).hom w) =
      (C.toCycles (n - 1) n).hom ((g.f (n - 1)).hom w) at e
    rw [← e, hw]
    exact congr($(hfgc) z)
  have hgw' : (C.d (n - 1) n).hom ((g.f (n - 1)).hom w) = 0 := by
    have e := congr($(C.toCycles_i (n - 1) n) ((g.f (n - 1)).hom w))
    change (C.iCycles n).hom ((C.toCycles (n - 1) n).hom
      ((g.f (n - 1)).hom w)) = _ at e
    rw [← e, hgw, map_zero]
  let c : C.cycles (n - 1) := (C.sc (n - 1)).cyclesMk
    ((g.f (n - 1)).hom w) (by
      change (C.d (n - 1) ((ComplexShape.up ℤ).next (n - 1))).hom _ = 0
      rw [CochainComplex.next, sub_add_cancel]
      exact hgw')
  have hci : (C.iCycles (n - 1)).hom c = (g.f (n - 1)).hom w := by
    exact (C.sc (n - 1)).i_cyclesMk _ _
  have hcz : (HomologicalComplex.cyclesMap h (n - 1)).hom c = 0 := by
    apply (ModuleCat.mono_iff_injective (D.iCycles (n - 1))).1 inferInstance
    have e := congr($(HomologicalComplex.cyclesMap_i h (n - 1)) c)
    change (D.iCycles (n - 1)).hom
      ((HomologicalComplex.cyclesMap h (n - 1)).hom c) =
      (h.f (n - 1)).hom ((C.iCycles (n - 1)).hom c) at e
    rw [map_zero, e, hci]
    exact congr($(congrArg (fun k : B ⟶ D ↦ k.f (n - 1)) hgh) w)
  obtain ⟨v, hv⟩ := (hc c).mp hcz
  have hgv : (g.f (n - 1)).hom ((B.iCycles (n - 1)).hom v) =
      (g.f (n - 1)).hom w := by
    have e := congr($(HomologicalComplex.cyclesMap_i g (n - 1)) v)
    change (C.iCycles (n - 1)).hom
      ((HomologicalComplex.cyclesMap g (n - 1)).hom v) =
      (g.f (n - 1)).hom ((B.iCycles (n - 1)).hom v) at e
    rw [← e, hv, hci]
  obtain ⟨t, ht⟩ := (he (w - (B.iCycles (n - 1)).hom v)).mp (by
    rw [map_sub, hgv, sub_self])
  refine ⟨t, ?_⟩
  have e := congr($(toCycles_naturality A B f n) t)
  change (HomologicalComplex.cyclesMap f n).hom ((A.toCycles (n - 1) n).hom t) =
    (B.toCycles (n - 1) n).hom ((f.f (n - 1)).hom t) at e
  rw [e, ht, map_sub]
  have hv0 : (B.toCycles (n - 1) n).hom ((B.iCycles (n - 1)).hom v) = 0 := by
    have hzero : B.iCycles (n - 1) ≫ B.toCycles (n - 1) n = 0 := by
      rw [← cancel_mono (B.iCycles n), Category.assoc,
        HomologicalComplex.toCycles_i, HomologicalComplex.iCycles_d, zero_comp]
    exact congr($(hzero) v)
  rw [hv0, sub_zero]

private theorem homology_exact_of_boundary_lifting
    (L A M : CochainComplex (ModuleCat R) ℤ) (f : L ⟶ A) (g : A ⟶ M)
    [∀ i, L.HasHomology i] [∀ i, A.HasHomology i] [∀ i, M.HasHomology i]
    (n : ℤ)
    (hc : Function.Exact (HomologicalComplex.cyclesMap f n).hom
      (HomologicalComplex.cyclesMap g n).hom)
    (hlift : ∀ (z : A.cycles n) (w : M.X (n - 1)),
      (M.toCycles (n - 1) n).hom w = (HomologicalComplex.cyclesMap g n).hom z →
      ∃ t : A.X (n - 1), (M.toCycles (n - 1) n).hom w =
        (HomologicalComplex.cyclesMap g n).hom ((A.toCycles (n - 1) n).hom t)) :
    Function.Exact (HomologicalComplex.homologyMap f n).hom
      (HomologicalComplex.homologyMap g n).hom := by
  have hcomp : HomologicalComplex.cyclesMap f n ≫
      HomologicalComplex.cyclesMap g n = 0 := by
    apply ModuleCat.hom_ext
    exact hc.linearMap_comp_eq_zero
  have hHcomp : HomologicalComplex.homologyMap f n ≫
      HomologicalComplex.homologyMap g n = 0 := by
    rw [← cancel_epi (L.homologyπ n)]
    rw [HomologicalComplex.homologyπ_naturality_assoc,
      HomologicalComplex.homologyπ_naturality, ← Category.assoc, hcomp,
      zero_comp, comp_zero]
  intro x
  constructor
  · intro hx
    obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (A.homologyπ n)).1 inferInstance x
    have hz : (M.homologyπ n).hom ((HomologicalComplex.cyclesMap g n).hom z) = 0 := by
      simpa only [← ModuleCat.hom_comp, ← LinearMap.comp_apply,
        ← HomologicalComplex.homologyπ_naturality] using hx
    let S := ShortComplex.mk (M.toCycles (n - 1) n) (M.homologyπ n)
      (M.toCycles_comp_homologyπ (n - 1) n)
    have hS : S.Exact := S.exact_of_g_is_cokernel
      (M.homologyIsCokernel (n - 1) n (by simp : (ComplexShape.up ℤ).prev n = n - 1))
    obtain ⟨w, hw⟩ := (S.moduleCat_exact_iff).mp hS
      ((HomologicalComplex.cyclesMap g n).hom z) hz
    obtain ⟨t, ht⟩ := hlift z w hw
    have hz' : (HomologicalComplex.cyclesMap g n).hom
        (z - (A.toCycles (n - 1) n).hom t) = 0 := by
      rw [map_sub, ← ht, hw, sub_self]
    obtain ⟨b, hb⟩ := (hc _).mp hz'
    refine ⟨(L.homologyπ n).hom b, ?_⟩
    have he := congr($(HomologicalComplex.homologyπ_naturality f n) b)
    change (HomologicalComplex.homologyMap f n).hom ((L.homologyπ n).hom b) =
      (A.homologyπ n).hom ((HomologicalComplex.cyclesMap f n).hom b) at he
    rw [he, hb, map_sub]
    have ht0 := congr($(A.toCycles_comp_homologyπ (n - 1) n) t)
    change (A.homologyπ n).hom ((A.toCycles (n - 1) n).hom t) = 0 at ht0
    rw [ht0, sub_zero]
  · rintro ⟨y, rfl⟩
    exact congr($(hHcomp) y)

private theorem homology_exact_of_cycles_exact
    (L A M : CochainComplex (ModuleCat R) ℤ) (f : L ⟶ A) (g : A ⟶ M)
    [∀ i, L.HasHomology i] [∀ i, A.HasHomology i] [∀ i, M.HasHomology i]
    (n : ℤ)
    (hc : Function.Exact (HomologicalComplex.cyclesMap f n).hom
      (HomologicalComplex.cyclesMap g n).hom)
    (hg : Function.Surjective (g.f (n - 1)).hom) :
    Function.Exact (HomologicalComplex.homologyMap f n).hom
      (HomologicalComplex.homologyMap g n).hom := by
  apply homology_exact_of_boundary_lifting L A M f g n hc
  intro z w _
  obtain ⟨t, ht⟩ := hg w
  refine ⟨t, ?_⟩
  have e := congr($(toCycles_naturality A M g n) t)
  change (HomologicalComplex.cyclesMap g n).hom ((A.toCycles (n - 1) n).hom t) =
    (M.toCycles (n - 1) n).hom ((g.f (n - 1)).hom t) at e
  rw [e, ht]

-- Preserve the inherited, unused negative-column augmentation hypothesis and its binder hp.
set_option linter.unusedVariables false in
/-- The total augmentation is injective on homology in every degree.
Source: Stacks Project, Homology, Tag 09IZ, proof.
(blueprint: lem-pc-derived-total-resolution-homology-injective)

Proof. A boundary-lifting diagram chase proves exactness of each horizontal
homology row from the exact term and cycle rows. Concretely, if the image
of a cycle z is d w, the next horizontal image of w is a cycle. Lift that
cycle backwards using exactness of the cycle row, subtract the lift from
w, and lift the difference backwards using exactness of the term row.
Subtract the differential of this primitive from z; exactness of the
cycle row now lifts the resulting cycle to the preceding column. At the
augmentation, surjectivity on terms lifts w directly instead.

The column-zero inclusion j is a chain map because the positive columns
vanish, and j ≫ ε = a. The finite-support reduction theorem makes H(j)
surjective, using the interior homology rows just proved. The composite
K.d (-1) 0 ≫ j is null-homotopic: its homotopy in degree q is the inclusion
of (K.X (-1)).X q into total degree q-1. The signed vertical term cancels
the differential of the source, leaving the horizontal term. Therefore
H(K.d (-1) 0) ≫ H(j) = 0. Given x in the kernel of H(ε), lift x along H(j)
to y. Then H(a)(y) = 0. Exactness at H(K.X 0) lifts y along H(K.d (-1) 0),
so x = 0 by the null-homotopy. Zero kernel gives injectivity. -/
theorem total_resolution_homology_injective
    (M : CochainComplex (ModuleCat R) ℤ)
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (ε : K.total (ComplexShape.up ℤ) ⟶ M)
    (a : K.X 0 ⟶ M)
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ i, M.HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (h_augmentation_zero : ∀ q : ℤ,
      K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ ε.f q = a.f q)
    (h_augmentation : ∀ (p q n : ℤ) (hp : p < 0)
      (h : ComplexShape.π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      K.ιTotal (ComplexShape.up ℤ) p q n h ≫ ε.f n = 0)
    (h_exact : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        ((K.d p (p + 1)).f q).hom
        ((K.d (p + 1) (p + 2)).f q).hom)
    (h_exact_zero : ∀ q : ℤ, Function.Exact
      ((K.d (-1) 0).f q).hom (a.f q).hom)
    (h_surjective : ∀ q : ℤ, Function.Surjective
      (a.f q).hom)
    (h_cycles : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.cyclesMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.cyclesMap (K.d (p + 1) (p + 2)) q).hom)
    (h_cycles_zero : ∀ q : ℤ, Function.Exact
      (HomologicalComplex.cyclesMap (K.d (-1) 0) q).hom
      (HomologicalComplex.cyclesMap a q).hom)
    (h_cycles_surjective : ∀ q : ℤ, Function.Surjective
      (HomologicalComplex.cyclesMap a q).hom) :
    Function.Injective (HomologicalComplex.homologyMap ε n).hom := by
  classical
  have hd (q : ℤ) : (K.d 0 1).f q = 0 := by
    exact ((HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) q).map_isZero
      (h_positive 1 (by omega))).eq_of_tgt _ _
  let j : K.X 0 ⟶ K.total (ComplexShape.up ℤ) :=
    { f := fun q ↦ K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp)
      comm' := by
        intro q q' h
        dsimp [ComplexShape.up] at h
        subst q'
        rw [HomologicalComplex₂.total_d, Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
          K.d₁_eq' (ComplexShape.up ℤ) (by simp : (ComplexShape.up ℤ).Rel 0 1),
          K.d₂_eq (ComplexShape.up ℤ) 0
            (by simp : (ComplexShape.up ℤ).Rel q (q + 1)) _ (by simp), hd]
        simp [ComplexShape.ε₁, ComplexShape.ε₂] }
  have hja : j ≫ ε = a := by
    apply HomologicalComplex.Hom.ext
    funext q
    exact h_augmentation_zero q
  let s : Homotopy (K.d (-1) 0 ≫ j) 0 :=
    { hom := fun q q' ↦ K.ιTotalOrZero (ComplexShape.up ℤ) (-1) q q'
      zero := by
        intro q q' h
        apply K.ιTotalOrZero_eq_zero
        intro he
        apply h
        have he' : -1 + q = q' := by simpa using he
        change q' + 1 = q
        omega
      comm := by
        intro q
        simp only [dNext, prevD, AddMonoidHom.mk'_apply]
        rw [CochainComplex.next ℤ q, CochainComplex.prev ℤ q]
        change (K.d (-1) 0).f q ≫ j.f q =
          (K.X (-1)).d q (q + 1) ≫
            K.ιTotalOrZero (ComplexShape.up ℤ) (-1) (q + 1) q +
          K.ιTotalOrZero (ComplexShape.up ℤ) (-1) q (q - 1) ≫
            (K.total (ComplexShape.up ℤ)).d (q - 1) q + 0
        rw [K.ιTotalOrZero_eq (ComplexShape.up ℤ) (-1) q (q - 1) (by simp; omega)]
        rw [HomologicalComplex₂.total_d, Preadditive.comp_add, K.ι_D₁, K.ι_D₂,
          K.d₁_eq (ComplexShape.up ℤ)
            (by simp : (ComplexShape.up ℤ).Rel (-1) 0) _ _ (by simp),
          K.d₂_eq (ComplexShape.up ℤ) (-1)
            (by simp : (ComplexShape.up ℤ).Rel q (q + 1)) _ (by simp)]
        simp [j, ComplexShape.ε₁, ComplexShape.ε₂,
          K.ιTotalOrZero_eq (ComplexShape.up ℤ) (-1) (q + 1) q (by simp)] }
  have hzero : HomologicalComplex.homologyMap (K.d (-1) 0) n ≫
      HomologicalComplex.homologyMap j n = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, s.homologyMap_eq n,
      HomologicalComplex.homologyMap_zero]
  have hrow : Function.Exact (HomologicalComplex.homologyMap (K.d (-1) 0) n).hom
      (HomologicalComplex.homologyMap a n).hom :=
    homology_exact_of_cycles_exact (K.X (-1)) (K.X 0) M (K.d (-1) 0) a n
      (h_cycles_zero n) (h_surjective (n - 1))
  have hda : K.d (-1) 0 ≫ a = 0 := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    exact (h_exact_zero q).linearMap_comp_eq_zero
  have hH : ∀ (p q : ℤ), p < -1 → Function.Exact
      (HomologicalComplex.homologyMap (K.d p (p + 1)) q).hom
      (HomologicalComplex.homologyMap (K.d (p + 1) (p + 2)) q).hom := by
    intro p q hp
    apply homology_exact_of_boundary_lifting (K.X p) (K.X (p + 1)) (K.X (p + 2))
      (K.d p (p + 1)) (K.d (p + 1) (p + 2)) q (h_cycles p q hp)
    intro z w hw
    by_cases hp2 : p = -2
    · subst p
      have hc : Function.Exact (HomologicalComplex.cyclesMap a (q - 1)).hom
          (HomologicalComplex.cyclesMap (0 : M ⟶ M) (q - 1)).hom := by
        intro x
        rw [HomologicalComplex.cyclesMap_zero]
        constructor
        · intro _
          exact h_cycles_surjective (q - 1) x
        · intro _
          rfl
      exact lift_boundary (K.X (-1)) (K.X 0) M M (K.d (-1) 0) a 0 q hda
        (by simp) (h_exact_zero (q - 1)) hc z w hw
    · by_cases hp3 : p = -3
      · subst p
        exact lift_boundary (K.X (-2)) (K.X (-1)) (K.X 0) M
          (K.d (-2) (-1)) (K.d (-1) 0) a q (K.d_comp_d _ _ _) hda
          (by simpa using h_exact (-2) (q - 1) (by omega))
          (h_cycles_zero (q - 1)) z w hw
      · exact lift_boundary (K.X (p + 1)) (K.X (p + 2)) (K.X (p + 3))
          (K.X (p + 4)) (K.d (p + 1) (p + 2)) (K.d (p + 2) (p + 3))
          (K.d (p + 3) (p + 4)) q (K.d_comp_d _ _ _) (K.d_comp_d _ _ _)
          (by
            have he := h_exact (p + 1) (q - 1) (by omega)
            rw [show p + 1 + 1 = p + 2 by omega, show p + 1 + 2 = p + 3 by omega] at he
            exact he)
          (by
            have hc := h_cycles (p + 2) (q - 1) (by omega)
            rw [show p + 2 + 1 = p + 3 by omega, show p + 2 + 2 = p + 4 by omega] at hc
            exact hc)
          z w hw
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap j n).hom :=
    total_resolution_column_zero_surjective K j n h_positive (fun _ ↦ rfl) hH
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : (HomologicalComplex.homologyMap a n).hom y = 0 := by
    rw [← hja, HomologicalComplex.homologyMap_comp]
    exact hx
  obtain ⟨z, hz⟩ := (hrow y).mp hy
  rw [← hz]
  exact congr($(hzero) z)

end WeilConjectures.DerivedTotalResolution
