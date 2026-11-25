/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

import WeilConjectures.CategoryTheory.PBCFiltration

public import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension


public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentExtensionExtension
import WeilConjectures.AlgebraicGeometry.OrdinaryHigherImageQuasiCoherent
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-! # Quasi-coherence of a truncated higher image

Source: Stacks Project, Tag 08D5, bounded-below paragraph, and Tag 015J.
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Kernel and cokernel closure propagate any object property to every derived page. -/
private theorem property_pages {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C)
    (hk : ∀ {M N : C} (φ : M ⟶ N), P M → P N → P (Limits.kernel φ))
    (hc : ∀ {M N : C} (φ : M ⟶ N), P M → P N → P (Limits.cokernel φ))
    (S : BigradedExactCouple C 0) (hS : ∀ p q : ℤ, P (S.E p q)) :
    ∀ (r : ℕ) (p q : ℤ), P (S.page r p q) := by
  suffices h : ∀ (r : ℕ) (p q : ℤ), P ((S.pageCouple r).E p q) by
    intro r p q
    exact h (r - 2) p q
  intro r
  induction r with
  | zero => exact hS
  | succ r ih =>
    intro p q
    exact hc
      (Limits.kernel.lift ((S.pageCouple r).d p q) ((S.pageCouple r).dInto p q)
        ((S.pageCouple r).dInto_comp_d p q))
      (ih _ _)
      (hk ((S.pageCouple r).d p q) (ih _ _) (ih _ _))

/-- An isomorphism-invariant extension-closed property passes from finite graded pieces
to the filtered object on any finite index interval, by descending induction. -/
private theorem property_of_shifted_filtration {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hext : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {M : C} (F : PBCDecreasingFiltration M) (b : ℤ) (N : ℕ)
    (hfull : F.step b = ⊤) (hzero : F.step (b + N) = ⊥)
    (hgraded : ∀ p : ℤ, b ≤ p → p < b + N → P (F.gradedPiece p)) : P M := by
  have hstep : ∀ k : ℕ, k ≤ N → P (F.step (b + (N : ℤ) - k) : C) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp only [Nat.cast_zero, sub_zero, hzero]
      exact P.prop_of_isZero ((Limits.isZero_zero _).of_iso Subobject.botCoeIsoZero)
    | succ k ih =>
      intro hk
      let i : ℤ := b + (N : ℤ) - (k + 1)
      have hi : i + 1 = b + (N : ℤ) - k := by dsimp [i]; omega
      have hnext : P (F.step (i + 1) : C) := by rw [hi]; exact ih (by omega)
      let φ := Subobject.ofLE (F.step (i + 1)) (F.step i)
        (F.antitone_step (by omega))
      exact hext (ShortComplex.mk φ (Limits.cokernel.π φ) (Limits.cokernel.condition φ))
        ⟨ShortComplex.exact_cokernel φ⟩ hnext (hgraded i (by dsimp [i]; omega)
          (by dsimp [i]; omega))
  have htop := hstep N (by rfl)
  simp only [add_sub_cancel_right, hfull] at htop
  exact P.prop_of_iso (asIso (⊤ : Subobject M).arrow) htop

/-- Each higher image of a canonical lower truncation is quasi-coherent.
Source: Stacks Project, Tag 08D5, proof of part (1), bounded-below paragraph;
Tag 015J supplies the bounded-below hypercohomology spectral sequence, and
Tag 01XJ, part (1), supplies quasi-coherence of ordinary higher direct images.
(blueprint: lem-pc-truncated-higher-image-quasi-coherent).

Proof.
1. Put K = tau_{>= a} E. Its cohomology agrees with that of E in degrees at
   least a and is zero in lower degrees. Thus all its cohomology sheaves are
   quasi-coherent, including the zero sheaf, and K is bounded below by a.
2. Use bounded-below truncation hypercohomology for module direct image. Its
   second page in bidegree (p,r), for p >= 0, is R^p f_* H^r(K). These sheaves
   are quasi-coherent by Tag 01XJ (1); the terms for p < 0 or r < a are zero.
   To obtain Tag 01XJ (1) locally, restrict to an affine target open, whose
   preimage is qcqs. Affine acyclicity and localization of cohomology on
   principal opens identify higher-image sections with localized modules on
   an affine source. Mayer--Vietoris induction on a finite affine cover,
   with quasi-compact overlaps, propagates this localization comparison.
   The higher-image presheaf description gives quasi-coherent second pages.
3. Each subsequent page is a kernel modulo an image. Closure of quasi-coherent
   modules under kernels, images and cokernels proves their quasi-coherence
   by induction on the page. In total degree q, the quadrant bounds give a
   finite convergent filtration of H^q(Rf_* K), and its graded pieces are
   stable page terms, hence quasi-coherent. Starting with its zero last step,
   extension closure proves quasi-coherence of each preceding filtration
   step and finally of the whole abutment. This also covers q < a, when the
   abutment is zero, and an empty scheme, where every module sheaf is zero.
-/
theorem truncated_higherImage_isQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedQCohCategory X) (a q : ℤ) :
    ((schemeHigherDirectImage f q).obj
      ((DerivedCategory.TStructure.t.truncGE a).obj E.obj)).IsQuasicoherent := by
  have : (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).ContainsZero := by
    have hzero : Limits.IsZero
        (SheafOfModules.free (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}) := by
      apply (Limits.IsZero.iff_id_eq_zero _).mpr
      apply (SheafOfModules.freeHomEquiv _).injective
      funext i
      exact PEmpty.elim i
    exact ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free
      (R := moduleRings X.toRingedSpace) PEmpty.{u + 1}⟩⟩
  let T := (DerivedCategory.TStructure.t.truncGE a).obj E.obj
  have hT : schemeDerivedQCohProperty X T :=
    DerivedCategory.homologyProperty_truncGE E.property a
  classical
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let P := SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)
  have : P.ContainsZero := by
    have hzero : Limits.IsZero
        (SheafOfModules.free (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}) := by
      apply (Limits.IsZero.iff_id_eq_zero _).mpr
      apply (SheafOfModules.freeHomEquiv _).injective
      funext i
      exact PEmpty.elim i
    exact ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free
      (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}⟩⟩
  have : Limits.PreservesFiniteLimits F := by
    change Limits.PreservesFiniteLimits (Scheme.Modules.pushforward f)
    infer_instance
  have : IsGrothendieckAbelian.{u} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE T a
  let Kplus : CochainComplex.Plus A := ⟨K, a, hK⟩
  have ha : ∀ q : ℤ, q < a → Limits.IsZero (Kplus.obj.homology q) := by
    intro q hq
    exact (K.exactAt_of_isGE a q hq).isZero_homology
  obtain ⟨S, _, _, _, _, _, hsecond, hneg, _, _, _, _, _, _, _, _, _, hconv⟩ :=
    exists_truncationHypercohomology F Kplus a ha
  have hsecondQC : ∀ p q : ℤ, (S.E p q).IsQuasicoherent := by
    intro p q
    by_cases hp : p < 0
    · exact P.prop_of_isZero (hneg p q hp)
    · obtain ⟨_, _, eK, _⟩ := hsecond p.toNat q
      have hKq : (Kplus.obj.homology q).IsQuasicoherent :=
        (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
          ((DerivedCategory.homologyFunctor A q).mapIso e ≪≫
            (DerivedCategory.homologyFunctorFactors A q).app K) (hT q)
      have hRq : ((F.rightDerived p.toNat).obj (Kplus.obj.homology q)).IsQuasicoherent :=
        ordinaryHigherImage_isQuasicoherent f (Kplus.obj.homology q) hKq p.toNat
      have hEq : (S.E (p.toNat : ℤ) q).IsQuasicoherent :=
        P.prop_of_iso eK.symm hRq
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ p)] using hEq
  have hpages := property_pages P
    (fun {M N} φ hM hN ↦ by
      have : M.IsQuasicoherent := hM
      have : N.IsQuasicoherent := hN
      exact Scheme.Modules.isQuasicoherent_kernel φ)
    (fun {M N} φ hM hN ↦ by
      have : M.IsQuasicoherent := hM
      have : N.IsQuasicoherent := hN
      exact (Scheme.Modules.quasiCoherent_cokernel_image φ).2.2.2.2.2.2.1)
    S hsecondQC
  obtain ⟨_, _, H, hH, _, _, _, FH, _, _, _, _, _, _, _, _, _, _, hFHfull, hFHzero, _,
    hnegative, hpositive, _⟩ := hconv
  have hHQC : ∀ n : ℤ, (H n).IsQuasicoherent := by
    intro n
    apply property_of_shifted_filtration P
      (fun T hT h₁ h₃ ↦ by
        have : T.X₁.IsQuasicoherent := h₁
        have : T.X₃.IsQuasicoherent := h₃
        exact Scheme.Modules.isQuasicoherent_of_shortExact (S := T) hT)
      (FH n) 0 (max 0 (n - a + 1)).toNat (hFHfull n 0 (by omega))
    · apply hFHzero
      omega
    · intro p _ _
      by_cases hp : p < 0
      · have hz := (hnegative p (n - p) hp).1
        have heq : p + (n - p) = n := by omega
        rw [heq] at hz
        exact P.prop_of_isZero hz
      · obtain ⟨_, _, psi, grc, _, _, _, _, _⟩ :=
          hpositive p (n - p) (by omega)
        have hqc := hpages (max (p + 3) (n - p - a + 2)).toNat p (n - p)
        have hqc' : P ((FH (p + (n - p))).gradedPiece p) :=
          P.prop_of_iso (grc.symm ≪≫ psi).symm hqc
        have heq : p + (n - p) = n := by omega
        rw [heq] at hqc'
        exact hqc'
  have hQ : ((DerivedCategory.homologyFunctor B q).obj
      (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K))).IsQuasicoherent := by
    simpa only [hH] using hHQC q
  exact P.prop_of_iso
    ((DerivedCategory.homologyFunctor B q).mapIso
      ((schemeDerivedDirectImage f).mapIso e)).symm hQ

end AlgebraicGeometry
