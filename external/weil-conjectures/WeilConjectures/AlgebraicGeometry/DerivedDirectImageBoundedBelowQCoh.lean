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
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentExtensionExtension
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Bounded-below direct image and quasi-coherence

Source: Stacks Project, perfect.tex, Tag 08D5, bounded-below paragraph
(blueprint: lem-pc-derived-direct-image-bounded-below-qcoh).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- The zero sheaf is quasi-coherent, using the free sheaf on no generators. -/
private theorem qcoh_containsZero (Y : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)).ContainsZero := by
  have hzero : Limits.IsZero
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  exact ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free
    (R := moduleRings Y.toRingedSpace) PEmpty.{u + 1}⟩⟩

/-- Kernel and Limits.cokernel closure propagate quasi-coherence to every derived page. -/
private theorem qcoh_pages {Y : Scheme.{u}}
    (S : BigradedExactCouple (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0)
    (hS : ∀ p q : ℤ, (S.E p q).IsQuasicoherent) :
    ∀ (r : ℕ) (p q : ℤ), (S.page r p q).IsQuasicoherent := by
  suffices h : ∀ (r : ℕ) (p q : ℤ), ((S.pageCouple r).E p q).IsQuasicoherent by
    intro r p q
    exact h (r - 2) p q
  intro r
  induction r with
  | zero => exact hS
  | succ r ih =>
    intro p q
    have : ((S.pageCouple r).E p q).IsQuasicoherent := ih p q
    have : ((S.pageCouple r).E (p + 2 + r) (q - 1 - r)).IsQuasicoherent :=
      ih _ _
    have : ((S.pageCouple r).E (p - r - 2) (q + r + 1)).IsQuasicoherent :=
      ih _ _
    have := Scheme.Modules.isQuasicoherent_kernel ((S.pageCouple r).d p q)
    exact (Scheme.Modules.quasiCoherent_cokernel_image
      (Limits.kernel.lift ((S.pageCouple r).d p q) ((S.pageCouple r).dInto p q)
        ((S.pageCouple r).dInto_comp_d p q))).2.2.2.2.2.2.1

/-- An isomorphism-invariant extension-closed property passes from finite graded pieces
to the filtered object, by descending induction from the zero step. -/
private theorem property_of_filtration {C : Type*} [Category* C] [Abelian C]
    (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (hext : ∀ (S : ShortComplex C), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    {M : C} (F : PBCDecreasingFiltration M) (N : ℕ)
    (hfull : F.step 0 = ⊤) (hzero : F.step N = ⊥)
    (hgraded : ∀ p : ℤ, P (F.gradedPiece p)) : P M := by
  have hstep : ∀ k : ℕ, P (F.step ((N : ℤ) - k) : C) := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.cast_zero, sub_zero, hzero]
      exact P.prop_of_isZero ((Limits.isZero_zero _).of_iso Subobject.botCoeIsoZero)
    | succ k ih =>
      let i : ℤ := (N : ℤ) - (k + 1)
      have hi : i + 1 = (N : ℤ) - k := by dsimp [i]; omega
      have hnext : P (F.step (i + 1) : C) := by rw [hi]; exact ih
      let φ := Subobject.ofLE (F.step (i + 1)) (F.step i)
        (F.antitone_step (by omega))
      exact hext (ShortComplex.mk φ (Limits.cokernel.π φ) (Limits.cokernel.condition φ))
        ⟨ShortComplex.exact_cokernel φ⟩ hnext (hgraded i)
  have htop := hstep N
  simp only [sub_self, hfull] at htop
  exact P.prop_of_iso (asIso (⊤ : Subobject M).arrow) htop

/-- Derived direct image of a bounded-below object with quasi-coherent cohomology
has quasi-coherent cohomology. No compactness of the target is required.
Source: Stacks Project, perfect.tex, Tag 08D5, bounded-below paragraph
(blueprint: lem-pc-derived-direct-image-bounded-below-qcoh).

Proof:
1. Represent E by a strictly bounded-below complex, using the standard t-structure.
   Apply exists_truncationHypercohomology to the module direct-image functor.
   Its right derived functor is definitionally schemeDerivedDirectImage.
   The E2 comparisons identify the terms with R^p f_* H^j(E).
2. The qcqs higher-direct-image theorem (Tag 01XJ, lem-pc-finite-support-hi)
   makes these terms quasi-coherent. Negative p and j < a terms vanish.
3. Each later page is a Limits.kernel modulo an image. The quasi-coherent Limits.kernel and
   Limits.cokernel/image lemmas imply, by induction on the page, quasi-coherence of
   every page term. In total degree q only 0 <= p <= q-a occurs, and each
   term stabilizes at a finite page by the half-plane bounds.
4. The convergence theorem supplies a finite filtration of H^q(Rf_*E), with
   those stable terms as graded pieces. Start from its zero last step and use
   isQuasicoherent_of_shortExact successively to deduce quasi-coherence of all
   filtration steps, ending at H^q(Rf_*E). This applies to every integer q.
-/
theorem schemeDerivedDirectImage_preserves_QCoh_of_isGE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (a : ℤ) [E.IsGE a] :
    schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E) := by
  classical
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
  let P := SheafOfModules.isQuasicoherent (moduleRings Y.toRingedSpace)
  have : P.ContainsZero := qcoh_containsZero Y
  have : Limits.PreservesFiniteLimits F := by
    change Limits.PreservesFiniteLimits (Scheme.Modules.pushforward f)
    infer_instance
  have : IsGrothendieckAbelian.{u} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE E a
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
            (DerivedCategory.homologyFunctorFactors A q).app K) (hE q)
      have hRq : ((F.rightDerived p.toNat).obj (Kplus.obj.homology q)).IsQuasicoherent :=
        Scheme.Modules.isQuasicoherent_higherDirectImage f (Kplus.obj.homology q) p.toNat
      have hEq : (S.E (p.toNat : ℤ) q).IsQuasicoherent :=
        P.prop_of_iso eK.symm hRq
      simpa only [Int.toNat_of_nonneg (by omega : 0 ≤ p)] using hEq
  have hpages := qcoh_pages S hsecondQC
  obtain ⟨_, _, H, hH, _, _, _, FH, _, _, _, _, _, _, _, _, _, _, hFHfull, hFHzero, _,
    hnegative, hpositive, _⟩ := hconv
  have hHQC : ∀ n : ℤ, (H n).IsQuasicoherent := by
    intro n
    apply property_of_filtration P
      (fun T hT h₁ h₃ ↦ by
        have : T.X₁.IsQuasicoherent := h₁
        have : T.X₃.IsQuasicoherent := h₃
        exact Scheme.Modules.isQuasicoherent_of_shortExact (S := T) hT)
      (FH n) (max 0 (n - a + 1)).toNat (hFHfull n 0 (by omega))
    · apply hFHzero
      omega
    · intro p
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
  intro n
  have hQ : ((DerivedCategory.homologyFunctor B n).obj
      (F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K))).IsQuasicoherent := by
    simpa only [hH] using hHQC n
  exact P.prop_of_iso
    ((DerivedCategory.homologyFunctor B n).mapIso
      ((schemeDerivedDirectImage f).mapIso e)).symm hQ

end AlgebraicGeometry
