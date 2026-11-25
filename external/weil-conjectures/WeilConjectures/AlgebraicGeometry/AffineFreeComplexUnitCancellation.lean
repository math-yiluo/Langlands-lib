/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Algebra.Homology.UnitEntrySplits
import WeilConjectures.Algebra.Homology.SplitIdentityHomotopyEquiv
import WeilConjectures.AlgebraicGeometry.AffineFreeComplexModuleLift

/-! # Cancelling a unit coefficient in an affine free cochain complex

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`).
(blueprint: lem-pc-affine-free-complex-unit-cancellation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

private abbrev reverseComplex {V : Type*} [Category V] [Preadditive V]
    (C : ChainComplex V ℤ) : CochainComplex V ℤ where
  X j := C.X (-j)
  d j k := C.d (-j) (-k)
  shape j k h := C.shape _ _ (by
    intro h'
    apply h
    change j + 1 = k
    change -k + 1 = -j at h'
    omega)

private def reverseMap {V : Type*} [Category V] [Preadditive V]
    {C D : ChainComplex V ℤ} (f : C ⟶ D) : reverseComplex C ⟶ reverseComplex D where
  f j := f.f (-j)
  comm' j k _ := f.comm (-j) (-k)

private def reverseHomotopy {V : Type*} [Category V] [Preadditive V]
    {C D : ChainComplex V ℤ} {f g : C ⟶ D} (h : Homotopy f g) :
    Homotopy (reverseMap f) (reverseMap g) where
  hom j k := h.hom (-j) (-k)
  zero j k hjk := h.zero _ _ (by
    intro h'
    apply hjk
    change k + 1 = j
    change -j + 1 = -k at h'
    omega)
  comm j := by
    have hh := h.comm (-j)
    rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel (-j) (-j - 1) by
      change -j - 1 + 1 = -j; omega),
      prevD_eq _ (show (ComplexShape.down ℤ).Rel (-j + 1) (-j) from rfl)] at hh
    rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel j (j + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℤ).Rel (j - 1) j by
        change j - 1 + 1 = j; omega)]
    change f.f (-j) = C.d (-j) (-(j + 1)) ≫ h.hom (-(j + 1)) (-j) +
      h.hom (-j) (-(j - 1)) ≫ D.d (-(j - 1)) (-j) + g.f (-j)
    have h₁ : -(j + 1) = -j - 1 := by omega
    have h₂ : -(j - 1) = -j + 1 := by omega
    rw [h₁, h₂]
    exact hh

private def reverseHomotopyEquiv {V : Type*} [Category V] [Preadditive V]
    {C D : ChainComplex V ℤ} (h : HomotopyEquiv C D) :
    HomotopyEquiv (reverseComplex C) (reverseComplex D) where
  hom := reverseMap h.hom
  inv := reverseMap h.inv
  homotopyHomInvId := reverseHomotopy h.homotopyHomInvId
  homotopyInvHomId := reverseHomotopy h.homotopyInvHomId

/-- A unit coefficient removes a contractible summand, with explicit complementary sizes.

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`).
(blueprint: lem-pc-affine-free-complex-unit-cancellation)

Proof: Identify each free sheaf with tilde of the free module on its indicated finite
basis, using tildeFinsupp. Full faithfulness of tilde lifts the conjugated differentials
and their square-zero equations to a module complex. The global-sections isomorphism
identifies the displayed coefficient with its module coefficient and preserves units.
Reverse degree j to -j, reindex the ULift bases by Fin, and apply
ChainComplex.exists_splitting_of_isUnit_entry at -i. Its complement has sizes n(i)-1
and n(i+1)-1 at the two changed degrees, and the original sizes elsewhere. In the
identity summand the reverse differential is the contracting homotopy: it is the
inverse differential between the two nonzero terms, and zero elsewhere. The complex
relations make its homotopy identity hold in all degrees. Projection to the complement
and inclusion back are inverse up to this contraction. Apply the additive tilde functor
to these maps and the homotopy, and reverse the grading back. In unchanged degrees
the identity summand is zero, so the termwise splitting gives P'.X j ≅ P.X j.
This argument needs neither a local ring nor a residue differential nor support bounds. -/
theorem exists_affine_free_complex_unit_cancellation (R : CommRingCat.{u})
    (P : CochainComplex (Spec R).Modules ℤ) (n : ℤ → ℕ)
    (e : ∀ j : ℤ, P.X j ≅ SheafOfModules.free
      (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin (n j))))
    (i : ℤ) (p : ULift.{u} (Fin (n i))) (q : ULift.{u} (Fin (n (i + 1))))
    (hunit : IsUnit (freeMatrix ((e i).inv ≫ P.d i (i + 1) ≫ (e (i + 1)).hom) q p)) :
    ∃ P' : CochainComplex (Spec R).Modules ℤ,
      Nonempty (HomotopyEquiv P P') ∧
      (∀ j : ℤ, Nonempty (P'.X j ≅ SheafOfModules.free
        (R := (Spec R).ringCatSheaf)
        (ULift.{u} (Fin (if j = i ∨ j = i + 1 then n j - 1 else n j))))) ∧
      (∀ j : ℤ, j ≠ i → j ≠ i + 1 → Nonempty (P'.X j ≅ P.X j)) := by
  classical
  obtain ⟨C, m, b, p', q', hm, hu, φ, hφ⟩ :=
    exists_affine_free_complex_module_lift R P n e i p q hunit
  obtain ⟨C', T, m', hb, hi, hi₁, haway, hT, a, a₁, ha, ψ, hψ⟩ :=
    ChainComplex.exists_splitting_of_isUnit_entry C m b (-i) p' q' hu
  obtain ⟨hCC'⟩ :=
    ChainComplex.nonempty_homotopyEquiv_of_split_identity C C' T (-i) hT a a₁ ha ψ hψ
  let F := tilde.functor R
  let Q := reverseComplex ((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj C)
  let Q' := reverseComplex ((F.mapHomologicalComplex (ComplexShape.down ℤ)).obj C')
  let η : Q ≅ P := HomologicalComplex.Hom.isoOfComponents φ hφ
  have hrank : ∀ j : ℤ, m' (-j) =
      if j = i ∨ j = i + 1 then n j - 1 else n j := by
    intro j
    by_cases hj : j = i
    · subst j
      rw [ite_eq_left (Or.inl rfl)]
      have hh := hm i
      omega
    · by_cases hj₁ : j = i + 1
      · subst j
        rw [ite_eq_left (Or.inr rfl)]
        have hh := hm (i + 1)
        have heq : -(i + 1) = -i - 1 := by omega
        rw [heq] at hh ⊢
        omega
      · rw [ite_eq_right (not_or.mpr ⟨hj, hj₁⟩)]
        rw [haway (-j) (by omega) (by omega), hm j]
  have efree : ∀ j : ℤ, Nonempty (Q'.X j ≅ SheafOfModules.free
      (R := (Spec R).ringCatSheaf)
      (ULift.{u} (Fin (if j = i ∨ j = i + 1 then n j - 1 else n j)))) := by
    intro j
    obtain ⟨bj⟩ := hb (-j)
    let bj' := bj.reindex (Equiv.ulift.symm)
    let ej := F.mapIso bj'.repr.toModuleIso ≪≫ tildeFinsupp (ULift.{u} (Fin (m' (-j))))
    exact ⟨ej ≪≫ eqToIso (by rw [hrank j])⟩
  refine ⟨Q', ⟨(HomotopyEquiv.ofIso η.symm).trans
    (reverseHomotopyEquiv (F.mapHomotopyEquiv hCC'))⟩, efree, ?_⟩
  intro j hj hj₁
  obtain ⟨ej⟩ := efree j
  have hn : (if j = i ∨ j = i + 1 then n j - 1 else n j) = n j :=
    ite_eq_right (not_or.mpr ⟨hj, hj₁⟩)
  exact ⟨ej ≪≫ eqToIso (by rw [hn]) ≪≫ (e j).symm⟩

end AlgebraicGeometry.Scheme.Modules
