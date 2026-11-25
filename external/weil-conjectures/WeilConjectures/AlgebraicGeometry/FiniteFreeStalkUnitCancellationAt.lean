/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.AffineFreeComplexUnitCancellation

/-! # Unit cancellation at a specified degree

Source: Stacks Project, Tag 00MT, and blueprint lemma-coherent-base-change-invertible-sheaves--3,
proof step 4. (blueprint: lem-pc-finite-free-stalk-unit-cancellation-at)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private lemma unit_hom_eq_zero_of_top {X : Scheme.{u}}
    (f : Modules.unit X ⟶ Modules.unit X)
    (h : Hom.app f ⊤ (1 : Γ(X, ⊤)) = 0) : f = 0 := by
  apply Modules.hom_ext
  intro U
  ext a
  have hU : Hom.app f U (1 : Γ(X, U)) = 0 := by
    have hn := f.mapPresheaf.naturality (homOfLE (show U ≤ ⊤ from le_top)).op
    have hh := congrArg (fun g ↦ g (1 : Γ(X, ⊤))) hn
    change Hom.app f U (X.presheaf.map _ (1 : Γ(X, ⊤))) =
      X.presheaf.map _ (Hom.app f ⊤ (1 : Γ(X, ⊤))) at hh
    simpa only [map_one, h, map_zero] using hh
  have ha := Hom.app_smul f (U := U) a (1 : Γ(X, U))
  simpa [hU] using ha

set_option backward.isDefEq.respectTransparency false in
private lemma freeMatrix_ne_zero {X : Scheme.{u}} {I J : Type u}
    [Finite J] [DecidableEq J]
    (f : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free J)
    (hf : f ≠ 0) : freeMatrix f ≠ 0 := by
  classical
  let _ := Fintype.ofFinite J
  intro h
  apply hf
  apply free_hom_ext
  intro i
  have he : SheafOfModules.ιFree i ≫ f =
      ∑ j : J, (SheafOfModules.ιFree i ≫ f ≫ freeπ j) ≫ SheafOfModules.ιFree j := by
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum, ← Preadditive.comp_sum, sum_freeπ_ιFree]
    simp
  rw [he]
  have hz : ∀ j : J, SheafOfModules.ιFree i ≫ f ≫ freeπ j = 0 := by
    intro j
    apply unit_hom_eq_zero_of_top
    exact congrFun (congrFun h j) i
  simp [hz]

set_option backward.isDefEq.respectTransparency false in
/-- Cancel the specified nonzero residue differential, retaining every rank equation.

Source: Stacks Project, Tag 00MT (`lemma-add-trivial-complex`), applied once;
blueprint lemma-coherent-base-change-invertible-sheaves--3, proof step 4.
(blueprint: lem-pc-finite-free-stalk-unit-cancellation-at)

Proof: Choose the given free-sheaf identifications. On the affine scheme Spec of
O_{Y,y}, free sheaves are the associated sheaves of their finite free modules.
Read the differential in degree i as a matrix over O_{Y,y}. The pullback free
identifications reduce its coefficients modulo the maximal ideal. The given
nonzero residue differential therefore has a nonzero matrix coefficient, whose
lift is a unit in the local ring. Reverse grading and apply
ChainComplex.exists_splitting_of_isUnit_entry to that entry. The complement
has one fewer basis vector in degrees i and i+1 and the original bases in all
other degrees. The other summand is the identity two-term complex, contracted
by the inverse of its differential in the reverse direction, with zero
components elsewhere. Projection and inclusion are inverse up to this
contraction. Apply the additive associated-sheaf functor and reverse grading
back to obtain the homotopy equivalence and free-sheaf identifications. Because
i and i+1 are both in [0,d], outside this interval the complementary terms
agree with the original zero terms, so both support bounds persist. Record the
cardinalities of the complementary bases: both affected sizes drop by exactly
one, and all other sizes stay equal. No choice of cancellation degree is part
of this statement; that is established separately from the support bounds. -/
theorem exists_stalk_unit_cancellation_at {Y : Scheme.{u}} (y : Y)
    (P : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ) (d : ℕ)
    (hge : P.IsStrictlyGE 0) (hle : P.IsStrictlyLE d) (n : ℤ → ℕ)
    (hfree : ∀ j : ℤ, Nonempty
      (P.X j ≅ SheafOfModules.free
        (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin (n j)))))
    (i : ℕ) (hi : i < d)
    (hne :
      (((Modules.pullback (Spec.map (Y.residue y))).mapHomologicalComplex _).obj
        P).d (i : ℤ) ((i : ℤ) + 1) ≠ 0) :
    ∃ (P' : CochainComplex (Spec (Y.presheaf.stalk y)).Modules ℤ)
      (n' : ℤ → ℕ),
      Nonempty (HomotopyEquiv P P') ∧
      P'.IsStrictlyGE 0 ∧ P'.IsStrictlyLE d ∧
      (∀ j : ℤ, Nonempty
        (P'.X j ≅ SheafOfModules.free
          (R := (Spec (Y.presheaf.stalk y)).ringCatSheaf) (ULift.{u} (Fin (n' j))))) ∧
      n' (i : ℤ) + 1 = n (i : ℤ) ∧
      n' ((i : ℤ) + 1) + 1 = n ((i : ℤ) + 1) ∧
      (∀ j : ℤ, j ≠ (i : ℤ) → j ≠ (i : ℤ) + 1 → n' j = n j) := by
  classical
  let e := fun j ↦ Classical.choice (hfree j)
  let g := Spec.map (Y.residue y)
  let F := Modules.pullback g
  let φ := (e (i : ℤ)).inv ≫ P.d (i : ℤ) ((i : ℤ) + 1) ≫
    (e ((i : ℤ) + 1)).hom
  have hφ : F.map φ ≠ 0 := by
    intro hz
    apply hne
    change F.map (P.d (i : ℤ) ((i : ℤ) + 1)) = 0
    apply (cancel_epi (F.map (e (i : ℤ)).inv)).mp
    apply (cancel_mono (F.map (e ((i : ℤ) + 1)).hom)).mp
    simpa [φ, ← Functor.map_comp] using hz
  let δ := (pullbackFreeIso g (ULift.{u} (Fin (n (i : ℤ))))).inv ≫ F.map φ ≫
    (pullbackFreeIso g (ULift.{u} (Fin (n ((i : ℤ) + 1))))).hom
  have hδ : δ ≠ 0 := by
    intro hz
    apply hφ
    apply (cancel_epi (pullbackFreeIso g (ULift.{u} (Fin (n (i : ℤ))))).inv).mp
    apply (cancel_mono (pullbackFreeIso g
      (ULift.{u} (Fin (n ((i : ℤ) + 1))))).hom).mp
    simpa [δ] using hz
  have hm := freeMatrix_ne_zero δ hδ
  obtain ⟨q, p, hqp⟩ : ∃ q p, freeMatrix δ q p ≠ 0 := by
    by_contra h
    apply hm
    ext q p
    simpa using not_exists.mp (not_exists.mp h q) p
  have hcoeff : g.appTop (freeMatrix φ q p) ≠ 0 := by
    have hmat := freeMatrix_pullback g φ
    change freeMatrix δ = (freeMatrix φ).map g.appTop at hmat
    rw [hmat] at hqp
    exact hqp
  have hres : Y.residue y ((ΓSpecIso (Y.presheaf.stalk y)).hom
      (freeMatrix φ q p)) ≠ 0 := by
    have hn := congrArg (fun f ↦ f (freeMatrix φ q p))
      (ΓSpecIso_naturality (Y.residue y))
    change (ΓSpecIso (Y.residueField y)).hom (g.appTop (freeMatrix φ q p)) =
      Y.residue y ((ΓSpecIso (Y.presheaf.stalk y)).hom (freeMatrix φ q p)) at hn
    rw [← hn]
    exact fun hz ↦ hcoeff ((ConcreteCategory.bijective_of_isIso
      (ΓSpecIso (Y.residueField y)).hom).1 (by simpa using hz))
  have hunit : IsUnit (freeMatrix φ q p) := by
    have hu := (IsLocalRing.residue_ne_zero_iff_isUnit
      ((ΓSpecIso (Y.presheaf.stalk y)).hom (freeMatrix φ q p))).mp hres
    have hv := hu.map (ΓSpecIso (Y.presheaf.stalk y)).inv.hom
    simpa using hv
  obtain ⟨P', he, hfree', haway⟩ :=
    exists_affine_free_complex_unit_cancellation (Y.presheaf.stalk y) P n e
      (i : ℤ) p q hunit
  let n' : ℤ → ℕ := fun j ↦ if j = (i : ℤ) ∨ j = (i : ℤ) + 1 then n j - 1 else n j
  let _ := hge
  let _ := hle
  refine ⟨P', n', he, ?_, ?_, hfree', ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    obtain ⟨ej⟩ := haway j (by omega) (by omega)
    exact (P.isZero_of_isStrictlyGE 0 j hj).of_iso ej
  · rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    obtain ⟨ej⟩ := haway j (by omega) (by omega)
    exact (P.isZero_of_isStrictlyLE d j hj).of_iso ej
  · have hp := p.down.isLt
    simp only [n', eq_self, true_or, ite_true]
    omega
  · have hq := q.down.isLt
    simp only [n', eq_self, or_true, ite_true]
    omega
  · intro j hj hj'
    simp [n', hj, hj']

end AlgebraicGeometry.Scheme.Modules
