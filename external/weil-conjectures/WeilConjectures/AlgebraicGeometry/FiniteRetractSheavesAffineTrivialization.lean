/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.SingleFiniteRetractSheafAffineTrivialization

/-! # Simultaneous affine trivialization of finitely many finite free retracts

Source: Stacks Project, Tags 00NX, 01IA and 01IB.
(blueprint: lem-pc-finite-retract-sheaves-affine-trivialization).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private noncomputable def restrictFreeIso (X : Scheme.{u}) (U V : X.Opens)
    (h : V ≤ U) (r : ℕ) :
    (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE h)).obj
      (SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r))) ≅
      SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r)) :=
  (asIso (CategoryTheory.Limits.sigmaComparison
    (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE h))
    (fun _ : ULift.{u} (Fin r) ↦
      SheafOfModules.unit ((moduleRings X.toRingedSpace).over U)))).symm ≪≫
    CategoryTheory.Limits.Sigma.mapIso (fun _ ↦ SheafOfModules.overMapUnitIso (homOfLE h))

private noncomputable def restrictCompIso (X : Scheme.{u}) (U V W : X.Opens)
    (hVU : V ≤ U) (hWV : W ≤ V)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
    (SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (hWV.trans hVU))).obj M ≅
    (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hWV)).obj
      ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj M) :=
  Iso.refl _

/-- A finite family of retracts of finite free sheaves becomes finite free on one affine
neighbourhood of a specified point.

Source: Stacks Project, Algebra, Tag 00NX (3) implies (7), and Schemes, Tags 01IA
and 01IB; https://stacks.math.columbia.edu/tag/00NX.
Proof: Choose an affine neighbourhood W of x inside U. Restriction preserves finite
free sheaves and the splitting equations. For each index in s, the composite of its
retraction and section is an idempotent endomorphism of a finite free sheaf on W.
Use the equivalence between the localized-site sheaves on W and W.Modules. The affine
tilde-Gamma adjunction identifies this endomorphism with an idempotent matrix over
Gamma(W,O_W). Its image is a finite projective module, being a summand of a finite
free module. Applying tilde to its splitting yields the original restricted sheaf:
both are splittings of the same idempotent, hence canonically isomorphic.
The finite projective standard free cover supplies, for each of the finitely many
indices, a principal open containing x on which that module is finite free.
Their intersection is again a principal open in W (the product of the elements),
so is affine and contains x. Sections/localization and tilde identify the sheaf
restrictions there with free sheaves of the respective finite ranks. Compose the
nested-restriction comparisons to obtain the stated trivializations. For s empty
use W itself. A zero summand has rank zero; no positive rank is required. If U
is empty there is no x satisfying hx, so no existence claim is imposed.
(blueprint: lem-pc-finite-retract-sheaves-affine-trivialization). -/
theorem exists_affine_trivialization_of_finite_retracts
    (X : Scheme.{u}) (U : X.Opens) (s : Finset ℤ)
    (M : ℤ → SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (hM : ∀ n ∈ s, ∃ m : ℕ,
      ∃ (ι : M n ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ M n),
        ι ≫ π = 𝟙 (M n))
    (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ hVU : V ≤ U, IsAffine V.toScheme ∧
      ∀ n ∈ s, ∃ r : ℕ, Nonempty
        ((SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hVU)).obj (M n) ≅
          SheafOfModules.free
            (R := (moduleRings X.toRingedSpace).over V) (ULift.{u} (Fin r))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact ⟨V, hxV, hVU, hV, fun n hn ↦ (Finset.notMem_empty n hn).elim⟩
  | @insert a s ha ih =>
    obtain ⟨V, hxV, hVU, hV, hfree⟩ := ih (fun n hn ↦ hM n (Finset.mem_insert_of_mem hn))
    obtain ⟨W, hxW, hWU, _, r, ⟨e⟩⟩ :=
      exists_affine_trivialization_of_finite_retract X U (M a)
        (hM a (Finset.mem_insert_self a s)) x hx
    obtain ⟨Z, hZ, hxZ, hZVW⟩ :=
      exists_isAffineOpen_mem_and_subset (U := V ⊓ W) ⟨hxV, hxW⟩
    have hZV : Z ≤ V := hZVW.trans inf_le_left
    have hZW : Z ≤ W := hZVW.trans inf_le_right
    have hZU : Z ≤ U := hZV.trans hVU
    refine ⟨Z, hxZ, hZU, hZ, ?_⟩
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · refine ⟨r, ⟨?_⟩⟩
      exact restrictCompIso X U W Z hWU hZW (M n) ≪≫
        (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hZW)).mapIso e ≪≫
          restrictFreeIso X W Z hZW r
    · obtain ⟨r, ⟨e⟩⟩ := hfree n hn
      refine ⟨r, ⟨?_⟩⟩
      exact restrictCompIso X U V Z hVU hZV (M n) ≪≫
        (SheafOfModules.overMap (moduleRings X.toRingedSpace) (homOfLE hZV)).mapIso e ≪≫
          restrictFreeIso X V Z hZV r

end AlgebraicGeometry.Scheme
