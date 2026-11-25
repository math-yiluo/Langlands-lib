/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Vanishing of a bottom differential with full-rank kernel
Source: Stacks Project, Tags 0BDL and 0EWY.
(blueprint: lem-sc-finite-free-bottom-differential-zero). -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
open Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


private theorem free_map_ext_top {X : Scheme.{u}} {I J : Type u}
    {f g : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ SheafOfModules.free J}
    (h : Modules.Hom.app f ⊤ = Modules.Hom.app g ⊤) : f = g := by
  apply free_hom_ext
  intro i
  apply (SheafOfModules.unitHomEquiv _).injective
  apply Subtype.ext
  funext W
  have htop : (SheafOfModules.unitHomEquiv _ (SheafOfModules.ιFree i ≫ f)).val (op ⊤) =
      (SheafOfModules.unitHomEquiv _ (SheafOfModules.ιFree i ≫ g)).val (op ⊤) := by
    change Modules.Hom.app f ⊤ (Modules.Hom.app (SheafOfModules.ιFree i) ⊤ (1 : Γ(X, ⊤))) = _
    rw [h]
    rfl
  have hs := (SheafOfModules.unitHomEquiv _ (SheafOfModules.ιFree i ≫ f)).property
    (homOfLE (show W.unop ≤ ⊤ from le_top)).op
  have ht := (SheafOfModules.unitHomEquiv _ (SheafOfModules.ιFree i ≫ g)).property
    (homOfLE (show W.unop ≤ ⊤ from le_top)).op
  dsimp at hs ht
  exact hs.symm.trans ((congrArg (fun x ↦
    (SheafOfModules.free (R := X.ringCatSheaf) J).val.presheaf.map
      (homOfLE (show W.unop ≤ ⊤ from le_top)).op x) htop).trans ht)

private theorem free_zero_of_square_mono {X : Scheme.{u}} (r n : ℕ)
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      SheafOfModules.free (ULift.{u} (Fin r))) [Mono φ]
    (ψ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      SheafOfModules.free (ULift.{u} (Fin n))) (hz : φ ≫ ψ = 0) : ψ = 0 := by
  classical
  let A := freeMatrix φ
  let B := freeMatrix ψ
  let e := freeSectionsEquiv (X := X) (ULift.{u} (Fin r))
  let q := freeSectionsEquiv (X := X) (ULift.{u} (Fin n))
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    apply e.symm.injective
    apply (ModuleCat.mono_iff_injective
      ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map φ)).1 inferInstance
    change Modules.Hom.app φ ⊤ (e.symm x) = Modules.Hom.app φ ⊤ (e.symm y)
    apply e.injective
    simpa only [e, freeSectionsEquiv_app, LinearEquiv.apply_symm_apply] using hxy
  have ht : Function.Injective (fun x ↦ Matrix.vecMul x A) :=
    Matrix.vecMul_injective_iff.2
      (Matrix.linearIndependent_col_iff_row.1 (Matrix.mulVec_injective_iff.1 hinj))
  have hm : B * A = 0 := by
    apply Matrix.mulVec_injective
    funext x
    rw [← Matrix.mulVec_mulVec]
    have hh := congrArg (fun f ↦ q (Modules.Hom.app f ⊤ (e.symm x))) hz
    change q (Modules.Hom.app ψ ⊤ (Modules.Hom.app φ ⊤ (e.symm x))) = q 0 at hh
    simpa only [q, freeSectionsEquiv_app, e, LinearEquiv.apply_symm_apply,
      map_zero, Matrix.zero_mulVec] using hh
  have hB : B = 0 := by
    ext i j
    have hrow : Matrix.vecMul (B i) A = Matrix.vecMul 0 A := by
      funext k
      have hh := congrFun (congrFun hm i) k
      simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, mul_comm] using hh
    exact congrFun (ht hrow) j
  apply free_map_ext_top
  ext x
  apply q.injective
  simp [q, B, freeSectionsEquiv_app, hB]


/-- A finite-free bottom term and locally free bottom homology of the same rank
force the outgoing differential to vanish.
Source: Stacks Project, Tag 0BDL, matrix-chart proof; Tag 0EWY.
(blueprint: lem-sc-finite-free-bottom-differential-zero).

Proof: The term in degree a-1 is zero, so homology in degree a is the kernel
of d^a. Cover X by opens trivializing this locally free kernel. On each such
open its inclusion into K^a is an injective square map of free rank-r sheaves.
Global sections are left exact, and finite free sheaves have free sections of
the stated ranks on every scheme, so no affine refinement is needed.
The square injective matrix has injective transpose by Tag 0EWY. Every row
of the matrix for d^a annihilates the kernel inclusion, and therefore is zero.
Thus the differential is zero on the covering, hence is zero globally.
No splitting of the kernel inclusion is asserted. At r=0 the source term is
zero; on the empty X all module morphisms coincide. -/
theorem finiteFreeBottom_differential_zero
    (X : Scheme.{u})
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (a : ℤ) (r : ℕ)
    (hbelow : ∀ i : ℤ, i < a → IsZero (K.X i))
    (hfirst : Nonempty (K.X a ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r))))
    (hnext : ∃ n : ℕ, Nonempty (K.X (a + 1) ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin n))))
    (hhomology : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (K.homology a) r) :
    K.d a (a + 1) = 0  := by
  classical
  obtain ⟨eFirst⟩ := hfirst
  obtain ⟨n, ⟨eNext⟩⟩ := hnext
  let C := K.sc' (a - 1) a (a + 1)
  have hf : C.f = 0 := (hbelow (a - 1) (by omega)).eq_of_src _ _
  let e : K.homology a ≅ C.cycles :=
    K.homologyIsoSc' (a - 1) a (a + 1) (by simp) (by simp) ≪≫
      C.leftHomologyIso.symm ≪≫ (C.cyclesIsoLeftHomology hf).symm
  let j : K.homology a ⟶ K.X a := e.hom ≫ C.iCycles
  have : Mono j := by dsimp [j]; infer_instance
  have hj : j ≫ K.d a (a + 1) = 0 := by
    dsimp only [j]
    rw [Category.assoc]
    exact (congrArg (fun f ↦ e.hom ≫ f) C.iCycles_g).trans (comp_zero)
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (K.homology a) r := hhomology
  obtain ⟨I, U, hU, htriv⟩ :=
    Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free (K.homology a) (r := r)
  apply Modules.hom_ext_of_restrictAdjunction_unit U
    (fun x ↦ TopologicalSpace.Opens.mem_iSup.1 (by rw [hU]; trivial))
  intro i
  let F := Modules.restrictFunctor (U i).ι
  let e0 := F.mapIso eFirst ≪≫ Modules.restrictFreeIso (U i).ι (ULift.{u} (Fin r))
  let e1 := F.mapIso eNext ≪≫ Modules.restrictFreeIso (U i).ι (ULift.{u} (Fin n))
  let φ := (htriv i).some.inv ≫ F.map j ≫ e0.hom
  let ψ := e0.inv ≫ F.map (K.d a (a + 1)) ≫ e1.hom
  have : Mono φ := by dsimp [φ]; infer_instance
  have hz : φ ≫ ψ = 0 := by
    simp only [φ, ψ, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← F.map_comp_assoc, hj, F.map_zero, zero_comp, comp_zero]
  have hψ := free_zero_of_square_mono r n φ ψ hz
  have hd : F.map (K.d a (a + 1)) = 0 := by
    have hh := congrArg (fun f ↦ e0.hom ≫ f ≫ e1.inv) hψ
    simpa [ψ] using hh
  have hh := (Modules.restrictAdjunction (U i).ι).unit.naturality (K.d a (a + 1))
  change K.d a (a + 1) ≫ (Modules.restrictAdjunction (U i).ι).unit.app (K.X (a + 1)) =
    (Modules.restrictAdjunction (U i).ι).unit.app (K.X a) ≫
      (Modules.pushforward (U i).ι).map (F.map (K.d a (a + 1))) at hh
  rw [hd, Functor.map_zero, comp_zero] at hh
  simpa only [zero_comp] using hh

end AlgebraicGeometry.Scheme
