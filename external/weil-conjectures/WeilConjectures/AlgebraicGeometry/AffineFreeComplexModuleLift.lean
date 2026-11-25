/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Lifting an affine free complex and its unit coefficient

Source: Stacks Project, Tags 01I7 and 00MT, the affine comparison before pivot elimination.
(blueprint: lem-pc-affine-free-complex-module-lift)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

private noncomputable def freeCoordinates (R : CommRingCat.{u}) (I : Type u)
    [Fintype I] [DecidableEq I] :
    Γ(SheafOfModules.free (R := (Spec R).ringCatSheaf) I, ⊤) ≃ₗ[R] (I → R) where
  toFun x j := (ΓSpecIso R).hom (freeSectionsEquiv I x j)
  invFun x := (freeSectionsEquiv I).symm (fun j ↦ (ΓSpecIso R).inv (x j))
  left_inv x := by
    apply (freeSectionsEquiv I).injective
    ext j
    simp
  right_inv x := by
    ext j
    simp
  map_add' x y := by
    ext j
    simp
  map_smul' r x := by
    ext j
    have hs : r • x = (ΓSpecIso R).inv r • x := by
      rw [smul_Spec_def]
      congr 1
    rw [hs]
    simp [smul_eq_mul]

private noncomputable def affineFreeCoordinates (R : CommRingCat.{u})
    {M : (Spec R).Modules} (I : Type u) [Fintype I] [DecidableEq I]
    (e : M ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) I) :
    (moduleSpecΓFunctor (R := R)).obj M ≃ₗ[R] (I → R) :=
  ((appLinearEquivOfIso e ⊤).restrictScalars R).trans (freeCoordinates R I)

private lemma freeCoordinates_symm_single (R : CommRingCat.{u}) (I : Type u)
    [Fintype I] [DecidableEq I] (p : I) :
    (freeCoordinates R I).symm (Pi.single p 1) =
      (freeSectionsEquiv I).symm (Pi.single p 1) := by
  change (freeSectionsEquiv I).symm (fun j ↦ (ΓSpecIso R).inv ((Pi.single p (1 : R) : I → R) j)) = _
  congr 1
  ext j
  by_cases h : p = j <;> simp [h]

private lemma affineFreeCoordinates_matrix (R : CommRingCat.{u})
    {M N : (Spec R).Modules} (I J : Type u)
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (eM : M ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) I)
    (eN : N ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) J)
    (f : M ⟶ N) (p : I) (q : J) :
    LinearMap.toMatrix (Module.Basis.ofEquivFun (affineFreeCoordinates R I eM))
      (Module.Basis.ofEquivFun (affineFreeCoordinates R J eN))
      ((moduleSpecΓFunctor (R := R)).map f).hom q p =
        (ΓSpecIso R).hom (freeMatrix (eM.inv ≫ f ≫ eN.hom) q p) := by
  rw [LinearMap.toMatrix_apply, Module.Basis.ofEquivFun_repr_apply,
    Module.Basis.coe_ofEquivFun]
  change (freeCoordinates R J)
    (Hom.app eN.hom ⊤ (Hom.app f ⊤
      (Hom.app eM.inv ⊤ ((freeCoordinates R I).symm (Pi.single p 1))))) q = _
  rw [freeCoordinates_symm_single]
  change (ΓSpecIso R).hom
    (freeSectionsEquiv J (Hom.app (eM.inv ≫ f ≫ eN.hom) ⊤
      ((freeSectionsEquiv I).symm (Pi.single p 1))) q) = _
  rw [freeSectionsEquiv_app, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one]
  rfl

/-- Lift the original complex, before any cancellation, to modules with finite bases.

Source: Stacks Project, Tag 01I7 (affine associated-sheaf equivalence), and Tag 00MT
(the supplied matrix entry). (blueprint: lem-pc-affine-free-complex-module-lift)

Proof: In degree k take the module of finitely supported functions on the supplied basis
in degree -k. Identify its associated sheaf with P.X (-k) using tildeFinsupp and e.symm.
Use fullness of tilde to lift the conjugated differential, and faithfulness to prove
its shape and square-zero equations. These give a chain complex C. Reindex the canonical
ULift basis by Fin, set m k = n (-k), and transport the supplied pivot indices.
The isomorphism isoTop, followed by the structure-sheaf global-sections isomorphism,
identifies the coordinates of the lifted differential with freeMatrix. This is an
isomorphism of rings, so the given unit coefficient stays a unit. The chosen sheaf
identifications give φ and its differential compatibility. Double negation gives
m (-j) = n j. No rank reduction or homotopy equivalence is asserted here; this is only
the affine lifting step. Empty bases cannot contain the supplied indices; the zero
ring is allowed, since preservation of units does not use nontriviality. -/
theorem exists_affine_free_complex_module_lift (R : CommRingCat.{u})
    (P : CochainComplex (Spec R).Modules ℤ) (n : ℤ → ℕ)
    (e : ∀ j : ℤ, P.X j ≅ SheafOfModules.free
      (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin (n j))))
    (i : ℤ) (p : ULift.{u} (Fin (n i))) (q : ULift.{u} (Fin (n (i + 1))))
    (hunit : IsUnit (freeMatrix ((e i).inv ≫ P.d i (i + 1) ≫ (e (i + 1)).hom) q p)) :
    ∃ (C : ChainComplex (ModuleCat.{u} R) ℤ) (m : ℤ → ℕ)
      (b : ∀ k : ℤ, Module.Basis (Fin (m k)) R (C.X k))
      (p' : Fin (m (-i))) (q' : Fin (m (-i - 1))),
      (∀ j : ℤ, m (-j) = n j) ∧
      IsUnit (LinearMap.toMatrix (b (-i)) (b (-i - 1))
        (C.d (-i) (-i - 1)).hom q' p') ∧
      ∃ φ : ∀ j : ℤ, tilde (C.X (-j)) ≅ P.X j,
        ∀ j k : ℤ, (ComplexShape.up ℤ).Rel j k →
          (φ j).hom ≫ P.d j k = tilde.map (C.d (-j) (-k)) ≫ (φ k).hom  := by
  classical
  -- Use the canonical global-sections model rather than lifting each differential separately.
  let F := moduleSpecΓFunctor (R := R)
  have hzero (M N : (Spec R).Modules) : F.map (0 : M ⟶ N) = 0 := by
    ext x
    rfl
  let C : ChainComplex (ModuleCat.{u} R) ℤ :=
    { X := fun k ↦ F.obj (P.X (-k))
      d := fun k l ↦ F.map (P.d (-k) (-l))
      shape := by
        intro k l h
        rw [P.shape]
        · exact hzero _ _
        · intro h'
          apply h
          change l + 1 = k
          change -k + 1 = -l at h'
          omega
      d_comp_d' := by
        intro k l t _ _
        rw [← F.map_comp, P.d_comp_d]
        exact hzero _ _ }
  let m (k : ℤ) := n (-k)
  let v (k : ℤ) : C.X k ≃ₗ[R] (ULift.{u} (Fin (m k)) → R) :=
    affineFreeCoordinates R (ULift.{u} (Fin (m k))) (e (-k))
  let b (k : ℤ) : Module.Basis (Fin (m k)) R (C.X k) :=
    (Module.Basis.ofEquivFun (v k)).reindex Equiv.ulift
  have hi : - -i = i := neg_neg i
  have hq : -(-i - 1) = i + 1 := by omega
  let p' : Fin (m (-i)) := Fin.cast (congrArg n hi).symm p.down
  let q' : Fin (m (-i - 1)) := Fin.cast (congrArg n hq).symm q.down
  refine ⟨C, m, b, p', q', ?_, ?_, ?_⟩
  · intro j
    simp [m]
  · have hcoeff := affineFreeCoordinates_matrix R
      (ULift.{u} (Fin (m (-i)))) (ULift.{u} (Fin (m (-i - 1))))
      (e (- -i)) (e (-(-i - 1))) (P.d (- -i) (-(-i - 1)))
      (ULift.up p') (ULift.up q')
    have hu := hunit.map (ΓSpecIso R).hom.hom
    have hu' : IsUnit
        (LinearMap.toMatrix (Module.Basis.ofEquivFun (v (-i)))
          (Module.Basis.ofEquivFun (v (-i - 1)))
          (C.d (-i) (-i - 1)).hom (ULift.up q') (ULift.up p')) := by
      rw [hcoeff]
      have hmat (j k : ℤ) (hj : j = i) (hk : k = i + 1) :
          freeMatrix ((e j).inv ≫ P.d j k ≫ (e k).hom)
            (ULift.up (Fin.cast (congrArg n hk).symm q.down))
            (ULift.up (Fin.cast (congrArg n hj).symm p.down)) =
              freeMatrix ((e i).inv ≫ P.d i (i + 1) ≫ (e (i + 1)).hom) q p := by
        subst j
        subst k
        cases p
        cases q
        rfl
      change IsUnit ((ΓSpecIso R).hom
        (freeMatrix ((e (- -i)).inv ≫ P.d (- -i) (-(-i - 1)) ≫
          (e (-(-i - 1))).hom) (ULift.up q') (ULift.up p')))
      rw [hmat (- -i) (-(-i - 1)) hi hq]
      exact hu
    simpa only [LinearMap.toMatrix_apply, b, Module.Basis.reindex_apply,
      Module.Basis.repr_reindex_apply, Equiv.ulift_symm_apply] using hu'
  · have hIso (j : ℤ) : IsIso (P.X j).fromTildeΓ :=
      isIso_fromTildeΓ_iff.mpr
        ⟨_, ⟨tildeFinsupp (ULift.{u} (Fin (n j))) ≪≫ (e j).symm⟩⟩
    let φ (j : ℤ) : tilde (C.X (-j)) ≅ P.X j :=
      (tilde.functor R).mapIso (F.mapIso (P.XIsoOfEq (neg_neg j))) ≪≫
        asIso (P.X j).fromTildeΓ
    refine ⟨φ, ?_⟩
    intro j k _
    change tilde.map (F.map (P.XIsoOfEq (neg_neg j)).hom) ≫
      (P.X j).fromTildeΓ ≫ P.d j k =
      tilde.map (F.map (P.d (- -j) (- -k))) ≫
        tilde.map (F.map (P.XIsoOfEq (neg_neg k)).hom) ≫ (P.X k).fromTildeΓ
    have hn : (P.X j).fromTildeΓ ≫ P.d j k =
        tilde.map (F.map (P.d j k)) ≫ (P.X k).fromTildeΓ :=
      (fromTildeΓNatTrans.naturality (P.d j k)).symm
    rw [hn, ← tilde.map_comp_assoc, ← F.map_comp,
      HomologicalComplex.XIsoOfEq_hom_comp_d, ← tilde.map_comp_assoc, ← F.map_comp,
      HomologicalComplex.d_comp_XIsoOfEq_hom]

end AlgebraicGeometry.Scheme.Modules
