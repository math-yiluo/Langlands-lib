/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechBaseChange
public import Mathlib.Algebra.Category.ModuleCat.Descent
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyCechCocycles

/-! # Compatibility of the Cech model with the canonical flat cohomology comparison

Source: Stacks Project, Tags 02KH, 01XD and 02KE.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}} {ι : Type u}

/-- Identify categorical scalar extension with tensor using the given algebra action.
Source: Mathlib's definition of extendScalars and the algebra smul identity.
(blueprint: lem-pc-flat-cech-cohomology-square) -/
noncomputable def extendScalarsTensorIso (A : Type u) [AddCommGroup A] [Module R A] :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R A) ≅
      ModuleCat.of S (TensorProduct R S A) := by
  let e : (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) ≃ₗ[R] S :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r s ↦ (@Algebra.smul_def R S _ _ _ r s).symm }
  let t := TensorProduct.congr e (LinearEquiv.refl R A)
  let eS : (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R A) ≃ₗ[S]
      TensorProduct R S A :=
    { toEquiv := t.toEquiv
      map_add' := t.map_add
      map_smul' := by
        intro b x
        change t (b • x) = b • t x
        induction x using TensorProduct.inductionOn with
        | tmul s a => rfl
        | add x y hx hy => simp only [smul_add, map_add, hx, hy] }
  exact eS.toModuleIso

/-- The tensor identification is the identity on pure tensors.
Source: the defining tensor maps in Mathlib.
(blueprint: lem-pc-flat-cech-cohomology-square) -/
lemma extendScalarsTensorIso_hom_tmul (A : Type u) [AddCommGroup A] [Module R A]
    (b : S) (a : A) :
    (extendScalarsTensorIso (R := R) (S := S) A).hom
      (TensorProduct.tmul R b a) = TensorProduct.tmul R b a := by
  rfl


/-- Exact scalar extension commutes with the homology of the ordered Cech complex.
This uses only the three terms at the selected degree; boundedness is unnecessary.
Source: Mathlib `ShortComplex.mapHomologyIso`, as in Stacks Tag 02KH.
(blueprint: lem-pc-flat-tensor-complex-cohom) -/
noncomputable def flatCechHomologyIso [Module.Flat R S] (f : X ⟶ Spec (.of R))
    (U : ι → X.Opens) (M : X.Modules) (q : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).obj ((cechOver f U M).homology q) ≅
      (tensorCech (S := S) f U M).homology q := by
  have : (ModuleCat.extendScalars (algebraMap R S)).Additive :=
    (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).left_adjoint_additive
  have := (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
    (algebraMap R S)).leftAdjoint_preservesColimits
  have : PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap R S)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
  exact ((cechOver f U M).sc q).mapHomologyIso (ModuleCat.extendScalars (algebraMap R S)) |>.symm

/-- The exact-tensor homology isomorphism takes an extended cycle to its class.
This is the universal property of cycles and homology, with no geometric input. -/
private theorem extendedCechCycles_homology [Module.Flat R S]
    (f : X ⟶ Spec (.of R)) (U : ι → X.Opens) (M : X.Modules)
    (c : tensorCech (S := S) f U M ⟶
      cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)) (q : ℕ) :
    (ModuleCat.extendScalars (algebraMap R S)).map ((cechOver f U M).homologyπ q) ≫
      (flatCechHomologyIso (S := S) f U M q).hom ≫
        HomologicalComplex.homologyMap c q =
      extendedCechCycles f U M c q ≫
        (cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
          (baseChangedModule (S := S) f M)).homologyπ q := by
  set_option backward.isDefEq.respectTransparency false in
    have : (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).left_adjoint_additive
    have := (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap R S)).leftAdjoint_preservesColimits
    have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
    let C := cechOver f U M
    let D := cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
      (baseChangedModule (S := S) f M)
    change (ModuleCat.extendScalars (algebraMap R S)).map (C.homologyπ q) ≫
      ((C.sc q).mapHomologyIso (ModuleCat.extendScalars (algebraMap R S))).inv ≫
        HomologicalComplex.homologyMap c q = extendedCechCycles f U M c q ≫ D.homologyπ q
    let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
    let E := (F.mapHomologicalComplex (.up ℕ)).obj C
    have hπ : F.map (C.homologyπ q) ≫ ((C.sc q).mapHomologyIso F).inv =
        ((C.sc q).mapCyclesIso F).inv ≫ E.homologyπ q := by
      change F.map (C.sc q).homologyπ ≫ ((C.sc q).mapHomologyIso F).inv =
        ((C.sc q).mapCyclesIso F).inv ≫ ((C.sc q).map F).homologyπ
      let h := (C.sc q).homologyData.left
      rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
      simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc]
      rw [← Category.assoc, ← F.map_comp, h.homologyπ_comp_homologyIso_hom]
      rw [F.map_comp, Category.assoc]
      change F.map h.cyclesIso.hom ≫ (h.map F).π ≫ (h.map F).homologyIso.inv =
        F.map h.cyclesIso.hom ≫ (h.map F).cyclesIso.inv ≫ ((C.sc q).map F).homologyπ
      rw [(h.map F).π_comp_homologyIso_inv]
    rw [← Category.assoc, hπ, Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc]
    apply congrArg (fun t ↦ t ≫ D.homologyπ q)
    apply (cancel_mono (D.iCycles q)).mp
    simp only [Category.assoc]
    rw [show HomologicalComplex.cyclesMap c q ≫ D.iCycles q = E.iCycles q ≫ c.f q from
      HomologicalComplex.cyclesMap_i c q]
    change ((C.sc q).mapCyclesIso F).inv ≫ (E.iCycles q ≫ c.f q) = _
    have hi : ((C.sc q).mapCyclesIso F).inv ≫ E.iCycles q = F.map (C.iCycles q) := by
      change ((C.sc q).mapCyclesIso F).inv ≫ ((C.sc q).map F).iCycles =
        F.map (C.sc q).iCycles
      rw [← (C.sc q).mapCyclesIso_hom_iCycles F, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hi]
    dsimp only [extendedCechCycles, D, C, F]
    rw [HomologicalComplex.liftCycles_i]

/-- Leray identifications can be chosen so that any chain map with the canonical
pure-tensor formula induces the specified sheaf cohomology comparison. This is a
compatibility statement; it does not assert that the chain map is invertible.

Source: Stacks Project, Lemma 30.5.2 (Tag 02KH), separated-case paragraph;
Lemma 30.2.6 (Tag 01XD), and the canonical comparison of Tag 02KE.
(blueprint: lem-pc-flat-cech-cohomology-square)

Proof: Separatedness over an affine base makes the tuple intersections of U affine;
base change gives an affine-intersection cover on X_S. The pulled-back module is
quasi-coherent. Apply the Cech-to-sheaf comparison to these two covers. Affine
acyclicity makes the comparison maps isomorphisms. The Cech-to-sheaf edge maps
are natural for the inverse-image coefficient map induced by the module adjunction
unit: construct them from the augmented Cech double complexes of injective
resolutions, and use a resolution comparison for this coefficient map. On each
tuple intersection the map of augmentations is exactly the map specified by
IsCechBaseChange. Thus the resulting square commutes on cocycles and boundaries.
The scalar action on each comparison is induced by multiplication on the module,
so the first edge map is R-linear and the second S-linear. Restricting scalars from
global functions gives e and e'. Finally extend the original edge map to S tensor,
and use the canonical exact-tensor homology comparison flatCechHomologyIso.
On pure tensors b tensor x the composite is b times the inverse-image cohomology
map of the unit. This is the defining formula for H.baseChange; tensor induction
then gives the displayed equality. No invertibility of c is used in this argument.
The comparison is valid in degree zero, on the empty scheme, and for any flat
algebra including the zero ring. -/
theorem exists_cechBaseChange_cohomology_square [Module.Flat R S]
    (f : X ⟶ Spec (.of R)) [IsSeparated f] [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (q : ℕ)
    (c : tensorCech (S := S) f U M ⟶
      cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)) (hc : IsCechBaseChange f U M c) :
    ∃ e : (cechOver f U M).homology q ≅ ModuleCat.of R (HOver f M q),
    ∃ e' : (cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
        (baseChangedModule (S := S) f M)).homology q ≅
          ModuleCat.of S (HOver (baseChangeSnd (S := S) f)
            (baseChangedModule (S := S) f M) q),
      (extendScalarsTensorIso (S := S) (HOver f M q)).inv ≫
        (ModuleCat.extendScalars (algebraMap R S)).map e.inv ≫
        (flatCechHomologyIso (S := S) f U M q).hom ≫
        HomologicalComplex.homologyMap c q ≫ e'.hom =
          ModuleCat.ofHom (H.baseChange (S := S) f M q) := by
  set_option backward.isDefEq.respectTransparency false in
    obtain ⟨e, e', hz⟩ := exists_cechBaseChange_cocycle_comparison
      (S := S) f U hU hcover M q c hc
    refine ⟨e, e', ?_⟩
    let C := cechOver f U M
    let D := cechOver (baseChangeSnd (S := S) f) (baseChangeCover (S := S) f U)
      (baseChangedModule (S := S) f M)
    have : (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)).Additive :=
      (ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).left_adjoint_additive
    have := (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
      (algebraMap R S)).leftAdjoint_preservesColimits
    have : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} (algebraMap R S)) :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        (RingHom.flat_algebraMap_iff.mpr inferInstance)
    let F := ModuleCat.extendScalars.{u, u, u} (algebraMap R S)
    apply (cancel_epi (extendScalarsTensorIso (S := S) (HOver f M q)).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    apply (cancel_epi (F.map e.hom)).mp
    dsimp only [F]
    rw [← Category.assoc ((ModuleCat.extendScalars (algebraMap R S)).map e.hom),
      ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    apply (cancel_epi (F.map (C.homologyπ q))).mp
    dsimp only [F]
    trans (extendedCechCycles f U M c q ≫ D.homologyπ q) ≫ e'.hom
    · simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ e'.hom)
        (show (ModuleCat.extendScalars (algebraMap R S)).map (C.homologyπ q) ≫
          (flatCechHomologyIso (S := S) f U M q).hom ≫ HomologicalComplex.homologyMap c q =
            extendedCechCycles f U M c q ≫ D.homologyπ q from
          extendedCechCycles_homology f U M c q)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change e'.hom (D.homologyπ q (extendedCechCycles f U M c q x)) =
      H.baseChange (S := S) f M q ((extendScalarsTensorIso (S := S) (HOver f M q)).hom
        (F.map e.hom (F.map (C.homologyπ q) x)))
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul b z =>
      have h := hz z
      have ht : TensorProduct.tmul R b z =
          (show S from b) • (TensorProduct.tmul R (1 : S) z : F.obj (C.cycles q)) := by
        rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
      rw [ht]
      change e'.hom.hom ((D.homologyπ q).hom ((extendedCechCycles f U M c q).hom
        ((show S from b) • ((TensorProduct.tmul R (1 : S) z) : F.obj (C.cycles q))))) =
          H.baseChange (S := S) f M q ((extendScalarsTensorIso (S := S) (HOver f M q)).hom.hom
            ((F.map e.hom).hom ((F.map (C.homologyπ q)).hom
              ((show S from b) • ((TensorProduct.tmul R (1 : S) z) : F.obj (C.cycles q))))))
      simp only [LinearMap.map_smul]
      apply congrArg (fun t ↦ (show S from b) • t)
      change e'.hom (D.homologyπ q
        (extendedCechCycles f U M c q (TensorProduct.tmul R (1 : S) z))) =
        H.baseChange (S := S) f M q (TensorProduct.tmul R (1 : S) (e.hom (C.homologyπ q z)))
      simpa only [H.baseChange, extendComparison, TensorProduct.AlgebraTensorModule.lift_tmul,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, one_smul] using h

end AlgebraicGeometry.Scheme.Modules
