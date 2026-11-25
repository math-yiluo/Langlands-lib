/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Continuous matrices for locally free integral lattice pairs

Source: Bhatt--Scholze, Proposition 6.8.4(6), local bases
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

open scoped ChangeOfRings Matrix

private noncomputable def frameCoordinates (X : Scheme.{u}) (K : Type u) [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K] (U : X.ProEt) (n : ℕ)
    (T : (Over U)ᵒᵖ) :
    (latticeFreeSheaf X K U n).val.obj T ≃ₗ[
      (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)]
        (Fin n → (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)) :=
  by
    let c : (latticeFreeSheaf X K U n).val.obj T ≃ₗ[
        (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)]
          (ULift.{u + 1} (Fin n) → (latticeCoefficientSheaf X K).obj.obj
            (op T.unop.left)) :=
      SheafOfModules.freeSectionsLinearEquiv (R := (latticeModuleRing X K).over U)
        (ULift.{u + 1} (Fin n)) T
    exact c.trans (LinearEquiv.funCongrLeft _ _ Equiv.ulift.symm)

private def basisTestObject {X : Scheme.{u}} {V : X.ProEt}
    {R : Sheaf ((Scheme.ProEt.topology X).over V) RingCat.{u + 1}}
    {M : SheafOfModules.{u + 1} R} (q : M.LocalGeneratorsData) (i : q.I)
    (W : X.ProEt) (a : W ⟶ V) (t : Over.mk a ⟶ q.X i) (T : Over W) : Over (q.X i) :=
  Over.mk (show Over.mk (T.hom ≫ a) ⟶ q.X i from
    Over.homMk (T.hom ≫ t.left) (by simp [Category.assoc]))

private noncomputable def integralCoordinates {C : Type w} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u + 1}]
    [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {M : SheafOfModules.{u + 1} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] [q.IsFiniteType] (i : q.I)
    [Fintype (q.generators i).I] [DecidableEq (q.generators i).I]
    (T : (Over (q.X i))ᵒᵖ) :
    M.val.obj (op T.unop.left) ≃ₗ[R.obj.obj (op T.unop.left)]
      ((q.generators i).I → R.obj.obj (op T.unop.left)) :=
  by
    let h : HasSheafify (J.over (q.X i)) AddCommGrpCat.{u + 1} := inferInstance
    exact SheafOfModules.sectionsLinearEquivOfIsoFree (asIso (q.generators i).π).symm T

private theorem integralBasis_eq {C : Type w} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u + 1}]
    [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {M : SheafOfModules.{u + 1} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] [q.IsFiniteType] (i : q.I)
    [Fintype (q.generators i).I] [DecidableEq (q.generators i).I]
    (T : (Over (q.X i))ᵒᵖ) (j : (q.generators i).I) :
    Module.Basis.ofEquivFun (integralCoordinates q i T) j =
      (q.generators i).π.val.app T
        ((SheafOfModules.ιFree (R := R.over (q.X i)) j).val.app T
          (1 : (R.over (q.X i)).obj.obj T)) := by
  rw [Module.Basis.coe_ofEquivFun]
  change (q.generators i).π.val.app T
    ((SheafOfModules.freeSectionsLinearEquiv
      (R := R.over (q.X i)) (q.generators i).I T).symm (Pi.single j 1)) = _
  congr 1
  change (∑ k, (SheafOfModules.ιFree (R := R.over (q.X i)) k).val.app T
    ((Pi.single j (1 : (R.over (q.X i)).obj.obj T) :
      (q.generators i).I → (R.over (q.X i)).obj.obj T) k)) = _
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

private theorem integralBasis_naturality {C : Type w} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    [∀ Y : C, HasSheafify (J.over Y) AddCommGrpCat.{u + 1}]
    [∀ Y : C, (J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {M : SheafOfModules.{u + 1} R} (q : M.LocalGeneratorsData)
    [q.IsLocallyFreeData] [q.IsFiniteType] (i : q.I)
    [Fintype (q.generators i).I] [DecidableEq (q.generators i).I]
    {T T' : (Over (q.X i))ᵒᵖ} (g : T ⟶ T') (j : (q.generators i).I) :
    Module.Basis.ofEquivFun (integralCoordinates q i T') j =
      M.val.map ((Over.forget (q.X i)).op.map g)
        (Module.Basis.ofEquivFun (integralCoordinates q i T) j) := by
  have h := PresheafOfModules.naturality_apply
    (SheafOfModules.ιFree (R := R.over (q.X i)) j).val g
    (1 : (R.over (q.X i)).obj.obj T)
  have hone : (SheafOfModules.unit (R.over (q.X i))).val.map g
      (1 : (R.over (q.X i)).obj.obj T) =
      (1 : (R.over (q.X i)).obj.obj T') :=
    ((R.over (q.X i)).obj.map g).hom.map_one
  have hι := (congrArg ((SheafOfModules.ιFree (R := R.over (q.X i)) j).val.app T')
    hone.symm).trans h
  have hπ := PresheafOfModules.naturality_apply (q.generators i).π.val g
    ((SheafOfModules.ιFree (R := R.over (q.X i)) j).val.app T
      (1 : (R.over (q.X i)).obj.obj T))
  exact (integralBasis_eq q i T' j).trans
    ((congrArg ((q.generators i).π.val.app T') hι).trans
      (hπ.trans (congrArg (M.val.map ((Over.forget (q.X i)).op.map g))
        (integralBasis_eq q i T j).symm)))

private noncomputable def tensorUnit {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}} (α : R ⟶ S)
    (V : X.ProEt)
    (M : SheafOfModules.{u + 1} ((sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over V))) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over V)).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (latticeScalarMap α V) M)

private noncomputable def pairVector {X : Scheme.{u}} {K : Type u} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    {L : SheafOfModules.{u + 1} (latticeModuleRing X K)} {V : X.ProEt}
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L V) (T : (Over V)ᵒᵖ) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1, u + 1}
    ((latticeScalarMap (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      V).hom.app T).hom
    ((tensorUnit (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      V P.module).app T ≫ P.rationalization.hom.val.app T)

private theorem frameCoordinates_naturality (X : Scheme.{u}) (K : Type u) [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K] (U : X.ProEt) (n : ℕ)
    {T T' : (Over U)ᵒᵖ} (g : T ⟶ T')
    (m : (latticeFreeSheaf X K U n).val.obj T) (i : Fin n) :
    frameCoordinates X K U n T' ((latticeFreeSheaf X K U n).val.map g m) i =
      (latticeCoefficientSheaf X K).obj.map ((Over.forget U).op.map g)
        (frameCoordinates X K U n T m i) :=
  PresheafOfModules.naturality_apply (SheafOfModules.freeπ
    (R := (latticeModuleRing X K).over U) (ULift.up i)).val g m

private theorem frameCoordinates_symm (X : Scheme.{u}) (K : Type u) [CommRing K]
    [TopologicalSpace K] [IsTopologicalRing K] (U : X.ProEt) (n : ℕ)
    (T : (Over U)ᵒᵖ)
    (c : Fin n → (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)) :
    (frameCoordinates X K U n T).symm c =
      ∑ j, c j • (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
        (ULift.up j : ULift.{u + 1} (Fin n))).val.app T
          (1 : (latticeModuleRing X K).obj.obj (op T.unop.left)) := by
  change (∑ j : ULift.{u + 1} (Fin n),
    (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U) j).val.app T
      (c j.down)) = _
  rw [← Equiv.sum_comp Equiv.ulift.symm]
  apply Finset.sum_congr rfl
  intro j _
  have h := ((SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
    (ULift.up j : ULift.{u + 1} (Fin n))).val.app T).hom.map_smul (c j)
    (1 : (latticeModuleRing X K).obj.obj (op T.unop.left))
  change (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
    (ULift.up j : ULift.{u + 1} (Fin n))).val.app T (c j) = _
  simpa only [smul_eq_mul, mul_one] using h

private noncomputable def basisMatrix {R : Type*} [CommRing R] {n : ℕ}
    (B : Module.Basis (Fin n) R (Fin n → R)) : Matrix.GeneralLinearGroup (Fin n) R :=
  Matrix.GeneralLinearGroup.toLin.symm
    (LinearMap.GeneralLinearGroup.ofLinearEquiv B.equivFun.symm)

private theorem basisMatrix_apply {R : Type*} [CommRing R] {n : ℕ}
    (B : Module.Basis (Fin n) R (Fin n → R)) (i j : Fin n) :
    (basisMatrix B).val i j = B j i := by
  change B.equivFun.symm (Pi.single j 1) i = _
  simp only [Module.Basis.equivFun_symm_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [hk]
  · simp

private theorem pairVector_naturality {X : Scheme.{u}} {K : Type u} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    {L : SheafOfModules.{u + 1} (latticeModuleRing X K)} {V : X.ProEt}
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L V) {T T' : (Over V)ᵒᵖ} (g : T ⟶ T') (m : P.module.val.obj T) :
    pairVector A P T' (P.module.val.map g m) =
      (L.over V).val.map g (pairVector A P T m) := by
  let α := latticeCoefficientSheafMap X A.subtype continuous_subtype_val
  let η := tensorUnit α V P.module
  have hn := PresheafOfModules.naturality_apply η g
    ((1 : (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)) ⊗ₜ[
      (latticeCoefficientSheaf X A).obj.obj (op T.unop.left),
      ((latticeScalarMap α V).hom.app T).hom] m)
  have ht := Classical.choose_spec
    (SheafOfModules.exists_changeOfRingsMap (latticeScalarMap α V) P.module g)
    (1 : (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)) m
  change (η.app T') (SheafOfModules.changeOfRingsMap
    (latticeScalarMap α V) P.module g _) = _ at hn
  change SheafOfModules.changeOfRingsMap (latticeScalarMap α V) P.module g
    ((1 : (latticeCoefficientSheaf X K).obj.obj (op T.unop.left)) ⊗ₜ[
      (latticeCoefficientSheaf X A).obj.obj (op T.unop.left),
      ((latticeScalarMap α V).hom.app T).hom] m) = _ at ht
  rw [ht, map_one] at hn
  change P.rationalization.hom.val.app T' (η.app T' _) = _
  rw [hn]
  exact PresheafOfModules.naturality_apply P.rationalization.hom.val g _

/-- A specified finite local integral basis determines an invertible matrix in a
rational frame, with its embedded-image formula after arbitrary restriction.
Source: Bhatt--Scholze, Proposition 6.8.4(6), local integral bases
(auxiliary; not a blueprint node).
Proof: on the specified finite free neighborhood, the tensor sheafification unit
is an isomorphism. Transport the integral section basis through scalar extension,
P's rationalization and the rational frame. When W is nonempty, evaluation at a point
makes the continuous-section ring nontrivial, so invariant basis number reindexes
this rational basis by Fin n. Its coordinate equivalence gives an invertible matrix.
Naturality identifies its restricted columns with the rationalized integral basis.
Expanding every integral section in this basis proves the matrix-span formula in both
directions. When W is empty, all further test objects are empty; their coefficient
rings and free section modules are singletons, and both images are nonempty.
Rank zero is included by the same finite-basis and finite-sum arguments. -/
theorem integralLatticePair_matrixAtBasis (X : Scheme.{u})
    (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    (L : SheafOfModules.{u + 1} (latticeModuleRing X K))
    (U : X.ProEt) (n : ℕ) (e : L.over U ≅ latticeFreeSheaf X K U n)
    (V : X.ProEt) (f : V ⟶ U)
    (P : IntegralLatticePair (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
      L V)
    (q : P.module.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) (W : X.ProEt) (a : W ⟶ V) (t : Over.mk a ⟶ q.X i) :
    ∃ G : Matrix.GeneralLinearGroup (Fin n)
        ((latticeCoefficientSheaf X K).obj.obj (op W)),
      ∀ T : Over W,
        Set.image (e.hom.val.app (op (Over.mk (T.hom ≫ a ≫ f))))
          (P.image (op (Over.mk (T.hom ≫ a)))) =
        sectionMatrixLatticeImage X K A U n (op (Over.mk (T.hom ≫ a ≫ f)))
          (Matrix.GeneralLinearGroup.map
            (((latticeCoefficientSheaf X K).obj.map T.hom.op).hom) G) := by
  classical
  have hs₀ : HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1} := inferInstance
  have hs₁ : ∀ Y : X.ProEt, HasSheafify ((Scheme.ProEt.topology X).over Y)
      AddCommGrpCat.{u + 1} := fun Y ↦ inferInstance
  have hs₂ : ∀ Y : Over V, HasSheafify (((Scheme.ProEt.topology X).over V).over Y)
      AddCommGrpCat.{u + 1} := fun Y ↦ inferInstance
  have hw₁ : ∀ Y : X.ProEt, ((Scheme.ProEt.topology X).over Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := fun Y ↦ inferInstance
  have hw₂ : ∀ Y : Over V, (((Scheme.ProEt.topology X).over V).over Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := fun Y ↦ inferInstance
  have : (q.generators i).IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType i
  let : Fintype (q.generators i).I := Fintype.ofFinite (q.generators i).I
  let φ := ((latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
    (op W)).hom
  by_cases hW : Nonempty W.left
  · let : Nontrivial ((latticeCoefficientSheaf X K).obj.obj (op W)) := by
      obtain ⟨x⟩ := hW
      exact ⟨⟨0, 1, fun h ↦ zero_ne_one (congrArg (fun z ↦ z.down x) h)⟩⟩
    let : Algebra ((latticeCoefficientSheaf X A).obj.obj (op W))
        ((latticeCoefficientSheaf X K).obj.obj (op W)) := φ.toAlgebra
    let B : Module.Basis (q.generators i).I
        ((latticeCoefficientSheaf X A).obj.obj (op W))
        (P.module.val.obj (op (Over.mk a))) :=
      Module.Basis.ofEquivFun (integralCoordinates q i (op (Over.mk t)))
    have hη := localFreeTensorUnit_isIso
      (latticeCoefficientSheafMap X A.subtype continuous_subtype_val) V P.module q i W a t
    have : IsIso ((tensorUnit
        (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
        V P.module).app (op (Over.mk a))) := hη
    let Fη : (ModuleCat.extendScalars φ).obj (P.module.val.obj (op (Over.mk a))) ≃ₗ[
        (latticeCoefficientSheaf X K).obj.obj (op W)]
        (SheafOfModules.changeOfRings
          (latticeScalarMap (latticeCoefficientSheafMap X A.subtype
            continuous_subtype_val) V) P.module).val.obj (op (Over.mk a)) :=
      (asIso ((tensorUnit
        (latticeCoefficientSheafMap X A.subtype continuous_subtype_val)
        V P.module).app (op (Over.mk a)))).toLinearEquiv
    let Fr : (SheafOfModules.changeOfRings
        (latticeScalarMap (latticeCoefficientSheafMap X A.subtype
          continuous_subtype_val) V) P.module).val.obj (op (Over.mk a)) ≃ₗ[
        (latticeCoefficientSheaf X K).obj.obj (op W)]
        (L.over V).val.obj (op (Over.mk a)) :=
      ((SheafOfModules.evaluation ((latticeModuleRing X K).over V)
        (op (Over.mk a))).mapIso P.rationalization).toLinearEquiv
    let F := Fη.trans Fr
    let E : (L.over V).val.obj (op (Over.mk a)) ≃ₗ[
        (latticeCoefficientSheaf X K).obj.obj (op W)]
        (latticeFreeSheaf X K U n).val.obj (op (Over.mk (a ≫ f))) :=
      ((SheafOfModules.evaluation ((latticeModuleRing X K).over U)
      (op (Over.mk (a ≫ f)))).mapIso e).toLinearEquiv
    let cW : (latticeFreeSheaf X K U n).val.obj (op (Over.mk (a ≫ f))) ≃ₗ[
        (latticeCoefficientSheaf X K).obj.obj (op W)]
        (Fin n → (latticeCoefficientSheaf X K).obj.obj (op W)) :=
      frameCoordinates X K U n (op (Over.mk (a ≫ f)))
    let C : Module.Basis (q.generators i).I
        ((latticeCoefficientSheaf X K).obj.obj (op W))
        (Fin n → (latticeCoefficientSheaf X K).obj.obj (op W)) :=
      ((B.baseChange ((latticeCoefficientSheaf X K).obj.obj (op W))).map F).map
      (E.trans cW)
    let d := C.indexEquiv (Pi.basisFun
      ((latticeCoefficientSheaf X K).obj.obj (op W)) (Fin n))
    let G := basisMatrix (C.reindex d)
    refine ⟨G, ?_⟩
    intro T
    let Z := op (Over.mk (T.hom ≫ a ≫ f))
    let BT : Module.Basis (q.generators i).I
        ((latticeCoefficientSheaf X A).obj.obj (op T.left))
        (P.module.val.obj (op (Over.mk (T.hom ≫ a)))) :=
      Module.Basis.ofEquivFun
        (integralCoordinates q i (op (basisTestObject q i W a t T)))
    let k : basisTestObject q i W a t T ⟶ Over.mk t :=
      Over.homMk (show Over.mk (T.hom ≫ a) ⟶ Over.mk a from Over.homMk T.hom)
        (by ext; rfl)
    have hBT (j : (q.generators i).I) :
        BT j = P.module.val.map
          (show op (Over.mk a) ⟶ op (Over.mk (T.hom ≫ a)) from
            (Over.homMk T.hom).op) (B j) :=
      integralBasis_naturality q i k.op j
    have hC (j : (q.generators i).I) :
        C j = cW (E (pairVector A P (op (Over.mk a)) (B j))) := by
      simp only [C, Module.Basis.map_apply, Module.Basis.baseChange_apply]
      rfl
    have hG (j k : Fin n) : G.val k j = C (d.symm j) k :=
      (basisMatrix_apply (C.reindex d) k j).trans
        (congrArg (fun v ↦ v k) (Module.Basis.reindex_apply C d j))
    have hcolumn (j : Fin n) :
        e.hom.val.app Z (pairVector A P (op (Over.mk (T.hom ≫ a))) (BT (d.symm j))) =
          (frameCoordinates X K U n Z).symm
            (fun k ↦ (latticeCoefficientSheaf X K).obj.map T.hom.op (G.val k j)) := by
      have hc : frameCoordinates X K U n Z
          (e.hom.val.app Z
            (pairVector A P (op (Over.mk (T.hom ≫ a))) (BT (d.symm j)))) =
          (fun k ↦ (latticeCoefficientSheaf X K).obj.map T.hom.op (G.val k j)) := by
        funext l
        let g : op (Over.mk a) ⟶ op (Over.mk (T.hom ≫ a)) :=
          (Over.homMk T.hom).op
        let gu : op (Over.mk (a ≫ f)) ⟶ Z := (Over.homMk T.hom).op
        have hp := pairVector_naturality A P g (B (d.symm j))
        have he := PresheafOfModules.naturality_apply e.hom.val gu
          (pairVector A P (op (Over.mk a)) (B (d.symm j)))
        have hn := frameCoordinates_naturality X K U n gu
          (e.hom.val.app (op (Over.mk (a ≫ f)))
            (pairVector A P (op (Over.mk a)) (B (d.symm j)))) l
        have hv : cW (E (pairVector A P (op (Over.mk a)) (B (d.symm j)))) l =
            G.val l j := (congrFun (hC (d.symm j)).symm l).trans (hG j l).symm
        exact (congrArg (fun m ↦ frameCoordinates X K U n Z
          (e.hom.val.app Z (pairVector A P (op (Over.mk (T.hom ≫ a))) m)) l)
            (hBT (d.symm j))).trans
          ((congrArg (fun x ↦ frameCoordinates X K U n Z (e.hom.val.app Z x) l)
            hp).trans ((congrArg (fun y ↦ frameCoordinates X K U n Z y l) he).trans
              (hn.trans (congrArg ((latticeCoefficientSheaf X K).obj.map T.hom.op) hv))))
      exact (frameCoordinates X K U n Z).injective
        (hc.trans ((frameCoordinates X K U n Z).apply_symm_apply _).symm)
    have hsum (b : Fin n → (latticeCoefficientSheaf X A).obj.obj (op T.left)) :
        e.hom.val.app Z (pairVector A P (op (Over.mk (T.hom ≫ a)))
          (∑ j, b j • BT (d.symm j))) =
        ∑ k : Fin n,
          (∑ j : Fin n, ((latticeCoefficientSheaf X K).obj.map T.hom.op (G.val k j)) *
            (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
              (op T.left) (b j)) •
          (SheafOfModules.ιFree (R := (latticeModuleRing X K).over U)
            (ULift.up k : ULift.{u + 1} (Fin n))).val.app Z
              (1 : (latticeCoefficientSheaf X K).obj.obj (op T.left)) := by
      have hsm (r : (latticeCoefficientSheaf X A).obj.obj (op T.left))
          (m : P.module.val.obj (op (Over.mk (T.hom ≫ a)))) :
          pairVector A P (op (Over.mk (T.hom ≫ a))) (r • m) =
            (latticeCoefficientSheafMap X A.subtype continuous_subtype_val).hom.app
              (op T.left) r • pairVector A P (op (Over.mk (T.hom ≫ a))) m :=
        (pairVector A P (op (Over.mk (T.hom ≫ a)))).hom.map_smul r m
      rw [map_sum, map_sum]
      simp_rw [hsm, map_smul, hcolumn, frameCoordinates_symm,
        Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.sum_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact mul_comm _ _
    change Set.image (e.hom.val.app Z)
      (Set.range (fun m ↦ pairVector A P (op (Over.mk (T.hom ≫ a))) m)) = _
    apply Set.ext
    intro y
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      refine ⟨fun j ↦ BT.repr m (d.symm j), ?_⟩
      change _ = e.hom.val.app Z (pairVector A P (op (Over.mk (T.hom ≫ a))) m)
      have hB : (∑ j, BT.repr m (d.symm j) • BT (d.symm j)) = m := by
        exact (d.symm.sum_comp (fun j ↦ BT.repr m j • BT j)).trans (BT.sum_repr m)
      exact (hsum (fun j ↦ BT.repr m (d.symm j))).symm.trans
        (congrArg (fun z ↦ e.hom.val.app Z
          (pairVector A P (op (Over.mk (T.hom ≫ a))) z)) hB)
    · rintro ⟨b, hb⟩
      refine ⟨pairVector A P (op (Over.mk (T.hom ≫ a)))
        (∑ j, b j • BT (d.symm j)), ⟨_, rfl⟩, ?_⟩
      exact (hsum b).trans hb
  · refine ⟨1, ?_⟩
    intro T
    have hT : IsEmpty T.left.left :=
      ⟨fun x ↦ hW ⟨T.hom.left.base x⟩⟩
    let : Subsingleton ((latticeCoefficientSheaf X K).obj.obj (op T.left)) :=
      ⟨fun x y ↦ ULift.ext (ContinuousMap.ext (fun z ↦ (hT.false z).elim))⟩
    let : Subsingleton ((latticeFreeSheaf X K U n).val.obj
        (op (Over.mk (T.hom ≫ a ≫ f)))) :=
      ⟨fun x y ↦ (frameCoordinates X K U n
        (op (Over.mk (T.hom ≫ a ≫ f)))).injective (funext fun j ↦
          @Subsingleton.elim ((latticeCoefficientSheaf X K).obj.obj (op T.left))
            inferInstance _ _)⟩
    apply Set.ext
    intro y
    constructor
    · intro _
      exact ⟨fun _ ↦ 0, Subsingleton.elim _ _⟩
    · intro _
      exact ⟨pairVector A P (op (Over.mk (T.hom ≫ a))) 0, ⟨0, rfl⟩,
        Subsingleton.elim _ _⟩

end AlgebraicGeometry.ProEtale
