/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedCoefficientSheafAction
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Projection of homogeneous quotient actions

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, the quotient action on a square-zero ideal.
(blueprint: lem-sc-square-zero-tensor-graded-action-projection-first).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
noncomputable section

private theorem edge_naturality {X Z : Scheme.{u}} (j : Z ⟶ X)
    {A B : Z.Modules} (v : A ⟶ B) :
    (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map ((pushforward j).map v)) ≫
      moduleCohomologyEdgeMap j B 1 =
    moduleCohomologyEdgeMap j A 1 ≫ (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.moduleCohomology Z.toRingedSpace 1).map v) := by
  have hs := moduleCohomologyFMap_source_naturality j ((pushforward j).map v) (𝟙 _) 1
  have ht := moduleCohomologyFMap_target_naturality j v (𝟙 _) 1
  simpa only [moduleCohomologyEdgeMap, Category.comp_id, Category.id_comp] using
    hs.trans ht.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_comparison_via_sheaf {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n e : ℕ) :
    moduleCohomologyEdgeMap j
        (show Z.Modules from
          (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
            (((tensorPullback j).obj L).tensorPow n).tensorPow e) 1 ≫
      (boundaryCoefficientCohomologyIso j L hI n e).hom =
    (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).map
        (tensorCoefficientSheafIso j L hI n e).hom) := by
  let A := j.ker.toModules ⊗ L.tensorPow (n * (e + 1))
  have := SheafOfModules.isQuasicoherent_unit (R := j.ker.subscheme.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      ((SheafOfModules.pushforward j.ker.subschemeι.toRingCatSheafHom).obj
        (SheafOfModules.unit j.ker.subscheme.ringCatSheaf)) :=
    isQuasicoherent_pushforward_of_isClosedImmersion j.ker.subschemeι _
  have : j.ker.toModules.IsQuasicoherent :=
    isQuasicoherent_kernel j.ker.toPushforwardSubscheme
  have : A.IsQuasicoherent := isQuasicoherent_tensorObj _ _
  have : ((tensorPullback j).obj A).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso
      ((boundaryPullbackComparison j).app A).symm
      (inferInstance : ((pullback j).obj A).IsQuasicoherent)
  have := square_zero_ideal_tensor_unit_isIso j L hI (n * (e + 1))
  have := ((affine_morphism_cohomology_edge j ((tensorPullback j).obj A)).2 1).1
  have hn := edge_naturality j (boundaryCoefficientDegreeIso j L n e).inv
  simp only [boundaryCoefficientCohomologyIso, tensorCoefficientSheafIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Functor.comp_map]
  let E := moduleCohomologyEdgeMap j ((tensorPullback j).obj A) 1
  let U := (forget₂ _ AddCommGrpCat.{u}).map
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).map
      (asIso ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app A)).inv)
  let K := (forget₂ _ AddCommGrpCat.{u}).map
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).map
      (boundaryIdealKernelIso j (L.tensorPow (n * (e + 1)))).hom)
  have hh := congrArg (fun q ↦ q ≫ (asIso E).inv ≫ U ≫ K) hn.symm
  simpa only [E, U, K, A, Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc] using hh

private theorem comparison_square_cancel
    {A B C D E F : AddCommGrpCat.{u}} (s : A ≅ C) (t : B ≅ D)
    (k : E ≅ C) (l : F ≅ D) (ea : A ⟶ E) (eb : B ⟶ F)
    (v : A ⟶ B) (w : E ⟶ F) (q : C ⟶ D)
    (ha : ea ≫ k.hom = s.hom) (hb : eb ≫ l.hom = t.hom)
    (hn : v ≫ eb = ea ≫ w) (hm : s.hom ≫ q = v ≫ t.hom) :
    k.hom ≫ q = w ≫ l.hom := by
  have he : ea = s.hom ≫ k.inv := by
    rw [← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsIso ea := by rw [he]; infer_instance
  rw [← cancel_epi ea, ← Category.assoc, ha, hm]
  rw [← hb, ← Category.assoc, hn, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_comparison_naturality {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n a b : ℕ)
    (v : (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow a ⟶
      (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow b) :
    (boundaryCoefficientCohomologyIso j L hI n a).hom ≫
        (forget₂ _ AddCommGrpCat.{u}).map
          ((RingedSpace.moduleCohomology X.toRingedSpace 1).map
            (tensorCoefficientKernelMap j L hI n a b v)) =
      (forget₂ _ AddCommGrpCat.{u}).map
        ((RingedSpace.moduleCohomology Z.toRingedSpace 1).map v) ≫
          (boundaryCoefficientCohomologyIso j L hI n b).hom := by
  let HX := RingedSpace.moduleCohomology X.toRingedSpace 1 ⋙
    forget₂ _ AddCommGrpCat.{u}
  let s := tensorCoefficientSheafIso j L hI n a
  let t := tensorCoefficientSheafIso j L hI n b
  have hs : s.hom ≫ tensorCoefficientKernelMap j L hI n a b v =
      (pushforward j).map v ≫ t.hom := by
    simp only [s, t, tensorCoefficientKernelMap, Iso.hom_inv_id_assoc]
  have hm := congrArg (fun q ↦ HX.map q) hs
  simp only [Functor.map_comp] at hm
  exact comparison_square_cancel
    (HX.mapIso s) (HX.mapIso t)
    (boundaryCoefficientCohomologyIso j L hI n a)
    (boundaryCoefficientCohomologyIso j L hI n b)
    _ _ _ _ _ (coefficient_comparison_via_sheaf j L hI n a)
    (coefficient_comparison_via_sheaf j L hI n b) (edge_naturality j v) hm

private theorem transport_action
    {V A B C D : Type u} [AddCommGroup V] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D] (k : C ≃+ A) (l : D ≃+ B)
    (a : V →+ V) (p : V →+ A) (q : V →+ B) (m : A →+ B) (v : C →+ D)
    (hm : ∀ z, q (a z) = m (p z)) (hn : ∀ y, m (k y) = l (v y)) (z : V) :
    l.symm (q (a z)) = v (k.symm (p z)) := by
  apply l.injective
  rw [l.apply_symm_apply, hm, ← hn, k.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The unchanged interface retains the unused section x and let-bound coefficient N.
set_option linter.unusedVariables false in
/-- Compatibility of the degree-n section obtained from tensorPowSection f 1
on the degree-n(e+1) coefficient.

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, quotient multiplication on the square-zero ideal;
Tag 01XC, naturality of the affine cohomology comparison.
(blueprint: lem-sc-square-zero-tensor-graded-action-projection-first).
Proof: The inclusion i is mono by short exactness, so hlocal uniquely determines the
quotient action. Lift the homogeneous quotient section locally through the degreewise
unit. On each kernel summand k_d, use k_inclusion and b_multiply to compute multiplication
by this lift. Project to degree n(e+2); k_projection gives the diagonal term and
k_orthogonal kills every other input degree. The surviving input degree is
n(e+1). If n=0 this is a diagonal calculation in degree zero; no distinct-degree
assumption is needed. The colimit cofan k determines the map from these summands.
Changing a lift by a kernel section changes no product, since the ideal is square zero.
Restriction compatibility glues these local identities, and hglobal identifies the
resulting global action with mu. Apply H^1 and use haction. Transport the resulting
square through the canonical ideal-kernel, annihilated-module unit, affine cohomology,
and tensor-degree comparisons fixed by hD. Naturality identifies the transported map
with mulTensorPowSection f F e 1;
evaluating gives the stated equation.
The identity holds for every class, including the zero class and zero section. -/
theorem tensorGradedAction_projection_first {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (ρ : T.C.right.obj.obj (op ⊤) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I))
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hrestrict : ∀ (U V : X.Opens) (a : V ⟶ U)
      (g : T.C.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      T.I.val.map a.op (σ U g y) = σ V (T.C.right.obj.map a.op g) (T.I.val.map a.op y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).asHom.val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y)
    (haction : ∀ g : T.C.right.obj.obj (op ⊤), ρ g =
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ g).asHom).hom) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    let N : Z.Modules := ((tensorPullback j).obj L).tensorPow n
    let H := RingedSpace.moduleCohomology Z.toRingedSpace 1
    (∀ z : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I,
      tensorGradedCoefficientProjection T D (e + 1)
        (ρ (tensorGradedSection T D 0 (tensorPowSection f 1)) z) =
      H.map (mulTensorPowSection f F e 1) (tensorGradedCoefficientProjection T D e z)) := by
  intro F N H z
  clear N x
  dsimp only [F, H]
  let HX := RingedSpace.moduleCohomology X.toRingedSpace 1
  let HZ := RingedSpace.moduleCohomology Z.toRingedSpace 1
  let v := mulTensorPowSection f
    ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)) e 1
  have hs := tensorGradedCoefficient_sheaf_action j L hI n T D hD e f
    σ μ hlocal hrestrict hglobal
  have hc := coefficient_comparison_naturality j L hI n e (e + 1) v
  have hk : (D.k e).hom ≫ (forget₂ _ AddCommGrpCat.{u}).map
        (HX.map (tensorCoefficientKernelMap j L hI n e (e + 1) v)) =
      (forget₂ _ AddCommGrpCat.{u}).map (HZ.map v) ≫ (D.k (e + 1)).hom := by
    subst D
    simpa only [canonicalTensorBoundaryComparisons, HX, HZ] using hc
  have hm := congrArg (fun q ↦ HX.map q) hs
  simp only [HX.map_comp] at hm
  have ht := transport_action
    (Iso.addCommGroupIsoToAddEquiv (D.k e))
    (Iso.addCommGroupIsoToAddEquiv (D.k (e + 1)))
    (HX.map (μ (tensorGradedSection T D 0 (tensorPowSection f 1))).asHom).hom.toAddMonoidHom
    (HX.map (T.degree (n * (e + 1))).τ₁).hom.toAddMonoidHom
    (HX.map (T.degree (n * ((e + 1) + 1))).τ₁).hom.toAddMonoidHom
    (HX.map (tensorCoefficientKernelMap j L hI n e (e + 1) v)).hom.toAddMonoidHom
    (HZ.map v).hom.toAddMonoidHom
    (fun y ↦ ConcreteCategory.congr_hom hm y)
    (fun y ↦ ConcreteCategory.congr_hom hk y) z
  dsimp only [LinearMap.toAddMonoidHom, AddMonoidHom.coe_mk, AddHom.coe_mk] at ht
  simp only [tensorGradedCoefficientProjection_apply]
  have hr := congrArg
    (fun a : Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I) ↦
      (Iso.addCommGroupIsoToAddEquiv (D.k (e + 1))).symm
        ((HX.map (T.degree (n * ((e + 1) + 1))).τ₁).hom (a z)))
    (haction (tensorGradedSection T D 0 (tensorPowSection f 1)))
  exact hr.trans ht

end
end AlgebraicGeometry.Scheme.Modules
