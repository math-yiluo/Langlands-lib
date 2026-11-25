/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor

/-!
# Algebra compatibility of the structure-sheaf base change map

Source: Stacks Project, Cohomology, Remark 08HY; Sheaves, Tags 0093, 0095, 0096;
Modules, Tag 01CD. The algebra compatibility is the explicit argument in the node,
not a separately stated Stacks lemma
(blueprint: lem-weil-pbc-module-base-change-map-algebra).
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChangeUnit_adjoint
    {X S X' S' : Scheme.{v}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) :
    (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
        ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ≫
        (pushforward g).map
          (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
            (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
      (pushforward f).map (SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom) ≫
        (pushforwardComp g' f).hom.app (SheafOfModules.unit X'.ringCatSheaf) ≫
        (pushforwardCongr h).hom.app (SheafOfModules.unit X'.ringCatSheaf) ≫
        (pushforwardComp f' g).inv.app (SheafOfModules.unit X'.ringCatSheaf) := by
  rw [← (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv_unit _ _
    (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
      (pushforward f').map (tensorPullbackObjUnitToUnit g')),
    Adjunction.homEquiv_naturality_right]
  unfold moduleBaseChangeMap
  rw [Equiv.apply_symm_apply]
  simp only [Category.assoc]
  rw [← Functor.comp_map]
  rw [← (pushforwardComp f' g).inv.naturality (tensorPullbackObjUnitToUnit g')]
  rw [← (pushforwardCongr h).hom.naturality_assoc (tensorPullbackObjUnitToUnit g')]
  rw [← (pushforwardComp g' f).hom.naturality_assoc (tensorPullbackObjUnitToUnit g')]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc, (tensorPullbackObjUnitToUnit_isIso g').2]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_pushforwardUnitMul {X S : Scheme.{v}} (f : X ⟶ S) :
    ∃ mu : (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⊗
        (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf),
      ∀ (W : S.Opens) (a b : Γ(X, f ⁻¹ᵁ W)), mu.app W (tmulSection a b) = a * b := by
  let A := (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)
  let p : A.val ⊗ A.val ⟶ A.val :=
    { app := fun W ↦ ModuleCat.MonoidalCategory.tensorLift
        (fun (a b : Γ(X, f ⁻¹ᵁ unop W)) ↦ a * b)
        (by intro a b c; exact add_mul (R := Γ(X, f ⁻¹ᵁ unop W)) a b c)
        (by
          intro r a b
          exact mul_assoc (f.app (unop W) r)
            (show Γ(X, f ⁻¹ᵁ unop W) from a) (show Γ(X, f ⁻¹ᵁ unop W) from b))
        (by intro a b c; exact mul_add (R := Γ(X, f ⁻¹ᵁ unop W)) a b c)
        (by
          intro r a b
          exact mul_left_comm (show Γ(X, f ⁻¹ᵁ unop W) from a)
            (f.app (unop W) r) (show Γ(X, f ⁻¹ᵁ unop W) from b))
      naturality := by
        intro U V i
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro a b
        dsimp [A] at a b ⊢
        exact ((X.presheaf.map ((TopologicalSpace.Opens.map f.base).op.map i)).hom.map_mul
          a b).symm }
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 S.ringCatSheaf.obj)
  let q : sheafifyTensor A A ⟶ A := (adj.homEquiv _ A).symm p
  refine ⟨(SheafOfModules.tensorObjIsoSheafification A A).hom ≫ q, ?_⟩
  intro W a b
  have hq := (adj.homEquiv _ A).apply_symm_apply p
  have he : q.app W ((toSheafifyTensor A A).app (op W) (a ⊗ₜ b)) = a * b :=
    congrArg (fun t ↦ t.app (op W) (a ⊗ₜ b)) hq
  change q.app W (Hom.app (SheafOfModules.tensorObjIsoSheafification A A).hom W
    (Hom.app (SheafOfModules.tensorObjIsoSheafification A A).inv W
      ((toSheafifyTensor A A).app (op W) (a ⊗ₜ b)))) = a * b
  exact (congrArg (q.app W)
    (inv_app_hom_app_apply_of_iso (SheafOfModules.tensorObjIsoSheafification A A).symm
      ((toSheafifyTensor A A).app (op W) (a ⊗ₜ b)))).trans he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChangeUnit_unit
    {X S X' S' : Scheme.{v}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) :
    (tensorPullback g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
      tensorPullbackObjUnitToUnit g ≫
        SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom := by
  apply (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left]
  conv_rhs => rw [Adjunction.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit]
  erw [baseChangeUnit_adjoint f f' g g' h]
  rw [(tensorPullbackObjUnitToUnit_isIso g).2]
  apply hom_ext
  intro W
  ext a
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app]
  change X'.presheaf.map (eqToHom (congrArg (fun k : X' ⟶ S ↦ k ⁻¹ᵁ W) h.symm)).op
    (g'.app (f ⁻¹ᵁ W) (f.app W a)) = f'.app (g ⁻¹ᵁ W) (g.app W a)
  have hh := Scheme.Hom.congr_app h.symm W
  rw [Scheme.Hom.comp_app, Scheme.Hom.comp_app] at hh
  exact (ConcreteCategory.congr_hom hh a).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensor_hom_ext {S : Scheme.{v}} {M N P : S.Modules}
    (a b : M ⊗ N ⟶ P)
    (h : ∀ (W : S.Opens) (s : Γ(M, W)) (t : Γ(N, W)),
      a.app W (tmulSection s t) = b.app W (tmulSection s t)) : a = b := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (PresheafOfModules.sheafificationAdjunction (𝟙 S.ringCatSheaf.obj)).homEquiv _ P
    |>.injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact h (unop W) s t

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The adjunction and tensor comparisons require elaborating several sheafification types.
/-- The canonical base change map on structure sheaves has adjoint `f_*(g'^sharp)`
and preserves multiplication and units. The multiplications are characterized on pure
section tensors, so they are the actual ring multiplications, not arbitrary algebra data.

Source: Stacks Project, Cohomology, Remark 08HY; Sheaves, Tags 0093, 0095, 0096;
Modules, Tag 01CD; algebra compatibility is explicit
(blueprint: lem-weil-pbc-module-base-change-map-algebra).
Proof:
(1) Use the Hom bijection of def-pc-module-pullback and its natural unit. Identify
`f_* g'_*` with `g_* f'_*` through the pushforward composition and square comparisons;
0093 identifies the module actions.
(2) By lem-weil-pbc-module-pullback-structure-sheaf, the adjoint of epsilon is sharp.
Functoriality and the defining adjoint of beta therefore give the displayed adjoint of gamma;
on sections this is exactly gamma(eta(a)) = g'^sharp(a).
(3) Multiplication on the pushforward is induced by sectionwise ring multiplication,
using def-pur-sheaf-tensor-product and def-weil-presheaf-modules-sheafification.
Compare the adjoints of the two multiplication composites. Uniqueness of sheafification
reduces equality to pure tensors. Naturality of eta gives g'^sharp(ab) on the first side;
lem-weil-pbc-module-pullback-tensor gives g'^sharp(a) g'^sharp(b) on the second.
These agree because g'^sharp is a ring homomorphism (def-pc-scheme).
(4) Compare adjoints of the unit composites. Naturality and step (2) give
(f composed with g')^sharp; the epsilon characterization gives (g composed with f')^sharp.
They agree by the square and 0093. Thus gamma is an O_S'-algebra morphism. -/
theorem moduleBaseChangeMap_algebra
    {X S X' S' : Scheme.{v}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) :
    ∃ (mu : (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⊗
          (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
        (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
      (mu' : (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf) ⊗
          (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf) ⟶
        (pushforward f').obj (SheafOfModules.unit X'.ringCatSheaf)),
      (∀ (W : S.Opens) (a b : Γ(X, f ⁻¹ᵁ W)), mu.app W (tmulSection a b) = a * b) ∧
      (∀ (W : S'.Opens) (a b : Γ(X', f' ⁻¹ᵁ W)), mu'.app W (tmulSection a b) = a * b) ∧
      (Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) ≫
          (pushforward g).map
            (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
        (pushforward f).map (SheafOfModules.unitToPushforwardObjUnit g'.toRingCatSheafHom) ≫
          (pushforwardComp g' f).hom.app (SheafOfModules.unit X'.ringCatSheaf) ≫
          (pushforwardCongr h).hom.app (SheafOfModules.unit X'.ringCatSheaf) ≫
          (pushforwardComp f' g).inv.app (SheafOfModules.unit X'.ringCatSheaf) ∧
      (tensorPullback g).map mu ≫
          (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
        (Classical.choose (module_pullback_tensor g)
            ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
            ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).hom ≫
          ((moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) ⊗ₘ
            (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g'))) ≫ mu' ∧
      (tensorPullback g).map (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
          (pushforward f').map (tensorPullbackObjUnitToUnit g')) =
        tensorPullbackObjUnitToUnit g ≫
          SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom := by
  obtain ⟨mu, hmu⟩ := exists_pushforwardUnitMul f
  obtain ⟨mu', hmu'⟩ := exists_pushforwardUnitMul f'
  refine ⟨mu, mu', hmu, hmu', baseChangeUnit_adjoint f f' g g' h, ?_,
    baseChangeUnit_unit f f' g g' h⟩
  apply (Classical.choose (exists_tensorPullbackAdjunction g)).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left]
  simp only [Adjunction.homEquiv_unit]
  erw [baseChangeUnit_adjoint f f' g g' h]
  apply tensor_hom_ext
  intro W a b
  change Γ(X, f ⁻¹ᵁ W) at a b
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app]
  have ht := (Classical.choose_spec (module_pullback_tensor g)).2
    ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
    ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) W a b
  erw [ht]
  let gamma := moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
    (pushforward f').map (tensorPullbackObjUnitToUnit g')
  have hh := tensorHom_app_tmulSection (X := S') gamma gamma
    (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
      ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).val.app (op W) a)
    (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
      ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).val.app (op W) b)
  erw [hh]
  erw [hmu' (g ⁻¹ᵁ W), hmu W a b]
  have heval (c : Γ(X, f ⁻¹ᵁ W)) :
      (moduleBaseChangeMap f f' g g' h (SheafOfModules.unit X.ringCatSheaf) ≫
        (pushforward f').map (tensorPullbackObjUnitToUnit g')).app (g ⁻¹ᵁ W)
          (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
            ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).val.app (op W) c) =
      X'.presheaf.map (eqToHom
        (congrArg (fun k : X' ⟶ S ↦ k ⁻¹ᵁ W) h.symm)).op (g'.app (f ⁻¹ᵁ W) c) := by
    have he := congrArg (fun t ↦ t.app W c) (baseChangeUnit_adjoint f f' g g' h)
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
      pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
      pushforwardCongr_hom_app_app] at he
    exact he
  erw [heval a, heval b]
  simp only [pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app]
  change X'.presheaf.map (eqToHom
    (congrArg (fun k : X' ⟶ S ↦ k ⁻¹ᵁ W) h.symm)).op
      (g'.app (f ⁻¹ᵁ W) (a * b)) = _
  rw [(g'.app (f ⁻¹ᵁ W)).hom.map_mul,
    (X'.presheaf.map (eqToHom
      (congrArg (fun k : X' ⟶ S ↦ k ⁻¹ᵁ W) h.symm)).op).hom.map_mul]

end
end AlgebraicGeometry.Scheme.Modules
