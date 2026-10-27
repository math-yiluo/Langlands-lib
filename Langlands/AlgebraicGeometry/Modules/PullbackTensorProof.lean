import Langlands.AlgebraicGeometry.Modules.PullbackTensorStatement
import Langlands.AlgebraicGeometry.Modules.PresheafPullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.TensorMonoidal

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
namespace Langlands.Scheme.Modules

private abbrev prePullback {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.pullback.{u} f.toRingCatSheafHom.hom

private abbrev preAdj {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :=
  PresheafOfModules.pullbackPushforwardAdjunction.{u} f.toRingCatSheafHom.hom

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

private def pullbackUnitMate (M : Y.Modules) :
    (prePullback f).obj M.val ⟶ ((Scheme.Modules.pullback f).obj M).val :=
  ((preAdj f).homEquiv _ _).symm
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val

private def sheafifyPullbackIso :
    sheafify Y ⋙ Scheme.Modules.pullback f ≅ prePullback f ⋙ sheafify X :=
  SheafOfModules.sheafificationCompPullback.{u} f.toRingCatSheafHom

private lemma sheafify_tensor_map_isIso {P P' Q Q' : X.PresheafOfModules}
    (a : P ⟶ P') (b : Q ⟶ Q')
    [IsIso ((sheafify X).map a)] [IsIso ((sheafify X).map b)] :
    IsIso ((sheafify X).map (a ⊗ₘ b)) := by
  rw [Functor.Monoidal.map_tensor]
  infer_instance

private lemma sheafify_pullbackUnitMate_isIso (M : Y.Modules) :
    IsIso ((sheafify X).map (pullbackUnitMate f M)) := by
  let e := (SheafOfModules.pullbackIso.{u} f.toRingCatSheafHom).symm.app M
  have h : pullbackUnitMate f M =
      (sheafifyAdjunction X).unit.app ((prePullback f).obj M.val) ≫ e.hom.val := by
    apply ((preAdj f).homEquiv _ _).injective
    rw [pullbackUnitMate, Equiv.apply_symm_apply]
    have he := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (SheafOfModules.PullbackConstruction.adjunction.{u} f.toRingCatSheafHom)
      (Scheme.Modules.pullbackPushforwardAdjunction f) M
    exact congrArg (fun k => k.val) he.symm
  rw [h, Functor.map_comp]
  have : IsIso ((sheafify X).map
      ((sheafifyAdjunction X).unit.app ((prePullback f).obj M.val))) := by
    infer_instance
  have : IsIso e.hom.val :=
    inferInstanceAs (IsIso ((Scheme.Modules.toPresheafOfModules X).map e.hom))
  infer_instance


private lemma homEquiv_sheafifyPullbackIso (P : Y.PresheafOfModules)
    (T : X.Modules) (g : (sheafify X).obj ((prePullback f).obj P) ⟶ T) :
    ((sheafifyAdjunction Y).comp (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv P T
      ((sheafifyPullbackIso f).hom.app P ≫ g) =
    ((preAdj f).comp (sheafifyAdjunction X)).homEquiv P T g := by
  rw [Adjunction.homEquiv_naturality_right]
  have he := Adjunction.homEquiv_leftAdjointUniq_hom_app
    ((sheafifyAdjunction Y).comp (Scheme.Modules.pullbackPushforwardAdjunction f))
    ((preAdj f).comp (sheafifyAdjunction X)) P
  erw [he]
  rfl

private lemma composite_homEquiv_comparison (M N : Y.Modules) :
    ((sheafifyAdjunction Y).comp (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv
      (M.val ⊗ N.val) _ (pullbackTensorComparisonApp f M N) =
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val ⊗ₘ
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val) ≫
      pushforwardTensorPresheafHom f ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) := by
  change tensorHomEquiv _ _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackTensorComparisonApp f M N)) = _
  calc
    _ = tensorHomEquiv M N _
        (tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
          pushforwardTensorApp f ((Scheme.Modules.pullback f).obj M)
            ((Scheme.Modules.pullback f).obj N)) :=
      congrArg (tensorHomEquiv M N _) (homEquiv_pullbackTensorComparisonApp f M N)
    _ = _ := (tensorHomEquiv_tensorMap_comp _ _ _).trans
      (congrArg (fun a =>
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val ⊗ₘ
          ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val) ≫ a)
        (tensorHomEquiv_pushforwardTensorApp f ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N)))

private lemma pullbackUnitMate_adj (M : Y.Modules) :
    (preAdj f).homEquiv _ _ (pullbackUnitMate f M) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val :=
  Equiv.apply_symm_apply _ _

private lemma canonical_comparison_isIso_of_presheaf
    (M N : Y.Modules)
    (d : (prePullback f).obj (M.val ⊗ N.val) ⟶
      (prePullback f).obj M.val ⊗ (prePullback f).obj N.val)
    [IsIso d]
    (hd : ∀ (U : Y.Opensᵒᵖ) (m : M.val.obj U) (n : N.val.obj U),
      (((preAdj f).homEquiv _ _ d).app U).hom (m ⊗ₜ n) =
        TensorProduct.tmul
          (R := X.presheaf.obj ((TopologicalSpace.Opens.map f.base).op.obj U))
          (M := ((prePullback f).obj M.val).obj ((TopologicalSpace.Opens.map f.base).op.obj U))
          (N := ((prePullback f).obj N.val).obj ((TopologicalSpace.Opens.map f.base).op.obj U))
          ((((preAdj f).unit.app M.val).app U).hom m)
          ((((preAdj f).unit.app N.val).app U).hom n)) :
    IsIso (pullbackTensorComparisonApp f M N) := by
  let k := pullbackUnitMate f M ⊗ₘ pullbackUnitMate f N
  let g := (sheafify X).map (d ≫ k)
  have h : pullbackTensorComparisonApp f M N =
      (sheafifyPullbackIso f).hom.app (M.val ⊗ N.val) ≫ g := by
    apply (((sheafifyAdjunction Y).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _).injective
    erw [composite_homEquiv_comparison, homEquiv_sheafifyPullbackIso]
    change _ = (preAdj f).homEquiv _ _ ((sheafifyAdjunction X).homEquiv _ _ g)
    have hsh : (sheafifyAdjunction X).homEquiv _ _ g =
        (d ≫ k) ≫ (sheafifyAdjunction X).unit.app _ :=
      (Adjunction.homEquiv_unit _ _ _ _).trans
        ((sheafifyAdjunction X).unit.naturality (d ≫ k)).symm
    rw [hsh, Category.assoc, Adjunction.homEquiv_naturality_right]
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    have hm := congrArg (fun a => (a.app U).hom m) (pullbackUnitMate_adj f M)
    have hn := congrArg (fun a => (a.app U).hom n) (pullbackUnitMate_adj f N)
    simp only [Adjunction.homEquiv_unit] at hm hn
    simp only [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
    erw [hd U m n]
    exact congrArg₂ (fun a b => (tensorSheafifyUnit _ _).app
      ((TopologicalSpace.Opens.map f.base).op.obj U) (a ⊗ₜ b)) hm.symm hn.symm
  rw [h]
  have : IsIso ((sheafify X).map (pullbackUnitMate f M)) :=
    sheafify_pullbackUnitMate_isIso f M
  have : IsIso ((sheafify X).map (pullbackUnitMate f N)) :=
    sheafify_pullbackUnitMate_isIso f N
  have : IsIso ((sheafify X).map k) := sheafify_tensor_map_isIso _ _
  dsimp only [g]
  rw [Functor.map_comp]
  infer_instance

private lemma pullbackTensorComparisonIsIso_of_presheaf
    (h : ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y),
      IsIso (presheafPullbackTensorComparison f)) :
    pullbackTensorComparisonIsIsoStatement.{u} := by
  intro X Y f
  have : IsIso (presheafPullbackTensorComparison f) := h f
  have (MN : Y.Modules × Y.Modules) :
      IsIso ((pullbackTensorComparison f).app MN) := by
    change IsIso (pullbackTensorComparisonApp f MN.1 MN.2)
    have : IsIso (presheafPullbackTensorComparisonApp f MN.1.val MN.2.val) :=
      inferInstanceAs (IsIso ((presheafPullbackTensorComparison f).app
        (MN.1.val, MN.2.val)))
    apply canonical_comparison_isIso_of_presheaf f MN.1 MN.2
      (presheafPullbackTensorComparisonApp f MN.1.val MN.2.val)
    exact homEquiv_presheafPullbackTensorComparisonApp_app_tmul f MN.1.val MN.2.val
  exact NatIso.isIso_of_isIso_app _

/-- The fixed canonical sheaf pullback tensor comparison is invertible. -/
theorem pullbackTensorComparisonIsIso :
    pullbackTensorComparisonIsIsoStatement.{u} :=
  pullbackTensorComparisonIsIso_of_presheaf presheafPullbackTensorComparisonIsIso

end Langlands.Scheme.Modules
