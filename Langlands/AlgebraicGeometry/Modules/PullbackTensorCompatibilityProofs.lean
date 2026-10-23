import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityStatements
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs

noncomputable section
universe u
open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry
namespace Langlands.Scheme.Modules

local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))
local instance (X : Scheme.{u}) : SymmetricCategory X.PresheafOfModules :=
  inferInstanceAs (SymmetricCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))

set_option backward.isDefEq.respectTransparency false

private lemma adjoint_tensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} {P Q : X.Modules}
    (a : (Scheme.Modules.pullback f).obj M ⟶ P)
    (b : (Scheme.Modules.pullback f).obj N ⟶ Q) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (pullbackTensorComparisonApp f M N ≫ tensorMap a b) =
    tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ a)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ b) ≫
        pushforwardTensorApp f P Q := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_pullbackTensorComparisonApp,
    Category.assoc, ← pushforwardTensorApp_naturality, ← Category.assoc, tensorMap_comp]
  rfl

private lemma pushforward_tensor_identity (X : Scheme.{u}) (M N : X.Modules) :
    tensorMap ((Scheme.Modules.pushforwardId X).inv.app M)
      ((Scheme.Modules.pushforwardId X).inv.app N) ≫ pushforwardTensorApp (𝟙 X) M N =
    (Scheme.Modules.pushforwardId X).inv.app (tensorObj M N) := by
  apply (tensorHomEquiv _ _ _).injective
  rw [tensorHomEquiv_tensorMap_comp, tensorHomEquiv_pushforwardTensorApp]
  refine PresheafOfModules.hom_ext (fun U => ModuleCat.MonoidalCategory.tensor_ext (fun m n => ?_))
  rfl

lemma pullbackTensorIdentity : PullbackTensorIdentityStatement.{u} := by
  intro X M N
  have h (T : X.Modules) :
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _
        ((Scheme.Modules.pullbackId X).hom.app T) =
      (Scheme.Modules.pushforwardId X).inv.app T := by
    have ht := unit_conjugateEquiv Adjunction.id
      (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
      (Scheme.Modules.pullbackId X).hom T
    rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at ht
    rw [Adjunction.homEquiv_unit, ← ht]
    change 𝟙 T ≫ _ = _
    rw [Category.id_comp]
    rfl
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv _ _).injective
  rw [adjoint_tensor]
  dsimp only [Functor.id_obj] at h ⊢
  rw [h, h, h]
  exact pushforward_tensor_identity X M N

private lemma tensorHomEquiv_comm_comp {X : Scheme.{u}} {M N T : X.Modules}
    (k : tensorObj N M ⟶ T) :
    tensorHomEquiv M N T ((tensorComm M N).hom ≫ k) =
      (β_ M.val N.val).hom ≫ tensorHomEquiv N M T k :=
  (sheafifyAdjunction X).homEquiv_naturality_left _ _

private lemma tensorSheafifyUnit_comm {X : Scheme.{u}} (M N : X.Modules) :
    tensorSheafifyUnit M N ≫ (tensorComm M N).hom.val =
      (β_ M.val N.val).hom ≫ tensorSheafifyUnit N M :=
  ((sheafifyAdjunction X).unit.naturality (β_ M.val N.val).hom).symm

private lemma pushforward_tensor_symmetry {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : X.Modules) :
    pushforwardTensorApp f P Q ≫ (Scheme.Modules.pushforward f).map (tensorComm P Q).hom =
      (tensorComm _ _).hom ≫ pushforwardTensorApp f Q P := by
  apply (tensorHomEquiv _ _ _).injective
  rw [tensorHomEquiv_comp, tensorHomEquiv_comm_comp,
    tensorHomEquiv_pushforwardTensorApp, tensorHomEquiv_pushforwardTensorApp]
  refine PresheafOfModules.hom_ext (fun U => ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_))
  exact congrArg (fun k => (k.app ((TopologicalSpace.Opens.map f.base).op.obj U)).hom
    (p ⊗ₜ q)) (tensorSheafifyUnit_comm P Q)

lemma pullbackTensorSymmetry : PullbackTensorSymmetryStatement.{u} := by
  intro X Y f M N
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    homEquiv_pullbackTensorComparisonApp, homEquiv_pullbackTensorComparisonApp,
    Category.assoc, pushforward_tensor_symmetry, ← Category.assoc]
  have hn := tensorComm_naturality
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)
  exact (congrArg (fun k => k ≫ pushforwardTensorApp f
    ((Scheme.Modules.pullback f).obj N) ((Scheme.Modules.pullback f).obj M)) hn).trans
      (Category.assoc _ _ _)

private lemma pushforward_tensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (P Q : X.Modules) :
    pushforwardTensorApp g ((Scheme.Modules.pushforward f).obj P)
        ((Scheme.Modules.pushforward f).obj Q) ≫
      (Scheme.Modules.pushforward g).map (pushforwardTensorApp f P Q) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (tensorObj P Q) =
    tensorMap ((Scheme.Modules.pushforwardComp f g).hom.app P)
      ((Scheme.Modules.pushforwardComp f g).hom.app Q) ≫
      pushforwardTensorApp (f ≫ g) P Q := by
  apply (tensorHomEquiv _ _ _).injective
  rw [tensorHomEquiv_comp, tensorHomEquiv_pushforwardTensorApp,
    tensorHomEquiv_tensorMap_comp, tensorHomEquiv_pushforwardTensorApp]
  refine PresheafOfModules.hom_ext (fun U => ModuleCat.MonoidalCategory.tensor_ext (fun p q => ?_))
  exact congrArg (fun k => (k.app ((TopologicalSpace.Opens.map g.base).op.obj U)).hom
    (p ⊗ₜ q)) (tensorHomEquiv_pushforwardTensorApp f P Q)

private lemma homEquiv_comp_apply {C D E : Type*}
    [Category* C] [Category* D] [Category* E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {A : C} {B : E} (k : L₂.obj (L₁.obj A) ⟶ B) :
    (adj₁.comp adj₂).homEquiv _ _ k =
      adj₁.homEquiv _ _ (adj₂.homEquiv _ _ k) := by
  rw [Adjunction.comp_homEquiv]
  rfl

private lemma adjoint_composite_tensor {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {M N : Z.Modules} {P Q : X.Modules}
    (a : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ⟶ P)
    (b : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N) ⟶ Q) :
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _
      ((Scheme.Modules.pullback f).map (pullbackTensorComparisonApp g M N) ≫
        pullbackTensorComparisonApp f _ _ ≫ tensorMap a b) =
    tensorMap (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _ a)
      (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv _ _ b) ≫
      pushforwardTensorApp g ((Scheme.Modules.pushforward f).obj P)
        ((Scheme.Modules.pushforward f).obj Q) ≫
      (Scheme.Modules.pushforward g).map (pushforwardTensorApp f P Q) := by
  rw [homEquiv_comp_apply, Adjunction.homEquiv_naturality_left, adjoint_tensor, ← Category.assoc,
    Adjunction.homEquiv_naturality_right, adjoint_tensor, Category.assoc]
  rfl

lemma pullbackTensorComposition : PullbackTensorCompositionStatement.{u} := by
  intro X Y Z f g M N
  let adj := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  have h (T : Z.Modules) :
      adj.homEquiv _ _ ((Scheme.Modules.pullbackComp f g).hom.app T) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app _ =
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).unit.app T := by
    have ht := homEquiv_conjugate adj
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      (Scheme.Modules.pullbackComp f g).inv
      ((Scheme.Modules.pullbackComp f g).hom.app T)
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at ht
    simpa only [Iso.inv_hom_id_app, Adjunction.homEquiv_id] using ht.symm
  apply ((Scheme.Modules.pullbackComp f g).app (tensorObj M N)).eq_inv_comp.mp
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  rw [homEquiv_pullbackTensorComparisonApp]
  erw [homEquiv_conjugate adj
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv]
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  dsimp only [adj]
  rw [adjoint_composite_tensor]
  simp only [Category.assoc]
  rw [pushforward_tensor_composition, ← Category.assoc, tensorMap_comp]
  change _ = tensorMap (adj.homEquiv _ _ _ ≫ _) (adj.homEquiv _ _ _ ≫ _) ≫ _
  dsimp only [Functor.id_obj]
  rw [h, h]

/-- Identity, composition and explicit symmetry compatibility of the canonical comparison. -/
theorem pullbackTensorCompatibility : PullbackTensorCompatibilityStatement.{u} :=
  ⟨pullbackTensorIdentity, pullbackTensorComposition, pullbackTensorSymmetry⟩

end Langlands.Scheme.Modules
