import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs
import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackCoherenceProofs
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

@[simp]
lemma localDualPullback_zero (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    localDualPullback f M U 0 = 0 := by
  simp [localDualPullback]

@[simp]
lemma localDualPullback_add (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    (h k : Γ(dual M, U)) :
    localDualPullback f M U (h + k) =
      localDualPullback f M U h + localDualPullback f M U k := by
  unfold localDualPullback
  rw [localHomPullback_add, Preadditive.add_comp]

lemma localDualPullback_naturality (f : X ⟶ Y) {M N : Y.Modules}
    (a : M ⟶ N) (U : Y.Opens) (h : Γ(dual N, U)) :
    localDualPullback f M U ((dualMap a).app U h) =
      (dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map a)).app (f ⁻¹ᵁ U)
        (localDualPullback f N U h) := by
  simp only [dualMap_app, localDualPullback]
  have hn := localHomPullback_naturality f a
    (𝟙 (Langlands.SchemeModule.structureModule Y)) U h
  have hi : SheafOfModules.Hom.over (𝟙 (Langlands.SchemeModule.structureModule Y)) U = 𝟙 _ := rfl
  have hj : ((AlgebraicGeometry.Scheme.Modules.pullback f).map
      (𝟙 (Langlands.SchemeModule.structureModule Y))).over (f ⁻¹ᵁ U) = 𝟙 _ :=
    congrArg (fun (a : (AlgebraicGeometry.Scheme.Modules.pullback f).obj
        (Langlands.SchemeModule.structureModule Y) ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback f).obj
          (Langlands.SchemeModule.structureModule Y)) => SheafOfModules.Hom.over a (f ⁻¹ᵁ U))
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map_id
        (Langlands.SchemeModule.structureModule Y))
  rw [hi, hj, Category.comp_id, Category.comp_id] at hn
  exact (congrArg (fun k => k ≫ (pullbackUnitIso f).hom.over (f ⁻¹ᵁ U)) hn).trans
    (Category.assoc _ _ _)

lemma localHomPullback_postcompose (f : X ⟶ Y) {M N N' : Y.Modules}
    (b : N ⟶ N') (U : Y.Opens) (h : LocalHom M N U) :
    localHomPullback f U (h ≫ b.over U) =
      localHomPullback f U h ≫
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map b).over (f ⁻¹ᵁ U) := by
  have hn := localHomPullback_naturality f (𝟙 M) b U h
  have hi : SheafOfModules.Hom.over (𝟙 M) U = 𝟙 _ := rfl
  have hj : ((AlgebraicGeometry.Scheme.Modules.pullback f).map (𝟙 M)).over (f ⁻¹ᵁ U) = 𝟙 _ :=
    congrArg (fun (a : (AlgebraicGeometry.Scheme.Modules.pullback f).obj M ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback f).obj M) =>
      SheafOfModules.Hom.over a (f ⁻¹ᵁ U))
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map_id M)
  rw [hi, hj, Category.id_comp, Category.id_comp] at hn
  exact hn

lemma localDualPullback_identity (X : AlgebraicGeometry.Scheme.{u}) (M : X.Modules)
    (U : X.Opens) (h : Γ(dual M, U)) :
    localDualPullback (𝟙 X) M U h =
      (dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M)).app U h := by
  rw [localDualPullback, localHomPullbackIdentity, pullbackUnitIdentity, dualMap_app]
  change ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M).over U ≫
    h ≫ ((AlgebraicGeometry.Scheme.Modules.pullbackId X).inv.app
      (Langlands.SchemeModule.structureModule X)).over U ≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app
      (Langlands.SchemeModule.structureModule X)).over U = _
  have hc := ((SheafOfModules.overFunctor X.ringCatSheaf U).mapIso
    ((AlgebraicGeometry.Scheme.Modules.pullbackId X).app
      (Langlands.SchemeModule.structureModule X))).inv_hom_id
  change ((AlgebraicGeometry.Scheme.Modules.pullbackId X).inv.app
      (Langlands.SchemeModule.structureModule X)).over U ≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app
      (Langlands.SchemeModule.structureModule X)).over U = 𝟙 _ at hc
  rw [hc]
  exact congrArg (fun k => ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M).over U ≫ k)
    (Category.comp_id h)

set_option maxHeartbeats 800000 in
lemma localDualPullback_composition (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (h : Γ(dual M, U)) :
    localDualPullback f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (localDualPullback g M U h) =
      (dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M)).app
        ((f ≫ g) ⁻¹ᵁ U) (localDualPullback (f ≫ g) M U h) := by
  have hu := pullbackUnitComposition X Y Z f g
  have hc : (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app
      (Langlands.SchemeModule.structureModule Z) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫
      (pullbackUnitIso f).hom = (pullbackUnitIso (f ≫ g)).hom := by
    rw [← hu]
    exact ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app
      (Langlands.SchemeModule.structureModule Z)).inv_hom_id_assoc
        (pullbackUnitIso (f ≫ g)).hom
  have ho := congrArg (fun (a : (AlgebraicGeometry.Scheme.Modules.pullback (f ≫ g)).obj
      (Langlands.SchemeModule.structureModule Z) ⟶ Langlands.SchemeModule.structureModule X) =>
    a.over ((f ≫ g) ⁻¹ᵁ U)) hc
  change ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app
      (Langlands.SchemeModule.structureModule Z)).over ((f ≫ g) ⁻¹ᵁ U) ≫
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map (pullbackUnitIso g).hom).over
      ((f ≫ g) ⁻¹ᵁ U) ≫ (pullbackUnitIso f).hom.over ((f ≫ g) ⁻¹ᵁ U) =
    (pullbackUnitIso (f ≫ g)).hom.over ((f ≫ g) ⁻¹ᵁ U) at ho
  rw [localDualPullback, localDualPullback, localHomPullback_postcompose,
    localHomPullbackComposition, dualMap_app, localDualPullback]
  simp only [Category.assoc]
  exact congrArg (fun k => ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M).over
    ((f ≫ g) ⁻¹ᵁ U) ≫ localHomPullback (f ≫ g) U h ≫ k) ho

section Assembly

lemma localDualPullback_restrict (f : X ⟶ Y) (M : Y.Modules)
    {U V : Y.Opens} (i : V ⟶ U) (h : Γ(dual M, U)) :
    localDualPullback f M V (LocalHom.restrict i h) =
      LocalHom.restrict ((Opens.map f.base).map i) (localDualPullback f M U h) := by
  unfold localDualPullback
  rw [localHomPullback_restrict f M (Langlands.SchemeModule.structureModule Y) i h]
  rfl

lemma localDualPullback_smul (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (r : Γ(Y, U)) (h : Γ(dual M, U)) :
    localDualPullback f M U (r • h) = f.app U r • localDualPullback f M U h := by
  unfold localDualPullback
  rw [localHomPullback_smul f M (Langlands.SchemeModule.structureModule Y) U r h]
  apply LocalHom.ext
  intro V i
  ext x
  exact ((pullbackUnitIso f).hom.val.app (op V)).hom.map_smul _ _

/-- The local functional pullbacks assemble into a morphism to the pushforward of the dual. -/
def dualPushforwardComparison (f : X ⟶ Y) (M : Y.Modules) :
    dual M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward f).obj
      (dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)) where
  val :=
    { app := fun U => ModuleCat.ofHom
        (Y := ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj
          (dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M))).val.obj U)
        { toFun := localDualPullback f M U.unop
          map_add' := localDualPullback_add f M U.unop
          map_smul' := localDualPullback_smul f M U.unop }
      naturality := by
        intro U V i
        ext h
        exact localDualPullback_restrict f M i.unop h }

/-- The canonical comparison: the adjunction mate of the local functional pullback map. -/
def dualPullbackComparison (f : X ⟶ Y) (M : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj (dual M) ⟶
      dual ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (dualPushforwardComparison f M)

lemma homEquiv_dualPullbackComparison (f : X ⟶ Y) (M : Y.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (dualPullbackComparison f M) =
        dualPushforwardComparison f M :=
  Equiv.apply_symm_apply _ _

lemma dualPullbackComparison_local (f : X ⟶ Y) (M : Y.Modules)
    (U : Y.Opens) (h : Γ(dual M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (dualPullbackComparison f M)).app U h =
        localDualPullback f M U h := by
  rw [homEquiv_dualPullbackComparison]
  rfl

lemma dualPushforwardComparison_naturality (f : X ⟶ Y)
    {M N : Y.Modules} (a : M ⟶ N) :
    dualMap a ≫ dualPushforwardComparison f M =
      dualPushforwardComparison f N ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward f).map
          (dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map a)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro h
  exact localDualPullback_naturality f a U.unop h

lemma dualPullbackComparison_naturality (f : X ⟶ Y)
    {M N : Y.Modules} (a : M ⟶ N) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (dualMap a) ≫
        dualPullbackComparison f M =
      dualPullbackComparison f N ≫
        dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map a) := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_dualPullbackComparison, homEquiv_dualPullbackComparison]
  exact dualPushforwardComparison_naturality f a

end Assembly

section GlobalCoherence

lemma dualPullbackComparison_id (M : X.Modules) :
    dualPullbackComparison (𝟙 X) M =
      (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app (dual M) ≫
        dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M) := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)).homEquiv
    _ _).injective
  rw [homEquiv_dualPullbackComparison, homEquiv_conjugate Adjunction.id
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom,
    AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom]
  ext U h
  exact localDualPullback_identity X M U h

set_option maxHeartbeats 800000 in
lemma dualPullbackComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    dualPullbackComparison (f ≫ g) M =
      (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app (dual M) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map
          (dualPullbackComparison g M) ≫
        dualPullbackComparison f
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) ≫
        dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app M) := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv
    _ _).injective
  rw [homEquiv_dualPullbackComparison, homEquiv_conjugate
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f))
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv,
    AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv,
    homEquiv_comp_map, Adjunction.homEquiv_naturality_right,
    homEquiv_dualPullbackComparison, homEquiv_dualPullbackComparison]
  ext U h
  change localDualPullback (f ≫ g) M U h =
    (dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app M)).app
      ((f ≫ g) ⁻¹ᵁ U) (localDualPullback f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
        (g ⁻¹ᵁ U) (localDualPullback g M U h))
  rw [localDualPullback_composition]
  change _ = (dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M) ≫
    dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app M)).app
      ((f ≫ g) ⁻¹ᵁ U) (localDualPullback (f ≫ g) M U h)
  rw [← dualMap_comp, Iso.inv_hom_id_app, dualMap_id]
  rfl

end GlobalCoherence

end Langlands.Scheme.Modules
