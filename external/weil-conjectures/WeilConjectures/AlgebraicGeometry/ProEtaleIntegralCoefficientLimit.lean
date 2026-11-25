/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison

/-!
# Integral pulled-back coefficients as the limit of finite constant coefficients

(blueprint: lemma-comparison-completed-coefficients--1).

Finite representability is natural in the finite label set. The integral comparison is
normalized by its adjunction mate on every profinite test object and every continuous
function into the integer ring. Thus its finite projections specify the canonical map.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

local instance (Y : Scheme.{u}) (J : Type u) :
    HasColimitsOfShape (Discrete J) (Over Y) := by
  have : HasColimitsOfShape (Discrete J) Scheme.{u} := inferInstance
  exact ⟨fun F ↦ Over.hasColimit_of_hasColimit_comp_forget F⟩

private noncomputable def finiteCopiesOverIso (Y : Scheme.{u}) (E : FintypeCat.{u}) :
    (sigmaConst.obj (Over.mk (𝟙 Y))).obj E ≅
      (Scheme.ProEt.forget Y).obj ((Scheme.proEtaleFiniteCopiesFunctor Y).obj E) := by
  change (∐ fun _ : E ↦ Over.mk (𝟙 Y)) ≅
    Over.mk (Sigma.desc (fun _ : E ↦ 𝟙 Y))
  let h : (∐ fun _ : E ↦ Over.mk (𝟙 Y)) ⟶
      Over.mk (Sigma.desc (fun _ : E ↦ 𝟙 Y)) :=
    Sigma.desc fun e : E ↦ Over.homMk (Sigma.ι (fun _ : E ↦ Y) e) (by simp)
  let k : Over.mk (Sigma.desc (fun _ : E ↦ 𝟙 Y)) ⟶
      (∐ fun _ : E ↦ Over.mk (𝟙 Y)) :=
    Over.homMk (Sigma.desc fun e : E ↦
      (Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e).left) (by
        apply Sigma.hom_ext
        intro e
        change Sigma.ι (fun _ : E ↦ Y) e ≫
          Sigma.desc (fun e : E ↦ (Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e).left) ≫
            (∐ fun _ : E ↦ Over.mk (𝟙 Y)).hom =
          Sigma.ι (fun _ : E ↦ Y) e ≫ Sigma.desc (fun _ : E ↦ 𝟙 Y)
        rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
        exact (Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e).w)
  refine ⟨h, k, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro e
    rw [← Category.assoc, show Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e ≫ h =
      Over.homMk (Sigma.ι (fun _ : E ↦ Y) e) (by simp) from Sigma.ι_comp_desc _ _]
    apply Over.OverMorphism.ext
    change Sigma.ι (fun _ : E ↦ Y) e ≫
      Sigma.desc (fun e : E ↦ (Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e).left) = _
    simp
  · apply Over.OverMorphism.ext
    change Sigma.desc (fun e : E ↦
      (Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e).left) ≫ h.left = 𝟙 _
    apply Sigma.hom_ext
    intro e
    rw [Sigma.ι_comp_desc_assoc]
    change (Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e ≫ h).left = _
    simp [h]

@[reassoc]
private theorem finiteCopiesOverIso_ι (Y : Scheme.{u}) (E : FintypeCat.{u}) (e : E) :
    Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e ≫ (finiteCopiesOverIso Y E).hom =
      Over.homMk (Sigma.ι (fun _ : E ↦ Y) e) (by
        change Sigma.ι (fun _ : E ↦ Y) e ≫ Sigma.desc (fun _ : E ↦ 𝟙 Y) = 𝟙 Y
        simp) := by
  exact Sigma.ι_comp_desc _ _

private noncomputable def finiteCopiesOverNatIso (Y : Scheme.{u}) :
    CategoryTheory.forget FintypeCat.{u} ⋙ sigmaConst.obj (Over.mk (𝟙 Y)) ≅
      Scheme.proEtaleFiniteCopiesFunctor Y ⋙ Scheme.ProEt.forget Y :=
  NatIso.ofComponents (finiteCopiesOverIso Y) (by
    intro E F a
    apply Sigma.hom_ext
    intro e
    change Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e ≫
      Sigma.map' a (fun _ ↦ 𝟙 (Over.mk (𝟙 Y))) ≫ (finiteCopiesOverIso Y F).hom =
        Sigma.ι (fun _ : E ↦ Over.mk (𝟙 Y)) e ≫
          (finiteCopiesOverIso Y E).hom ≫ _
    rw [Sigma.ι_comp_map'_assoc, Category.id_comp, finiteCopiesOverIso_ι,
      finiteCopiesOverIso_ι_assoc]
    apply Over.OverMorphism.ext
    change Sigma.ι (fun _ : F ↦ Y) (a e) =
      Sigma.ι (fun _ : E ↦ Y) e ≫ Sigma.desc
        (fun e : E ↦ Sigma.ι (fun _ : F ↦ Y) (a e))
    simp)

private noncomputable def finiteTestObjectIso (Y : Scheme.{u}) :
    FintypeCat.toProfinite ⋙ profiniteToProEtOf Y ≅ Scheme.proEtaleFiniteCopiesFunctor Y := by
  let e := (profinite_test_object_functor Y).2.2.1.some
  apply (Functor.FullyFaithful.whiskeringRight
    (Functor.FullyFaithful.ofFullyFaithful (Scheme.ProEt.forget Y)) FintypeCat.{u}).preimageIso
  exact e ≪≫ finiteCopiesOverNatIso Y

private noncomputable def finiteRepresentation (X : Scheme.{u}) :
    sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X :=
  Functor.isoWhiskerRight (Scheme.proEtaleFiniteConstantRepresentableIso X)
      (sheafToPresheaf _ _) ≪≫
    Functor.isoWhiskerRight (finiteTestObjectIso X).symm uliftYoneda.{u + 1}

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def integralTowerCone (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (e : Padic.coefficientExtensionIntegers l E ≃+*
      Padic.coefficientExtensionPositiveLimit l E)
    (he : @IsHomeomorph _ _ (Padic.coefficientExtensionIntegersTopology l E)
      (Padic.coefficientExtensionPositiveLimitTopology l E) e) :
    Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite) := by
  letI := Padic.coefficientExtensionIntegersTopology l E
  letI := Padic.coefficientExtensionPositiveLimitTopology l E
  letI (n : ℕ) : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  refine { pt := sfbIntegralProfinite l E, π := ?_ }
  exact NatTrans.ofOpSequence
    (fun n ↦ ConcreteCategory.ofHom
      (show C(sfbIntegralProfinite l E,
        FintypeCat.toProfinite.obj (sfbIntegralFiniteLevel l E n)) from
        ⟨fun x ↦ (e x).val n, by
      exact (continuous_apply n).comp (continuous_induced_dom.comp he.continuous)⟩))
    (by
      intro n
      simp only [Functor.const_obj_map, Functor.comp_map,
        sfbIntegralFiniteTower, Functor.ofOpSequence_map_homOfLE_succ]
      ext x
      change (e x).val n = Padic.coefficientExtensionTransition l E (n + 1)
        ((e x).val (n + 1))
      exact ((Subring.mem_iInf.mp (e x).property) n).symm)

private noncomputable def integralTowerCone_isLimit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (e : Padic.coefficientExtensionIntegers l E ≃+*
      Padic.coefficientExtensionPositiveLimit l E)
    (he : @IsHomeomorph _ _ (Padic.coefficientExtensionIntegersTopology l E)
      (Padic.coefficientExtensionPositiveLimitTopology l E) e) :
    IsLimit (integralTowerCone l E e he) := by
  letI := Padic.coefficientExtensionPositiveLimitTopology l E
  letI := Padic.coefficientExtensionIntegersTopology l E
  letI (n : ℕ) : TopologicalSpace (Padic.coefficientExtensionRing l E (n + 1)) := ⊥
  let h : Padic.coefficientExtensionIntegers l E ≃ₜ
      Padic.coefficientExtensionPositiveLimit l E :=
    { e.toEquiv with
      continuous_toFun := he.continuous
      continuous_invFun := e.toEquiv.continuous_symm_iff.mpr he.isOpenMap }
  let b (s : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
      (x : s.pt) : Padic.coefficientExtensionPositiveLimit l E :=
    ⟨fun n ↦ s.π.app (op n) x, by
      apply Subring.mem_iInf.mpr
      intro n
      change Padic.coefficientExtensionTransition l E (n + 1)
        (s.π.app (op (n + 1)) x) = s.π.app (op n) x
      have hw := ConcreteCategory.congr_hom
        (s.w (homOfLE (Nat.le_add_right n 1)).op) x
      simp only [Functor.comp_map, sfbIntegralFiniteTower,
        Functor.ofOpSequence_map_homOfLE_succ] at hw
      change Padic.coefficientExtensionTransition l E (n + 1)
        (s.π.app (op (n + 1)) x) = s.π.app (op n) x at hw
      exact hw⟩
  refine ⟨fun s ↦ CompHausLike.ofHom _ (X := s.pt)
    (Y := sfbIntegralProfinite l E) ⟨fun x ↦ h.symm (b s x),
    h.symm.continuous.comp (continuous_induced_rng.mpr
      (continuous_pi fun n ↦ (s.π.app (op n)).hom.hom.continuous))⟩, ?_, ?_⟩
  · intro s n
    ext x
    change (e (e.symm (b s x))).val n.unop = _
    rw [e.apply_symm_apply]
    rfl
  · intro s m hm
    ext x
    apply e.injective
    apply Subtype.ext
    funext n
    have hx := ConcreteCategory.congr_hom (hm (op n)) x
    change (e (m x)).val n = (e (e.symm (b s x))).val n
    rw [e.apply_symm_apply]
    exact hx

private noncomputable def integralPullbackForgetIso (X : Scheme.{u}) :
    sfbPullbackFromPoint X ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1}) ≅
      sheafCompose (coherentTopology Profinite.{u}) (forget Ab.{u + 1}) ⋙
        Functor.sheafPullbackConstruction.sheafPullback (profiniteToProEtOf X)
          (Type (u + 1)) (coherentTopology Profinite.{u}) (Scheme.ProEt.topology X) := by
  let U := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let := Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  let : U.IsContinuous J K :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology specZ) _
  let : PreservesFiniteLimits U := (profinite_test_object_functor X).1
  let : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  let : (forget Ab.{u + 1}).PreservesLeftKanExtensions U.op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{u, u + 1} (forget Ab.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (forget Ab.{u + 1}) P U.op V := by
      intro V
      infer_instance
    infer_instance
  let a : sfbPullbackFromPoint X ⊣ U.sheafPushforwardContinuous Ab.{u + 1} J K :=
    sfbIntegralPointAdjunction X
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U Ab.{u + 1} J K
  exact Functor.isoWhiskerRight (a.leftAdjointUniq b)
      (sheafCompose K (forget Ab.{u + 1})) ≪≫
    sheafPullbackForgetIso J K U (forget Ab.{u + 1})

private instance integralTestContinuous (X : Scheme.{u}) :
    (profiniteToProEtOf X).IsContinuous (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology X) := by
  let := Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  exact Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology specZ) _

private theorem integralPullbackForgetIso_unit (X : Scheme.{u})
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (S : Profinite.{u}) (x : A.obj.obj (op S)) :
    ((integralPullbackForgetIso X).hom.app A).hom.app
        (op ((profiniteToProEtOf X).obj S))
      (((sfbIntegralPointAdjunction X).unit.app A).hom.app (op S) x) =
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (profiniteToProEtOf X) (Type (u + 1)) (coherentTopology Profinite.{u})
      (Scheme.ProEt.topology X)).unit.app
        ((sheafCompose (coherentTopology Profinite.{u}) (forget Ab.{u + 1})).obj A)).hom.app
          (op S) x := by
  let U := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let := Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  let : U.IsContinuous J K :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology specZ) _
  let : PreservesFiniteLimits U := (profinite_test_object_functor X).1
  let : RepresentablyFlat U := flat_of_preservesFiniteLimits U
  let : (forget Ab.{u + 1}).PreservesLeftKanExtensions U.op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{u, u + 1} (forget Ab.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (forget Ab.{u + 1}) P U.op V := by
      intro V
      infer_instance
    infer_instance
  let a : sfbPullbackFromPoint X ⊣ U.sheafPushforwardContinuous Ab.{u + 1} J K :=
    sfbIntegralPointAdjunction X
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U Ab.{u + 1} J K
  have ha := a.unit_leftAdjointUniq_hom_app b A
  have hb := sheafPullbackForgetIso_unit J K U (forget Ab.{u + 1}) A
  have hax := congrArg (fun t ↦ t.hom.app (op S) x) ha
  have hbx := congrArg (fun t ↦ t.hom.app (op S) x) hb
  change ((sheafPullbackForgetIso J K U (forget Ab.{u + 1})).hom.app A).hom.app
      (op (U.obj S))
    (((a.leftAdjointUniq b).hom.app A).hom.app (op (U.obj S))
      ((a.unit.app A).hom.app (op S) x)) = _
  exact (congrArg (fun y ↦
    ((sheafPullbackForgetIso J K U (forget Ab.{u + 1})).hom.app A).hom.app
      (op (U.obj S)) y) hax).trans hbx

private noncomputable def integralUnderlyingRepresentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (sfbCondensedIntegers l E).X.obj ⋙ forget Ab.{u + 1} ≅
      uliftYoneda.{u + 1}.obj (sfbIntegralProfinite l E) :=
  NatIso.ofComponents (fun S ↦ Equiv.toIso
    { toFun := fun x ↦ ULift.up (show S.unop ⟶ sfbIntegralProfinite l E from
        ConcreteCategory.ofHom x.down)
      invFun := fun f ↦ ULift.up f.down.hom.hom
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (by
        intro S T f
        ext x
        rfl)

private noncomputable def representablePullbackIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K]
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    (adj : L ⊣ U.sheafPushforwardContinuous (Type (u + 1)) J K) (S : C) :
    L.obj (J.uliftYoneda.{u + 1}.obj S) ≅ K.uliftYoneda.{u + 1}.obj (U.obj S) := by
  let t : J.uliftYoneda.{u + 1}.obj S ⟶
      (U.sheafPushforwardContinuous (Type (u + 1)) J K).obj
        (K.uliftYoneda.{u + 1}.obj (U.obj S)) :=
    ⟨{ app := fun T ↦ ↾fun f ↦ ULift.up (U.map f.down)
       naturality := by
         intro T V f
         ext g
         apply ULift.ext
         change U.map (f.unop ≫ g.down) = U.map f.unop ≫ U.map g.down
         exact U.map_comp _ _ }⟩
  let r := (adj.homEquiv _ _).symm t
  have hr : IsIso r := by
    apply isIso_of_coyoneda_map_bijective
    intro F
    let e := (K.uliftYonedaEquiv.{u + 1} (X := U.obj S) (F := F)).trans
      ((J.uliftYonedaEquiv.{u + 1} (X := S)
        (F := (U.sheafPushforwardContinuous (Type (u + 1)) J K).obj F)).symm.trans
          (adj.homEquiv _ _).symm)
    have h (f : K.uliftYoneda.{u + 1}.obj (U.obj S) ⟶ F) : r ≫ f = e f := by
      apply (adj.homEquiv _ _).injective
      rw [adj.homEquiv_naturality_right]
      dsimp only [r, e, Equiv.trans_apply]
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      apply (J.uliftYonedaEquiv.{u + 1}).injective
      erw [Equiv.apply_symm_apply]
      change f.hom.app (op (U.obj S)) (ULift.up (U.map (𝟙 S))) =
        f.hom.app (op (U.obj S)) (ULift.up (𝟙 (U.obj S)))
      rw [U.map_id]
    exact (show (fun f ↦ r ≫ f) = e from funext h) ▸ e.bijective
  exact asIso r
private theorem representablePullbackIso_unit
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [U.IsContinuous J K]
    (L : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1)))
    (adj : L ⊣ U.sheafPushforwardContinuous (Type (u + 1)) J K)
    (S T : C) (f : T ⟶ S) :
    ((representablePullbackIso J K U L adj S).hom.hom.app (op (U.obj T)))
      (((adj.unit.app (J.uliftYoneda.{u + 1}.obj S)).hom.app (op T)) (ULift.up f)) =
        ULift.up (U.map f) := by
  let t : J.uliftYoneda.{u + 1}.obj S ⟶
      (U.sheafPushforwardContinuous (Type (u + 1)) J K).obj
        (K.uliftYoneda.{u + 1}.obj (U.obj S)) :=
    ⟨{ app := fun V ↦ ↾fun g ↦ ULift.up (U.map g.down)
       naturality := by
         intro V W g
         ext h
         apply ULift.ext
         change U.map (g.unop ≫ h.down) = U.map g.unop ≫ U.map h.down
         exact U.map_comp _ _ }⟩
  have h := (adj.homEquiv (J.uliftYoneda.{u + 1}.obj S)
    (K.uliftYoneda.{u + 1}.obj (U.obj S))).apply_symm_apply t
  exact congrArg (fun g ↦ g.hom.app (op T) (ULift.up f)) h

private noncomputable def integralPullbackRepresentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ((sfbPullbackFromPoint X).obj (sfbCondensedIntegers l E).X).obj ⋙
        forget Ab.{u + 1} ≅
      uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E)) := by
  let U := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let := Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  let : U.IsContinuous J K :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology specZ) _
  let L := Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1)) J K
  let j : (sheafCompose J (forget Ab.{u + 1})).obj (sfbCondensedIntegers l E).X ≅
      J.uliftYoneda.{u + 1}.obj (sfbIntegralProfinite l E) :=
    (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
      (integralUnderlyingRepresentation l E)
  exact (sheafToPresheaf K (Type (u + 1))).mapIso
    ((integralPullbackForgetIso X).app (sfbCondensedIntegers l E).X ≪≫ L.mapIso j ≪≫
      representablePullbackIso J K U L
        (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous U (Type (u + 1)) J K)
        (sfbIntegralProfinite l E))

private theorem integralPullbackRepresentation_unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (S : Profinite.{u}) (f : S ⟶ sfbIntegralProfinite l E) :
    (integralPullbackRepresentation l E X).hom.app
        (op ((profiniteToProEtOf X).obj S))
      ((((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
        (op S)) (ULift.up f.hom.hom)) = ULift.up ((profiniteToProEtOf X).map f) := by
  let U := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let L := Functor.sheafPullbackConstruction.sheafPullback U (Type (u + 1)) J K
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    U (Type (u + 1)) J K
  let A := (sheafCompose J (forget Ab.{u + 1})).obj (sfbCondensedIntegers l E).X
  let j : A ≅ J.uliftYoneda.{u + 1}.obj (sfbIntegralProfinite l E) :=
    (fullyFaithfulSheafToPresheaf J (Type (u + 1))).preimageIso
      (integralUnderlyingRepresentation l E)
  have hn := integralPullbackForgetIso_unit X (sfbCondensedIntegers l E).X S
    (ULift.up f.hom.hom)
  have hj := congrArg (fun t ↦ t.hom.app (op S) (ULift.up f.hom.hom))
    (adj.unit.naturality j.hom)
  change ((adj.unit.app (J.uliftYoneda.{u + 1}.obj (sfbIntegralProfinite l E))).hom.app
      (op S)) (ULift.up f) =
    (L.map j.hom).hom.app _ ((adj.unit.app A).hom.app (op S) (ULift.up f.hom.hom)) at hj
  change ((representablePullbackIso J K U L adj (sfbIntegralProfinite l E)).hom.hom.app _)
    ((L.map j.hom).hom.app _
      (((integralPullbackForgetIso X).hom.app _).hom.app _
        ((((sfbIntegralPointAdjunction X).unit.app _).hom.app (op S))
          (ULift.up f.hom.hom)))) = _
  calc
    _ = ((representablePullbackIso J K U L adj (sfbIntegralProfinite l E)).hom.hom.app _)
        ((L.map j.hom).hom.app _ ((adj.unit.app A).hom.app (op S)
          (ULift.up f.hom.hom))) := congrArg _ (congrArg _ hn)
    _ = _ := (congrArg _ hj.symm).trans
      (representablePullbackIso_unit J K U L adj (sfbIntegralProfinite l E) S f)

private theorem integralComparison_hom_ext (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (f g : (coefficientRing X (sfbCondensedIntegers l E)).X ⟶ sfbCompletedIntegersAb l E X)
    (h : ∀ (S : Profinite.{u}) (x : (sfbCondensedIntegers l E).X.obj.obj (op S)) (n : ℕ),
      (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
          (op ((profiniteToProEtOf X).obj S))
        (f.hom.app (op ((profiniteToProEtOf X).obj S))
          (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
            (op S) x)) =
      (limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
          (op ((profiniteToProEtOf X).obj S))
        (g.hom.app (op ((profiniteToProEtOf X).obj S))
          (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
            (op S) x))) : f = g := by
  apply ((sfbIntegralPointAdjunction X).homEquiv _ _).injective
  ext S x
  let ev := sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{u + 1} ⋙
    (evaluation X.ProEtᵒᵖ RingCat.{u + 1}).obj (op ((profiniteToProEtOf X).obj S.unop))
  apply Concrete.isLimit_ext _ (isLimitOfPreserves ev
    (limit.isLimit (integralCoefficientSheafSystem l E X)))
  intro n
  exact h S.unop x n.unop

private noncomputable def finiteTowerRepresentationIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X) :
    integralCoefficientSheafSystem l E X ⋙ sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj (forget RingCat.{u + 1}) ≅
      sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite ⋙
        profiniteToProEtOf X ⋙ uliftYoneda.{u + 1} := by
  let t : integralCoefficientSheafSystem l E X ⋙ sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget RingCat.{u + 1}) ⟶
      sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite ⋙
        profiniteToProEtOf X ⋙ uliftYoneda.{u + 1} := NatTrans.ofOpSequence
    (fun n ↦ (sfbIntegralFiniteRepresentation l E X a n).hom) (by
      intro n
      simp only [Functor.comp_map, integralCoefficientSheafSystem, sfbIntegralFiniteTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      dsimp only [sfbIntegralFiniteRepresentation, Iso.trans_hom, Functor.mapIso_hom,
        Functor.comp_map, NatTrans.comp_app, Functor.whiskeringRight_obj_map]
      have hc := (constantCommuteCompose (Scheme.ProEt.topology X)
        (forget CommRingCat.{u + 1})).hom.naturality
        (CommRingCat.ofHom
          ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
            ((Padic.coefficientExtensionTransition l E (n + 1)).comp
              (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom)))
      have ha := a.hom.naturality ((sfbIntegralFiniteTower l E).map
        (homOfLE (Nat.le_add_right n 1)).op)
      simp only [sfbIntegralFiniteTower, Functor.ofOpSequence_map_homOfLE_succ] at ha
      have hc' : Functor.whiskerRight (integralCoefficientSheafTransition l E X n).hom
          (forget RingCat.{u + 1}) ≫
          ((constantCommuteCompose (Scheme.ProEt.topology X)
            (forget CommRingCat.{u + 1})).app
              (CommRingCat.of (ULift.{u + 1}
                (Padic.coefficientExtensionRing l E (n + 1))))).hom.hom =
        ((constantCommuteCompose (Scheme.ProEt.topology X)
            (forget CommRingCat.{u + 1})).app
              (CommRingCat.of (ULift.{u + 1}
                (Padic.coefficientExtensionRing l E (n + 1 + 1))))).hom.hom ≫
          (sfbFiniteConstantSets X).map
            (FintypeCat.homMk (X := sfbIntegralFiniteLevel l E (n + 1))
              (Y := sfbIntegralFiniteLevel l E n)
              (Padic.coefficientExtensionTransition l E (n + 1))) :=
        by
          ext V x
          exact congrArg (fun f ↦ f.hom.app V x) hc
      ext V x
      have hx := congrArg (fun t ↦ t.app V x) hc'
      have hy := congrArg (fun t ↦ t.app V
        (((constantCommuteCompose (Scheme.ProEt.topology X)
          (forget CommRingCat.{u + 1})).app
            (CommRingCat.of (ULift.{u + 1}
              (Padic.coefficientExtensionRing l E (n + 1 + 1))))).hom.hom.app V x)) ha
      exact (congrArg (fun y ↦ (a.hom.app (sfbIntegralFiniteLevel l E n)).app V y)
        hx).trans hy)
  let : ∀ n, IsIso (t.app n) := fun n ↦
    inferInstanceAs (IsIso (sfbIntegralFiniteRepresentation l E X a n.unop).hom)
  exact NatIso.ofComponents (fun n ↦ asIso (t.app n)) (fun f ↦ t.naturality f)

private noncomputable def completedIntegralRepresentation (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
    (hsch : IsLimit ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙
      Over.forget X).mapCone c))
    (j : sfbIntegralProfinite l E ≅ c.pt) :
    (completedIntegralCoefficientSheafUnrestricted l E X).obj ⋙
      forget RingCat.{u + 1} ≅
        uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E)) := by
  let U := profiniteToProEtOf X
  let ht : IsLimit (U.mapCone c) :=
    isLimitOfReflects (Scheme.ProEt.forget X)
      (isLimitOfReflects (Over.forget X) hsch)
  let R := sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{u + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj (forget RingCat.{u + 1})
  let d := R.mapCone (limit.cone (integralCoefficientSheafSystem l E X))
  let hd : IsLimit d := isLimitOfPreserves R (limit.isLimit _)
  let q := finiteTowerRepresentationIso l E X a
  let d' := (Cone.postcompose q.hom).obj d
  let hd' : IsLimit d' := IsLimit.postcomposeHomEquiv q d |>.symm hd
  exact hd'.conePointUniqueUpToIso (isLimitOfPreserves uliftYoneda.{u + 1} ht) ≪≫
    uliftYoneda.{u + 1}.mapIso ((profiniteToProEtOf X).mapIso j).symm

private theorem completedIntegralRepresentation_inv_projection
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X)
    (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
    (hsch : IsLimit ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙
      Over.forget X).mapCone c)) (j : sfbIntegralProfinite l E ≅ c.pt)
    (V : X.ProEtᵒᵖ) (f : V.unop ⟶ (profiniteToProEtOf X).obj (sfbIntegralProfinite l E))
    (n : ℕ) :
    (sfbIntegralFiniteRepresentation l E X a n).hom.app V
      ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app V
        ((completedIntegralRepresentation l E X a c hsch j).inv.app V (ULift.up f))) =
      ULift.up (f ≫ (profiniteToProEtOf X).map (j.hom ≫ c.π.app (op n))) := by
  let U := profiniteToProEtOf X
  let ht : IsLimit (U.mapCone c) :=
    isLimitOfReflects (Scheme.ProEt.forget X)
      (isLimitOfReflects (Over.forget X) hsch)
  let R := sheafToPresheaf (Scheme.ProEt.topology X) RingCat.{u + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj (forget RingCat.{u + 1})
  let d := R.mapCone (limit.cone (integralCoefficientSheafSystem l E X))
  let hd : IsLimit d := isLimitOfPreserves R (limit.isLimit _)
  let q := finiteTowerRepresentationIso l E X a
  let d' := (Cone.postcompose q.hom).obj d
  let hd' : IsLimit d' := IsLimit.postcomposeHomEquiv q d |>.symm hd
  have h := hd'.conePointUniqueUpToIso_inv_comp
    (isLimitOfPreserves uliftYoneda.{u + 1} ht) (op n)
  have hx := congrArg (fun t ↦ t.app V
    (ULift.up (f ≫ U.map j.hom))) h
  change (sfbIntegralFiniteRepresentation l E X a n).hom.app V
      ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app V
        ((completedIntegralRepresentation l E X a c hsch j).inv.app V (ULift.up f))) =
      ULift.up ((f ≫ U.map j.hom) ≫ U.map (c.π.app (op n))) at hx
  rw [U.map_comp, ← Category.assoc]
  exact hx

/-- Finite constants and integral pulled-back coefficients have the stated representations;
the ring comparison is the unique one with the prescribed reduction projections.

(blueprint: lemma-comparison-completed-coefficients--1).

Proof: (1) A map into the finite coproduct of copies of X is a clopen labelled partition.
The summands cover it in the pro-etale topology. Glue constant sections on these pieces;
uniqueness on overlaps proves the sheafification universal property, naturally in labels.
For the empty label set use the empty covering of the empty object.
(2) The integers-profinite-tower theorem identifies the integer ring with its positive
finite quotients and makes those quotients cofinal among its finite quotients. Apply the
relative profinite test functor to this limit cone. Yoneda and sectionwise sheaf limits
identify its represented presheaf with the limit of finite constants.
(3) The left-exact site inverse image sends the sheaf represented by a profinite set S
to the sheaf represented by X[S]: use its adjunction, restriction on test objects, and
Yoneda, naturally in S. The adjunction lifts to abelian and ring objects, identifying
this underlying-set inverse image with the prescribed monoidal coefficient pullback.
This gives the representation in clause 2 and the displayed normalization by the unit.
(4) Addition, multiplication, negation, zero and one are computed on finite clopen labels.
The reductions preserve them. Their compatible coordinatewise values give the ring
structure on the limit; the limit projections jointly distinguish sections. The
represented comparison is therefore a ring isomorphism. Its adjunction mate on each
continuous function is exactly its reduction followed by finite-label representation.
This determines every projection, hence determines the comparison uniquely.
-/
theorem sfb_integral_coefficient_limit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ∃ a : sfbFiniteConstantSets X ≅ sfbFiniteRepresentables X,
      ∃ (c : Cone (sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite))
        (j : sfbIntegralProfinite l E ≅ c.pt),
        (∀ (n : ℕ) (x : Padic.coefficientExtensionIntegers l E),
          (j.hom ≫ c.π.app (op n)) x =
            Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x) ∧
        Nonempty (IsLimit c) ∧
        Nonempty (IsLimit ((profiniteToProEtOf X ⋙ Scheme.ProEt.forget X ⋙
          Over.forget X).mapCone c)) ∧
        Nonempty (((sfbPullbackFromPoint X).obj (sfbCondensedIntegers l E).X).obj ⋙
          forget Ab.{u + 1} ≅
            uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E))) ∧
        Nonempty ((completedIntegralCoefficientSheafUnrestricted l E X).obj ⋙
          forget RingCat.{u + 1} ≅
            uliftYoneda.{u + 1}.obj ((profiniteToProEtOf X).obj (sfbIntegralProfinite l E))) ∧
        ∃! e : (coefficientRing X (sfbCondensedIntegers l E)).X ≅
            sfbCompletedIntegersAb l E X,
          IsMonHom e.hom ∧ IsMonHom e.inv ∧
          ∀ (S : Profinite.{u}) (f : S ⟶ sfbIntegralProfinite l E) (n : ℕ),
            (sfbIntegralFiniteRepresentation l E X a n).hom.app
                (op ((profiniteToProEtOf X).obj S))
              (((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
                  (op ((profiniteToProEtOf X).obj S)))
                ((e.hom.hom.app (op ((profiniteToProEtOf X).obj S)))
                  (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
                    (op S) (ULift.up f.hom.hom)))) =
              ULift.up ((profiniteToProEtOf X).map (f ≫ j.hom ≫ c.π.app (op n))) := by
  obtain ⟨e, he, htop⟩ := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).1
  let a := finiteRepresentation X
  let c := integralTowerCone l E e htop
  let hc := integralTowerCone_isLimit l E e htop
  have hq (n : ℕ) (x : Padic.coefficientExtensionIntegers l E) :
      c.π.app (op n) x =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) x := he x n
  let : profiniteToCommRingCatOp.{u}.IsRightAdjoint :=
    profiniteToCommRingCatOp_isRightAdjoint
  let : (Over.forget specZ.{u}).IsEquivalence :=
    (Over.equivalenceOfIsTerminal specULiftZIsTerminal).isEquivalence_functor
  let D := sfbIntegralFiniteTower l E ⋙ FintypeCat.toProfinite
  let : PreservesLimitsOfSize.{0, 0} profiniteToScheme.{u} := by
    unfold profiniteToScheme
    infer_instance
  let : PreservesLimit D
      ((profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) ⋙ Over.forget specZ) :=
    inferInstanceAs (PreservesLimit D profiniteToScheme.{u})
  let : PreservesLimit D (profiniteToProEt.{u} ⋙ Scheme.ProEt.forget specZ) :=
    preservesLimit_of_reflects_of_preserves _ (Over.forget specZ)
  let hOver := isLimitOfPreserves
    ((profiniteToProEt ⋙ Scheme.ProEt.forget specZ) ⋙ Over.pullback (toSpecZ X)) hc
  let hsch := isLimitOfPreserves (Over.forget X) hOver
  let hp := integralPullbackRepresentation l E X
  let hd := completedIntegralRepresentation l E X a c hsch (Iso.refl _)
  obtain ⟨f, hf, hfd⟩ := sfb_integral_ring_comparison_exists l E X a c (Iso.refl _)
    hq hc hp hd (integralPullbackRepresentation_unit l E X)
      (completedIntegralRepresentation_inv_projection l E X a c hsch (Iso.refl _))
  let W := sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
    (Functor.whiskeringRight _ _ _).obj (forget Ab.{u + 1})
  have : IsIso (W.map f) := by
    change IsIso (Functor.whiskerRight f.hom (forget Ab.{u + 1}))
    rw [hfd]
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f W
  let e' := asIso f
  have he' : IsMonHom e'.hom := hf
  have hn (S : Profinite.{u}) (g : S ⟶ sfbIntegralProfinite l E) (n : ℕ) :
      (sfbIntegralFiniteRepresentation l E X a n).hom.app
          (op ((profiniteToProEtOf X).obj S))
        ((limit.π (integralCoefficientSheafSystem l E X) (op n)).hom.app
          (op ((profiniteToProEtOf X).obj S))
          (e'.hom.hom.app (op ((profiniteToProEtOf X).obj S))
            (((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
              (op S) (ULift.up g.hom.hom)))) =
        ULift.up ((profiniteToProEtOf X).map (g ≫ (Iso.refl _).hom ≫ c.π.app (op n))) := by
    have hx := congrArg (fun t ↦ t.app (op ((profiniteToProEtOf X).obj S))
      ((((sfbIntegralPointAdjunction X).unit.app (sfbCondensedIntegers l E).X).hom.app
        (op S)) (ULift.up g.hom.hom))) hfd
    change e'.hom.hom.app _ _ = hd.inv.app _ (hp.hom.app _ _) at hx
    rw [hx, integralPullbackRepresentation_unit]
    convert completedIntegralRepresentation_inv_projection l E X a c hsch
      (Iso.refl _) (op ((profiniteToProEtOf X).obj S)) ((profiniteToProEtOf X).map g) n using 1
    rw [Functor.map_comp]
  let := he'
  refine ⟨a, c, Iso.refl _, hq, ⟨hc⟩, ⟨hsch⟩, ⟨hp⟩, ⟨hd⟩,
    e', ⟨he', inferInstance, hn⟩, ?_⟩
  intro y hy
  apply Iso.ext
  apply integralComparison_hom_ext l E X
  intro S x n
  let f : S ⟶ sfbIntegralProfinite l E := ConcreteCategory.ofHom x.down
  apply ((sfbIntegralFiniteRepresentation l E X a n).app
    (op ((profiniteToProEtOf X).obj S))).toEquiv.injective
  exact (hy.2.2 S f n).trans (hn S f n).symm

end AlgebraicGeometry.ProEtale
