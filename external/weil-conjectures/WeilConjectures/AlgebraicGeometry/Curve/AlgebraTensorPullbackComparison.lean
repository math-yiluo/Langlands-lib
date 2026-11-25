/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.SheafTensorPushoutCancellation
import WeilConjectures.Topology.InverseImageRegularExtension
import WeilConjectures.Topology.InverseImageOperationExt

/-! # Algebra base change compared with module tensor pullback

Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096; Tag 09MS, coefficient quotient.
(blueprint: lem-sc-algebra-tensor-pullback-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

section
variable {U X : Scheme.{u}} (f : U ⟶ X) (B : X.CommAlgebraSheaf)
set_option hygiene false in
local notation "𝓙" T => Opens.grothendieckTopology T
set_option hygiene false in
local notation "𝓡" A => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj A
set_option hygiene false in
local notation "𝓻" a => (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map a
set_option hygiene false in
local notation "A" => B.right
set_option hygiene false in
local notation "ρ" => B.hom
set_option hygiene false in
local notation "S" => SheafOfModules.restrictScalars.{u} (𝓻 ρ)
set_option hygiene false in
local notation "I" => TopCat.Sheaf.inverseImageModule f.base A
set_option hygiene false in
local notation "t₀" => (TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map ρ

-- Unlike the affine helper, B is an arbitrary algebra sheaf, not f_* O_U.
private theorem inverseRestrict_smul {U X : Scheme.{u}} (f : U ⟶ X)
    (B : X.CommAlgebraSheaf)
    (G : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj B.right))
    (W : (Opens U)ᵒᵖ) (r : (TopCat.Sheaf.inverseImageRing f.base X.sheaf).obj.obj W)
    (m : (TopCat.Sheaf.inverseImageModule f.base B.right G).val.obj W) :
    @SMul.smul _ _ (TopCat.Sheaf.inverseImageModuleInstances f.base X.sheaf
      ((SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).map B.hom)).obj G)
      W).toSMul r m =
    @SMul.smul _ _ (TopCat.Sheaf.inverseImageModuleInstances f.base B.right G W).toSMul
      (((TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map B.hom).hom.app
        W r) m := by
  let M := (S).obj G
  let hM := Classical.choose_spec (TopCat.Sheaf.exists_inverseImageModuleInstances
    f.base X.sheaf M)
  let hG := Classical.choose_spec (TopCat.Sheaf.exists_inverseImageModuleInstances
    f.base A G)
  apply TopCat.Sheaf.inverseImageOperation_ext f.base X.sheaf
    ((SheafOfModules.toSheaf _).obj M) (TopCat.Sheaf.inverseImageAb f.base A G)
    (fun W r m ↦ @SMul.smul _ _
      (TopCat.Sheaf.inverseImageModuleInstances f.base X.sheaf M W).toSMul r m)
    (fun W r m ↦ @SMul.smul _ _
      (TopCat.Sheaf.inverseImageModuleInstances f.base A G W).toSMul ((t₀).hom.app W r) m)
    (by
      intro V W i r m
      exact hM.1 i r m)
    (by
      intro V W i r m
      erw [hG.1]
      congr 1
      exact ConcreteCategory.congr_hom ((t₀).hom.naturality i).symm r)
    (by
      intro V r m
      let adjR := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f.base) CommRingCat.{u} (𝓙 X) (𝓙 U)
      have hn : (t₀).hom.app ((Opens.map f.base).op.obj V)
          ((adjR.unit.app X.sheaf).hom.app V r) =
          (adjR.unit.app A).hom.app V ((ρ).hom.app V r) :=
        congrArg (fun a ↦ a.hom.app V r) (adjR.unit_naturality ρ)
      erw [hn]
      exact (hM.2 V r m).symm.trans (hG.2 V ((ρ).hom.app V r) m)
      )
    W r m

private def inverseRestrictIso (G : SheafOfModules.{u} (𝓡 A)) :
    (SheafOfModules.restrictScalars (𝓻 t₀)).obj (I G) ≅
      TopCat.Sheaf.inverseImageModule f.base X.sheaf ((S).obj G) where
  hom := ⟨PresheafOfModules.homMk (𝟙 _) (fun W r m ↦ by
    exact (inverseRestrict_smul f B G W r m).symm)⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 _) (fun W r m ↦ by
    exact inverseRestrict_smul f B G W r m)⟩
  hom_inv_id := by ext W m; rfl
  inv_hom_id := by ext W m; rfl

end

section
set_option hygiene false in
local notation "𝓡" E =>
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj E

private def changeOfRingsIso {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) {M N : SheafOfModules.{u} (𝓡 A)} (q : M ≅ N) :
    SheafOfModules.changeOfRings.{u, u, u} t M ≅
      SheafOfModules.changeOfRings.{u, u, u} t N := by
  let p : SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M ≅
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} t N :=
    PresheafOfModules.isoMk (fun W ↦
      (ModuleCat.extendScalars (t.hom.app W).hom).mapIso
        ((PresheafOfModules.evaluation (𝓡 A).obj W).mapIso
          ((SheafOfModules.forget (𝓡 A)).mapIso q)))
      (by
        intro W W' i
        exact SheafOfModules.changeOfRingsHom_naturality t M q.hom i)
  exact (PresheafOfModules.sheafification (𝟙 (𝓡 B).obj)).mapIso p

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped ChangeOfRings in
private theorem changeOfRingsIso_formula {T : TopCat.{u}} {A B : T.Sheaf CommRingCat.{u}}
    (t : A ⟶ B) {M N : SheafOfModules.{u} (𝓡 A)} (q : M ≅ N)
    (W : (TopologicalSpace.Opens T)ᵒᵖ)
    (x : (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M).obj W) :
    (changeOfRingsIso t q).hom.val.app W
      (((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M)).app W x) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit.app
      (SheafOfModules.changeOfRingsPresheaf.{u, u, u} t N)).app W
      ((ModuleCat.extendScalars (t.hom.app W).hom).map (q.hom.val.app W) x) := by
  let p : SheafOfModules.changeOfRingsPresheaf.{u, u, u} t M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u, u} t N :=
    { app := fun W ↦ (ModuleCat.extendScalars (t.hom.app W).hom).map (q.hom.val.app W)
      naturality := SheafOfModules.changeOfRingsHom_naturality t M q.hom }
  exact congrArg (fun a ↦ a.app W x)
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (𝓡 B).obj)).unit_naturality p)

end

/-- Canonical algebra pushout comparison for the chosen tensor pullback adjunction.

Source: Stacks Project, Tags 0095 and 0096; Tag 09MS, coefficient quotient.
(blueprint: lem-sc-algebra-tensor-pullback-comparison).
The proof constructs the sheaf pushout of the inverse-image structure sheaf and the
inverse-image algebra, then identifies its underlying module by the sheaf tensor
pushout comparison and inverse-image regular extension. -/
private theorem exists_algebraTensorPullbackComparison_canonical {X Z : Scheme.{u}} (j : Z ⟶ X)
    (B : X.CommAlgebraSheaf) :
    ∃ (C : X.CommAlgebraSheaf) (p : B ⟶ C)
      (e : (pushforward j).obj ((tensorPullback j).obj
        (commAlgebraSheafModule X.sheaf B)) ≅ commAlgebraSheafModule X.sheaf C),
      (commAlgebraSheafModuleFunctor X.sheaf).map p =
        (Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
          (commAlgebraSheafModule X.sheaf B) ≫ e.hom := by
  classical
  let JX := Opens.grothendieckTopology X
  let JZ := Opens.grothendieckTopology Z
  -- Construct the Kan extensions pointwise instead of searching for colimits of extensions.
  have : ∀ (F : (Opens X)ᵒᵖ ⥤ CommRingCat.{u}),
      (Opens.map j.base).op.HasLeftKanExtension F := fun F ↦ by
    have : (Opens.map j.base).op.HasPointwiseLeftKanExtension F := fun _ ↦ inferInstance
    exact Functor.HasLeftKanExtension.mk _
      (Functor.pointwiseLeftKanExtensionUnit (Opens.map j.base).op F)
  let adjR := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map j.base) CommRingCat.{u} JX JZ
  let P := (Opens.map j.base).sheafPushforwardContinuous CommRingCat.{u} JX JZ
  let r : TopCat.Sheaf.inverseImageRing j.base X.sheaf ⟶ Z.sheaf :=
    tensorPullbackRingMap j
  let s : TopCat.Sheaf.inverseImageRing j.base X.sheaf ⟶
      TopCat.Sheaf.inverseImageRing j.base B.right :=
    (TopCat.Sheaf.inverseImageConstruction j.base CommRingCat.{u}).map B.hom
  have : HasPushout r s := inferInstance
  let D := pushout r s
  let b : Z.sheaf ⟶ D := pushout.inl r s
  let t : TopCat.Sheaf.inverseImageRing j.base B.right ⟶ D := pushout.inr r s
  let C : X.CommAlgebraSheaf := Under.mk ((show X.sheaf ⟶ P.obj Z.sheaf from ⟨j.c⟩) ≫
    P.map b)
  have hr : adjR.unit.app X.sheaf ≫ P.map r = (show X.sheaf ⟶ P.obj Z.sheaf from
      ⟨j.c⟩) := by
    have h := (adjR.homEquiv X.sheaf Z.sheaf).apply_symm_apply
      (show X.sheaf ⟶ P.obj Z.sheaf from ⟨j.c⟩)
    rw [Adjunction.homEquiv_unit] at h
    exact h
  let p : B ⟶ C := Under.homMk (adjR.unit.app B.right ≫ P.map t) (by
    change B.hom ≫ (adjR.unit.app B.right ≫ P.map t) =
      (show X.sheaf ⟶ P.obj Z.sheaf from ⟨j.c⟩) ≫ P.map b
    have hn : B.hom ≫ adjR.unit.app B.right =
        adjR.unit.app X.sheaf ≫ P.map s := (adjR.unit_naturality B.hom).symm
    erw [← Category.assoc, hn, Category.assoc, ← P.map_comp,
      ← pushout.condition, P.map_comp, ← Category.assoc, hr])
  let M := SheafOfModules.unit
    ((sheafCompose JX (forget₂ CommRingCat.{u} RingCat.{u})).obj B.right)
  let IM := TopCat.Sheaf.inverseImageModule j.base B.right M
  let Rb := SheafOfModules.restrictScalars
    ((sheafCompose JZ (forget₂ CommRingCat.{u} RingCat.{u})).map b)
  obtain ⟨k, _, hk⟩ := SheafOfModules.sheafTensorPushoutCancellation r s b t
    (IsPushout.of_hasPushout r s)
  obtain ⟨v, hv⟩ := SheafOfModules.inverseImageRegularExtension j.base B.right D t
  let q := inverseRestrictIso j B M
  let d : (tensorPullback j).obj (commAlgebraSheafModule X.sheaf B) ≅
      commAlgebraSheafModule Z.sheaf (Under.mk b) :=
    changeOfRingsIso r q.symm ≪≫ (k IM).symm ≪≫ Rb.mapIso v
  let dP : (pushforward j).obj (commAlgebraSheafModule Z.sheaf (Under.mk b)) ≅
      commAlgebraSheafModule X.sheaf C := eqToIso (by rfl)
  let a₀ := Classical.choose (exists_tensorPullbackAdjunction j)
  let e₀ := (pushforward j).mapIso d ≪≫ dP
  refine ⟨C, p, e₀, ?_⟩
  apply hom_ext
  intro V
  ext x
  let W := op (j ⁻¹ᵁ V)
  let m : IM.val.obj W :=
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Opens.map j.base) AddCommGrpCat.{u} JX JZ).unit.app
        ((SheafOfModules.toSheaf _).obj M)).hom.app (op V) x
  change (t.hom.app W) ((adjR.unit.app B.right).hom.app (op V) x) =
    v.hom.val.app W ((k IM).inv.val.app W
      ((changeOfRingsIso r q.symm).hom.val.app W
        ((a₀.unit.app (commAlgebraSheafModule X.sheaf B)).val.app (op V) x)))
  symm
  -- Apply the section formulas without rewriting the composite's dependent module types.
  refine (congrArg (fun y ↦ v.hom.val.app W ((k IM).inv.val.app W
      ((changeOfRingsIso r q.symm).hom.val.app W y)))
    (Classical.choose_spec (exists_tensorPullbackAdjunction j)
      (commAlgebraSheafModule X.sheaf B) (op V) x)).trans ?_
  refine (congrArg (fun y ↦ v.hom.val.app W ((k IM).inv.val.app W y))
    (changeOfRingsIso_formula r q.symm W _)).trans ?_
  exact (congrArg (v.hom.val.app W) (hk IM W m)).trans (hv (op V) x)

/-- Pulling back an algebra sheaf and pushing it forward realizes the unit on its
underlying module, for any supplied tensor-pullback adjunction.

Source: Stacks Project, Sheaves on Spaces, Tags 0095 and 0096; Tag 09MS, coefficient quotient.
(blueprint: lem-sc-algebra-tensor-pullback-comparison).
Proof: Form the inverse-image algebra sheaf and extend its scalars from the
inverse-image structure sheaf to O_Z by the sheaf tensor product of commutative
algebras. Push this algebra sheaf forward, with structure map induced by j. The
canonical coefficient map is p. Forgetting the ring multiplication commutes with
the inverse image and the sheafified tensor construction: both are sheafifications
of the same sectionwise tensors, with the same restriction maps and O_X actions.
This yields an isomorphism from j_*j^* of the underlying module to the underlying
module of the algebra just constructed. It identifies the canonical tensor unit
with the underlying map of p. For a different supplied adjunction a, use uniqueness
of left adjoints to compare it to the canonical adjunction, apply pushforward to
that comparison, and compose the isomorphism with it. The unit comparison identity
gives the asserted equation. No closed immersion or local freeness is required;
the construction works also for the zero algebra and empty schemes. -/
theorem exists_algebraTensorPullbackComparison {X Z : Scheme.{u}} (j : Z ⟶ X)
    (a : tensorPullback j ⊣ pushforward j) (B : X.CommAlgebraSheaf) :
    ∃ (C : X.CommAlgebraSheaf) (p : B ⟶ C)
      (e : (pushforward j).obj ((tensorPullback j).obj
        (commAlgebraSheafModule X.sheaf B)) ≅ commAlgebraSheafModule X.sheaf C),
      (commAlgebraSheafModuleFunctor X.sheaf).map p =
        a.unit.app (commAlgebraSheafModule X.sheaf B) ≫ e.hom := by
  obtain ⟨C, p, e, he⟩ := exists_algebraTensorPullbackComparison_canonical j B
  let a₀ := Classical.choose (exists_tensorPullbackAdjunction j)
  let c := (Adjunction.leftAdjointUniq a a₀).app
    (commAlgebraSheafModule X.sheaf B)
  refine ⟨C, p, (pushforward j).mapIso c ≪≫ e, ?_⟩
  rw [he]
  change a₀.unit.app _ ≫ e.hom = a.unit.app _ ≫
    ((pushforward j).map c.hom ≫ e.hom)
  rw [← Category.assoc]
  exact (congrArg (fun h ↦ h ≫ e.hom)
    (Adjunction.unit_leftAdjointUniq_hom_app a a₀
      (commAlgebraSheafModule X.sheaf B))).symm

end
end AlgebraicGeometry.Scheme.Modules
