/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeFrobenius.NativeFrobeniusModelData
public import WeilConjectures.AlgebraicGeometry.Adic.AdicModuleHomComparisonCore
public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Curry

/-! # Sectionwise calculus for native and translated internal-Hom evaluation

## References

* Stacks 03D6 and 03EO
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Opposite
open CategoryTheory.TwistedActionRingedSite
open WeilConjectures.WeilFrobeniusAction
namespace AlgebraicGeometry.ProEtale.NativeFrobenius

open CategoryTheory.Limits MonoidalCategory

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction

private noncomputable def sectionPair {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
    (V : X.ProEtᵒᵖ) (p : P.obj.obj V) (q : Q.obj.obj V) : (P ⊗ Q).obj.obj V :=
  (Sheaf.tensorObjComparison (Scheme.ProEt.topology X) P Q).app V
    (p ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] q)

private theorem sectionPair_map {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    {P Q P' Q' : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)}
    (f : P ⟶ P') (g : Q ⟶ Q') (V : X.ProEtᵒᵖ)
    (p : P.obj.obj V) (q : Q.obj.obj V) :
    (f ⊗ₘ g).hom.app V (sectionPair P Q V p q) =
      sectionPair P' Q' V (f.hom.app V p) (g.hom.app V q) := by
  exact ConcreteCategory.congr_hom
    (congr_app (Sheaf.tensorObjComparison_naturality f g) V) (p ⊗ₜ[_] q)

/-- Native morphisms into internal Hom are determined by sectionwise evaluation. -/
theorem evaluation_ext {Y : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    {M N Q : AdicSheaf l Y} {f g : Q ⟶ (AdicSheaf.ihom M).obj N}
    (h : ∀ (V : Y.ProEtᵒᵖ) (z : Q.X.obj.obj V) (x : M.X.obj.obj V),
      adicComparisonEval M N V (f.hom.hom.app V z) x =
        adicComparisonEval M N V (g.hom.hom.app V z) x) : f = g := by
  apply Mod.hom_ext
  apply Mod.hom_ext_of_evaluation
  apply Sheaf.tensor_hom_ext
  apply NatTrans.ext
  funext V
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro z x
  change (Mod.evaluation M N).hom.app V
      ((f.hom ▷ M.X).hom.app V (sectionPair Q.X M.X V z x)) =
    (Mod.evaluation M N).hom.app V
      ((g.hom ▷ M.X).hom.app V (sectionPair Q.X M.X V z x))
  rw [← tensorHom_id, ← tensorHom_id, sectionPair_map, sectionPair_map]
  exact h V z x

/-- Native internal-Hom evaluation commutes with precomposition. -/
theorem evaluation_map_source {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    {M M' : AdicSheaf l X} (f : M' ⟶ M) (N : AdicSheaf l X)
    (V : X.ProEtᵒᵖ) (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V)
    (x : M'.X.obj.obj V) :
    adicComparisonEval M' N V (((Mod.ihomMap f).app N).hom.hom.app V z) x =
      adicComparisonEval M N V z (f.hom.hom.app V x) := by
  change (Mod.evaluation M' N).hom.app V
      (sectionPair ((AdicSheaf.ihom M').obj N).X M'.X V
        (((Mod.ihomMap f).app N).hom.hom.app V z) x) =
    (Mod.evaluation M N).hom.app V
      (sectionPair ((AdicSheaf.ihom M).obj N).X M.X V z (f.hom.hom.app V x))
  have h := congrArg (fun k ↦ k.hom.app V
    (sectionPair ((AdicSheaf.ihom M).obj N).X M'.X V z x))
      (Mod.evaluation_ihomMap f N)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply,
    ← tensorHom_id, ← id_tensorHom, sectionPair_map,
    ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] using h

/-- Native internal-Hom evaluation commutes with postcomposition. -/
theorem evaluation_map_target {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}
    (M : AdicSheaf l X) {N N' : AdicSheaf l X} (g : N ⟶ N')
    (V : X.ProEtᵒᵖ) (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V)
    (x : M.X.obj.obj V) :
    adicComparisonEval M N' V (((AdicSheaf.ihom M).map g).hom.hom.app V z) x =
      g.hom.hom.app V (adicComparisonEval M N V z x) := by
  change (Mod.evaluation M N').hom.app V
      (sectionPair ((AdicSheaf.ihom M).obj N').X M.X V
        (((AdicSheaf.ihom M).map g).hom.hom.app V z) x) =
    g.hom.hom.app V ((Mod.evaluation M N).hom.app V
      (sectionPair ((AdicSheaf.ihom M).obj N).X M.X V z x))
  have h := congrArg (fun k ↦ k.hom.app V
    (sectionPair ((AdicSheaf.ihom M).obj N).X M.X V z x))
      (Mod.evaluation_naturality M g)
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ModuleCat.comp_apply,
    ← tensorHom_id, sectionPair_map, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    ModuleCat.id_apply] using h

/-- Native evaluation commutes with restriction of sections. -/
theorem evaluation_restriction {Y : Scheme.{u}} {l : ℕ} [Fact l.Prime]
    (M N : AdicSheaf l Y) {V W : Y.ProEtᵒᵖ} (f : V ⟶ W)
    (z : ((AdicSheaf.ihom M).obj N).X.obj.obj V) (x : M.X.obj.obj V) :
    N.X.obj.map f (adicComparisonEval M N V z x) =
      adicComparisonEval M N W (((AdicSheaf.ihom M).obj N).X.obj.map f z)
        (M.X.obj.map f x) := by
  have h := (Sheaf.tensorObjComparison (Scheme.ProEt.topology Y)
    ((AdicSheaf.ihom M).obj N).X M.X ≫ (Mod.evaluation M N).hom).naturality f
  exact (ConcreteCategory.congr_hom h (z ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x)).symm

section
universe v w
variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  {R : Type (max v w)} [CommRing R]
  [HasWeakSheafify J (ModuleCat.{max v w} R)]
  [(J.W (A := ModuleCat.{max v w} R)).IsMonoidal]
attribute [local instance] Sheaf.monoidalCategory

private theorem tensorObjComparison_eq_mu
    (P Q : Sheaf J (ModuleCat.{max v w} R)) :
    Sheaf.tensorObjComparison J P Q =
      Functor.LaxMonoidal.μ (sheafToPresheaf J (ModuleCat.{max v w} R)) P Q := by
  rfl

end

private theorem sectionPair_pushforward (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) (P Q : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
    (V : Y.ProEtᵒᵖ)
    (z : P.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V))
    (x : Q.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V)) :
    (Functor.LaxMonoidal.μ (lowerStar (WeilCoefficients.{u} l) g.inv) P Q).hom.app V
        (sectionPair ((lowerStar (WeilCoefficients.{u} l) g.inv).obj P)
          ((lowerStar (WeilCoefficients.{u} l) g.inv).obj Q) V z x) =
      sectionPair P Q ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V) z x := by
  have h := Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv) (WeilCoefficients.{u} l)
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology Y) P Q V
  simp only [sectionPair, tensorObjComparison_eq_mu]
  change (((Functor.LaxMonoidal.μ
      (sheafToPresheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l))
      ((lowerStar (WeilCoefficients.{u} l) g.inv).obj P)
      ((lowerStar (WeilCoefficients.{u} l) g.inv).obj Q)).app V ≫
      (Functor.LaxMonoidal.μ (lowerStar (WeilCoefficients.{u} l) g.inv) P Q).hom.app V)
        (z ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x)) = _
  dsimp only [lowerStar, laxMonoidal_lowerStar]
  have h0 := ConcreteCategory.congr_hom h (z ⊗ₜ[ULift.{u + 1} (PadicAlgCl l)] x)
  exact h0

/-- Native inverse-pushforward Hom transport preserves sectionwise evaluation. -/
theorem pushforward_evaluation (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) (M N : AdicSheaf l Y) (V : Y.ProEtᵒᵖ)
    (z : ((adicLowerStar l g.inv).obj ((AdicSheaf.ihom M).obj N)).X.obj.obj V)
    (x : ((adicLowerStar l g.inv).obj M).X.obj.obj V) :
    adicComparisonEval ((adicLowerStar l g.inv).obj M) ((adicLowerStar l g.inv).obj N) V
      (((adicLowerStarCompIhomIso l g.inv M).inv.app N).hom.hom.app V z) x =
        adicComparisonEval M N ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V)
          z x := by
  change ((AdicSheaf.ihom M).obj N).X.obj.obj
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V) at z
  change M.X.obj.obj
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V) at x
  let : (Mod.mapModComap (G := lowerStar (WeilCoefficients.{u} l) g.inv)
      (adicConstantSheafToLowerStar l g.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l g.inv
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l g.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M N
  have hh := congrArg (fun k ↦ k.hom.app V
    (sectionPair ((adicLowerStar l g.inv).obj ((AdicSheaf.ihom M).obj N)).X
      ((adicLowerStar l g.inv).obj M).X V z x)) h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ModuleCat.comp_apply] at hh
  change (Mod.evaluation M N).hom.app _
      ((Functor.LaxMonoidal.μ (lowerStar (WeilCoefficients.{u} l) g.inv)
        ((AdicSheaf.ihom M).obj N).X M.X).hom.app V
          (sectionPair ((adicLowerStar l g.inv).obj ((AdicSheaf.ihom M).obj N)).X
            ((adicLowerStar l g.inv).obj M).X V z x)) =
    (Mod.evaluation ((adicLowerStar l g.inv).obj M)
      ((adicLowerStar l g.inv).obj N)).hom.app V
      ((((adicLowerStarCompIhomIso l g.inv M).inv.app N).hom ▷
        ((adicLowerStar l g.inv).obj M).X).hom.app V
          (sectionPair ((adicLowerStar l g.inv).obj ((AdicSheaf.ihom M).obj N)).X
            ((adicLowerStar l g.inv).obj M).X V z x)) at hh
  have ht := sectionPair_map
    ((adicLowerStarCompIhomIso l g.inv M).inv.app N).hom
    (𝟙 ((adicLowerStar l g.inv).obj M).X) V z x
  rw [tensorHom_id] at ht
  have he := congrArg (fun t ↦
    (Mod.evaluation ((adicLowerStar l g.inv).obj M)
      ((adicLowerStar l g.inv).obj N)).hom.app V t) ht
  have hh2 := hh.trans he
  have hp := sectionPair_pushforward Y l g ((AdicSheaf.ihom M).obj N).X M.X V z x
  exact hh2.symm.trans (congrArg ((Mod.evaluation M N).hom.app
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g.inv).op.obj V)) hp)

private theorem ordinary_evaluation
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}} (M N : Modules R) (V : Cᵒᵖ)
    (x : M.val.obj V) (f : (SheafOfModules.homObj (R := R) M N).val.obj V) :
    (evaluationMap M N).val.app V
      (pureTensor M (SheafOfModules.homObj (R := R) M N) V x f) =
        f.app (op (Over.mk (𝟙 V.unop))) x := by
  let B := SheafOfModules.homObj (R := R) M N
  let e := SheafOfModules.tensorHomEquiv (R := R) M B N
  let e' := PresheafOfModules.homObjEquiv (R := R.obj) M.val B.val N.val
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)
  have he := congrArg SheafOfModules.Hom.val (e.apply_symm_apply (𝟙 B))
  change e' (adj.homEquiv _ N
    ((SheafOfModules.tensorObjIsoSheafification M B).inv ≫ evaluationMap M N)) =
      𝟙 B.val at he
  have he' := e'.eq_symm_apply.mpr he
  rw [Adjunction.homEquiv_unit] at he'
  exact congrArg (fun k ↦ k.app V (x ⊗ₜ[R.obj.obj V] f)) he'

private theorem ordinary_pure_map
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}} {M M' N N' : Modules R}
    (a : M ⟶ M') (b : N ⟶ N') (V : Cᵒᵖ) (x : M.val.obj V) (y : N.val.obj V) :
    (a ⊗ₘ b).val.app V (pureTensor M N V x y) =
      pureTensor M' N' V (a.val.app V x) (b.val.app V y) := by
  exact CategoryTheory.CochainPullback.moduleTmul_map a b V x y

/-- Every twisted presentation has the specified translated evaluation on local maps. -/
theorem translated_evaluation (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    (g : Y ≅ Y) :
    let _ := (translation_continuous Y g).1
    let _ := (translation_continuous Y g).2
    ∀ (P : Presentation (topology Y) (translation g) (ring Y l) (ringIso Y l g))
      (M N : Modules (ring Y l)) (V : (Site Y)ᵒᵖ)
      (f : (SheafOfModules.homObj (R := ring Y l) M N).val.obj
        ((translation g).inverse.op.obj V))
      (x : M.val.obj ((translation g).inverse.op.obj V)),
    ((P.sigmaHom M N).hom.val.app V f).app (op (Over.mk (𝟙 V.unop))) x =
      f.app (op (Over.mk (𝟙 ((translation g).inverse.op.obj V).unop))) x := by
  let _ := (translation_continuous Y g).1
  let _ := (translation_continuous Y g).2
  dsimp only
  intro P M N V f x
  have h := congrArg (fun k ↦ k.val.app V
    (pureTensor M (SheafOfModules.homObj (R := ring Y l) M N)
      ((translation g).inverse.op.obj V) x f)) (P.sigmaHom_evaluation M N)
  change (evaluationMap M N).val.app ((translation g).inverse.op.obj V)
      (pureTensor M (SheafOfModules.homObj (R := ring Y l) M N)
        ((translation g).inverse.op.obj V) x f) = _ at h
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at h
  rw [P.sigmaTensor_pure, ordinary_pure_map, ordinary_evaluation] at h
  simpa only [ordinary_evaluation, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] using h.symm

end AlgebraicGeometry.ProEtale.NativeFrobenius
