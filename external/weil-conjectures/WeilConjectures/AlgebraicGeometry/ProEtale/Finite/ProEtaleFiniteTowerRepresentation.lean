/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Data.Fintype.Shrink

/-! # Geometric representation of finite coefficient towers

## References

* Stacks Project, Tags 0H7J, 03YW, 098T and 097D
-/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

local instance (Y : Scheme.{u}) (J : Type u) : HasColimitsOfShape (Discrete J) (Over Y) := by
  have : HasColimitsOfShape (Discrete J) Scheme.{u} := inferInstance
  exact ⟨fun F ↦ Over.hasColimit_of_hasColimit_comp_forget F⟩

private theorem testObject_preservesLimit
    {I : Type v} [Category.{w} I] (Y : Scheme.{u}) (D : I ⥤ Profinite.{u}) :
    PreservesLimit D (profiniteToProEtOf Y ⋙ ProEt.forget Y) := by
  let : profiniteToCommRingCatOp.{u}.IsRightAdjoint :=
    profiniteToCommRingCatOp_isRightAdjoint
  let : PreservesLimitsOfSize.{w, v} profiniteToCommRingCatOp.{u} := inferInstance
  let : PreservesLimitsOfSize.{w, v} profiniteToScheme.{u} := by
    unfold profiniteToScheme
    infer_instance
  let : (Over.forget specZ.{u}).IsEquivalence :=
    (Over.equivalenceOfIsTerminal specULiftZIsTerminal).isEquivalence_functor
  let : PreservesLimit D
      ((profiniteToProEt.{u} ⋙ ProEt.forget specZ) ⋙ Over.forget specZ) :=
    inferInstanceAs (PreservesLimit D profiniteToScheme.{u})
  let : PreservesLimit D (profiniteToProEt.{u} ⋙ ProEt.forget specZ) :=
    preservesLimit_of_reflects_of_preserves _ (Over.forget specZ)
  change PreservesLimit D
    ((profiniteToProEt ⋙ ProEt.forget specZ) ⋙ Over.pullback (toSpecZ Y))
  infer_instance

private noncomputable def finiteCopiesOverIso (Y : Scheme.{u}) (E : FintypeCat.{u}) :
    (sigmaConst.obj (Over.mk (𝟙 Y))).obj E ≅
      (ProEt.forget Y).obj ((proEtaleFiniteCopiesFunctor Y).obj E) := by
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
      proEtaleFiniteCopiesFunctor Y ⋙ ProEt.forget Y :=
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
    FintypeCat.toProfinite ⋙ profiniteToProEtOf Y ≅ proEtaleFiniteCopiesFunctor Y := by
  let e := (profinite_test_object_functor Y).2.2.1.some
  apply (Functor.FullyFaithful.whiskeringRight
    (Functor.FullyFaithful.ofFullyFaithful (ProEt.forget Y)) FintypeCat.{u}).preimageIso
  exact e ≪≫ finiteCopiesOverNatIso Y

private noncomputable def finiteRingTowerModel
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    ℕᵒᵖ ⥤ FintypeCat.{u} where
  obj n := FintypeCat.of (Shrink.{u} (Q.obj n))
  map {n m} a := FintypeCat.homMk fun x ↦
    equivShrink.{u} (Q.obj m) ((Q.map a) ((equivShrink.{u} (Q.obj n)).symm x))
  map_id n := by
    apply FintypeCat.hom_ext
    intro x
    change equivShrink.{u} (Q.obj n)
      ((Q.map (𝟙 n)) ((equivShrink.{u} (Q.obj n)).symm x)) = x
    simp
  map_comp {n m k} a b := by
    apply FintypeCat.hom_ext
    intro x
    change equivShrink.{u} (Q.obj k)
      ((Q.map (a ≫ b)) ((equivShrink.{u} (Q.obj n)).symm x)) =
        equivShrink.{u} (Q.obj k) ((Q.map b) ((equivShrink.{u} (Q.obj m)).symm
          (equivShrink.{u} (Q.obj m) ((Q.map a)
            ((equivShrink.{u} (Q.obj n)).symm x)))))
    simp

private noncomputable def finiteRingTowerModelIso
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    finiteRingTowerModel Q ⋙ CategoryTheory.forget FintypeCat.{u} ⋙
        uliftFunctor.{u + 1, u} ≅ Q ⋙ CategoryTheory.forget CommRingCat.{u + 1} :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso
    (Equiv.ulift.trans (equivShrink.{u} (Q.obj n)).symm)) (by
      intro n m a
      ext x
      change (equivShrink.{u} (Q.obj m)).symm
        (equivShrink.{u} (Q.obj m)
          ((Q.map a) ((equivShrink.{u} (Q.obj n)).symm x.down))) = _
      simp only [Equiv.symm_apply_apply]
      rfl)

/-- A finite constant ring tower has a representing diagram and a limit cone which
remains limiting after scheme base change. -/
theorem proEtaleFiniteTower_representableLimit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) [∀ n : ℕᵒᵖ, Finite (Q.obj n)] :
    ∃ (D : ℕᵒᵖ ⥤ Y.ProEt) (c : Cone D),
      Nonempty (IsLimit c) ∧ Nonempty (IsLimit ((proEtaleBaseChange f).mapCone c)) ∧
      Nonempty (D ⋙ (ProEt.topology Y).uliftYoneda.{u + 1} ≅
        Q ⋙ constantSheaf (ProEt.topology Y) CommRingCat.{u + 1} ⋙
          sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})) := by
  let P := finiteRingTowerModel Q ⋙ FintypeCat.toProfinite
  let G := profiniteToProEtOf Y
  let c := G.mapCone (limit.cone P)
  let : PreservesLimit P (G ⋙ ProEt.forget Y) := testObject_preservesLimit Y P
  have hc : IsLimit c :=
    isLimitOfReflects (ProEt.forget Y) (isLimitOfPreserves (G ⋙ ProEt.forget Y) (limit.isLimit P))
  have hfc : IsLimit ((proEtaleBaseChange f).mapCone c) := by
    apply isLimitOfReflects (ProEt.forget X)
    exact isLimitOfPreserves ((G ⋙ ProEt.forget Y) ⋙ Over.pullback f) (limit.isLimit P)
  refine ⟨P ⋙ G, c, ⟨hc⟩, ⟨hfc⟩, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (finiteRingTowerModel Q) (finiteTestObjectIso Y))
      (ProEt.topology Y).uliftYoneda.{u + 1} ≪≫
    Functor.isoWhiskerLeft (finiteRingTowerModel Q)
      (proEtaleFiniteConstantRepresentableIso Y).symm ≪≫
    Functor.isoWhiskerRight (finiteRingTowerModelIso Q)
      (constantSheaf (ProEt.topology Y) (Type (u + 1))) ≪≫
    Functor.isoWhiskerLeft Q
      (constantCommuteCompose (ProEt.topology Y)
        (CategoryTheory.forget CommRingCat.{u + 1})).symm

end AlgebraicGeometry.Scheme
