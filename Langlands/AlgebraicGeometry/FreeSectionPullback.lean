import Langlands.AlgebraicGeometry.SectionPullback
import Langlands.AlgebraicGeometry.LocalSectionBasis
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

namespace Langlands.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} {I : Type u} [Fintype I]

local instance : DecidableEq I := Classical.decEq I

local instance (U : X.Opens) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).Additive where
  map_add := by intros; rfl

variable {M : X.Modules}

/-- Restrict a global finite free trivialization to the over-site of an open. -/
def globalFreeOverIso (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (U : X.Opens) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U :=
  SheafOfModules.mapFreeIso (SheafOfModules.overFunctor X.ringCatSheaf U) I
    (Iso.refl _) ≪≫ (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso e

/-- The basis on sections over any open induced by a global finite free trivialization. -/
def globalSectionBasis (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (U : X.Opens) : Module.Basis I Γ(X, U) Γ(M, U) :=
  localSectionBasis (globalFreeOverIso e U) (Over.mk (𝟙 U))

@[simp]
lemma globalSectionBasis_apply
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (U : X.Opens) (i : I) :
    globalSectionBasis e U i =
      e.hom.val.app (op U) ((SheafOfModules.freeSection i).val (op U)) := by
  change localSectionBasis (globalFreeOverIso e U) (Over.mk (𝟙 U)) i = _
  calc
    _ = (localBasisSection (globalFreeOverIso e U) i).val (op (Over.mk (𝟙 U))) :=
      localSectionBasis_apply (globalFreeOverIso e U) (Over.mk (𝟙 U)) i
    _ = _ := ?_
  have h := SheafOfModules.ιFree_mapFreeIso_hom
    (SheafOfModules.overFunctor X.ringCatSheaf U) I (Iso.refl _) i
  exact congrArg
    (fun k => e.hom.val.app (op U) (k.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))) h

/-- Mathlib's canonical free-sheaf comparison for a scheme morphism. -/
def freePullbackIso (f : Y ⟶ X) (I : Type u) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj
      (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
        SheafOfModules.free (R := Y.ringCatSheaf) I := by
  have : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (AlgebraicGeometry.Scheme.Modules.pushforward f).IsRightAdjoint
  exact SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

/-- The actual pullback of a supplied global finite free trivialization. -/
def globalFreePullbackIso (f : Y ⟶ X)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M) :
    SheafOfModules.free (R := Y.ringCatSheaf) I ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj M :=
  (freePullbackIso f I).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso e

omit [Fintype I] in
/-- The free-sheaf comparison sends the actual pulled-back generator to the generator. -/
lemma sectionPullback_freeSection (f : Y ⟶ X) (U : X.Opens) (i : I) :
    (freePullbackIso f I).hom.val.app (op (f ⁻¹ᵁ U))
        (sectionPullback f (SheafOfModules.free I) U
          ((SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op U))) =
      (SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op (f ⁻¹ᵁ U)) := by
  have : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  have : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (AlgebraicGeometry.Scheme.Modules.pushforward f).IsRightAdjoint
  let p := SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I
  let adj := AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f
  have hu :
      adj.unit.app (SheafOfModules.unit X.ringCatSheaf) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward f).map
          (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom)
  have h :
      SheafOfModules.ιFree i ≫ adj.unit.app (SheafOfModules.free I) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward f).map p.hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward f).map (SheafOfModules.ιFree i) := by
    have hn :
        SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫ adj.unit.app (SheafOfModules.free I) =
        adj.unit.app (SheafOfModules.unit X.ringCatSheaf) ≫
          (AlgebraicGeometry.Scheme.Modules.pushforward f).map
            ((AlgebraicGeometry.Scheme.Modules.pullback f).map (SheafOfModules.ιFree i)) :=
      adj.unit.naturality (SheafOfModules.ιFree i)
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
    change adj.unit.app _ ≫ (AlgebraicGeometry.Scheme.Modules.pushforward f).map
      ((SheafOfModules.pullback f.toRingCatSheafHom).map (SheafOfModules.ιFree i) ≫ p.hom) = _
    rw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom]
    rw [Functor.map_comp, ← Category.assoc, hu]
  have hh := congrArg (fun k => k.val.app (op U) (1 : Γ(X, U))) h
  change p.hom.val.app (op (f ⁻¹ᵁ U))
      (sectionPullback f (SheafOfModules.free I) U
        ((SheafOfModules.freeSection i).val (op U))) =
    (SheafOfModules.ιFree (R := Y.ringCatSheaf) i).val.app (op (f ⁻¹ᵁ U))
      ((f.app U).hom 1) at hh
  rw [map_one] at hh
  exact hh

/-- The actual unit section map carries the source basis to the constructed target basis. -/
lemma sectionPullback_globalSectionBasis (f : Y ⟶ X)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (U : X.Opens) (i : I) :
    sectionPullback f M U (globalSectionBasis e U i) =
      globalSectionBasis (globalFreePullbackIso f e) (f ⁻¹ᵁ U) i := by
  let t := sectionPullback f (SheafOfModules.free (R := X.ringCatSheaf) I) U
    ((SheafOfModules.freeSection i).val (op U))
  have hg : t = (freePullbackIso f I).inv.val.app (op (f ⁻¹ᵁ U))
      ((SheafOfModules.freeSection i).val (op (f ⁻¹ᵁ U))) := by
    have hid := congrArg (fun k => k.val.app (op (f ⁻¹ᵁ U)) t)
      (freePullbackIso f I).hom_inv_id
    exact hid.symm.trans
      (congrArg (fun x => (freePullbackIso f I).inv.val.app (op (f ⁻¹ᵁ U)) x)
        (sectionPullback_freeSection f U i))
  calc
    _ = ((AlgebraicGeometry.Scheme.Modules.pullback f).map e.hom).app (f ⁻¹ᵁ U) t :=
      (congrArg (sectionPullback f M U) (globalSectionBasis_apply e U i)).trans
        (sectionPullback_naturality f e.hom U _)
    _ = _ := (congrArg
      (fun x => ((AlgebraicGeometry.Scheme.Modules.pullback f).map e.hom).app (f ⁻¹ᵁ U) x)
      hg).trans (globalSectionBasis_apply (globalFreePullbackIso f e) (f ⁻¹ᵁ U) i).symm

/-- Matrices in the constructed pulled-back basis are obtained by mapping coefficients. -/
theorem globalSectionBasis_pullback_toMatrix (f : Y ⟶ X)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (U : X.Opens) (a : End M) :
    (LinearMap.toMatrix (globalSectionBasis e U) (globalSectionBasis e U)
      (sectionEndomorphism M U a)).map (f.app U).hom =
    LinearMap.toMatrix
      (globalSectionBasis (globalFreePullbackIso f e) (f ⁻¹ᵁ U))
      (globalSectionBasis (globalFreePullbackIso f e) (f ⁻¹ᵁ U))
      (sectionEndomorphism _ (f ⁻¹ᵁ U) ((AlgebraicGeometry.Scheme.Modules.pullback f).map a)) :=
  sectionPullback_toMatrix f M U _ _ (sectionPullback_globalSectionBasis f e U) a

/-- Determinant transport with a target basis constructed from the actual free pullback. -/
theorem globalSectionBasis_pullback_determinant (f : Y ⟶ X)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ≅ M)
    (U : X.Opens) {ι : Type*} [Fintype ι] (a : ι → End M) :
    MvPolynomial.map (f.app U).hom
      (Langlands.Shimura.HodgeDeterminant.polynomial (globalSectionBasis e U)
        (fun i => sectionEndomorphism M U (a i))) =
    Langlands.Shimura.HodgeDeterminant.polynomial
      (globalSectionBasis (globalFreePullbackIso f e) (f ⁻¹ᵁ U))
      (fun i => sectionEndomorphism _ (f ⁻¹ᵁ U)
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map (a i))) :=
  sectionPullback_determinant f M U _ _ (sectionPullback_globalSectionBasis f e U) a

end Langlands.Scheme.Modules
