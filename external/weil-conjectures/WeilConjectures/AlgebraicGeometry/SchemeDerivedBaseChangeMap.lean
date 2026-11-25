/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedAdjoint
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.TensorPullbackKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs

/-!
 # The derived base-change morphism of O-modules

Source: Stacks Project, Cohomology, Remark 08HY; equivalently the unit construction
of Lemma 02N7 (blueprint: def-pc-derived-base-change-map).
-/

@[expose] public section

set_option autoImplicit false
universe uBC wBC uAdj wAdj
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option synthInstance.maxSize 2048 in
-- The sheaf tensor and total-complex instances require larger search terms and budget.
/-- Derived pullback is left adjoint to derived direct image, bifunctorially on the
unbounded derived categories of O-modules. Source: Stacks, Tag 079W
(blueprint: def-pc-derived-base-change-map).
Proof: nonempty_derivedPullbackAdjunction (lem-pc-ringed-spaces-derived-adjoint)
gives existence of an unbounded adjunction. To specify the canonical one, the
module tensor pullback is left adjoint to module direct image by
lem-pc-module-pullback-adjunction. Their left and right derived functors are the
recorded derivedPullback and schemeDerivedDirectImage. Apply the abstract derived
adjunction theorem lem-pc-derived-adjoint-functors (Tag 09T5); its functoriality
clause gives naturality in both arguments. K-flat and K-injective resolutions give
existence on all objects, so the adjunction is unbounded. The displayed identity
pins its Hom equivalence to the canonical underived tensor-pullback adjunction,
the supplied left-derived counit and the recorded right-derived unit, as in
lem-pc-derived-adjoint-functors. It rules out arbitrary adjunction twists. -/
theorem exists_schemeDerivedAdjunction {X Y : Scheme.{uAdj}} (f : X ⟶ Y)
    [HasDerivedCategory.{wAdj} (SheafOfModules.{uAdj} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wAdj} (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace))]
    [hAdd : (Scheme.Modules.tensorPullback f).Additive]
    (ε : DerivedCategory.Qh ⋙ derivedPullback f ⟶
      (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh
          (C := SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)))
    (hε : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))) :
    ∃ adj : derivedPullback f ⊣ schemeDerivedDirectImage f,
      ∀ (M : HomotopyCategory
          (SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ))
        (K : HomotopyCategory
          (SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ))
        (a : ((Scheme.Modules.tensorPullback f).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj M ⟶ K),
        adj.homEquiv (DerivedCategory.Qh.obj M) (DerivedCategory.Qh.obj K)
            (ε.app M ≫ DerivedCategory.Qh.map a) =
          (DerivedCategory.Qh
            (C := SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace))).map
            (((Classical.choose
              (Scheme.Modules.exists_tensorPullbackAdjunction f)).mapHomotopyCategory
                (ComplexShape.up ℤ)).homEquiv M K a) ≫
            (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app K
      := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let A := SheafOfModules.{uAdj} (moduleRings Y.toRingedSpace)
  let B := SheafOfModules.{uAdj} (moduleRings X.toRingedSpace)
  let : Abelian A := inferInstanceAs (Abelian A)
  let : Abelian B := inferInstanceAs (Abelian B)
  have := SheafOfModules.isMonoidal_W Y.sheaf
  let : MonoidalCategory A := SheafOfModules.monoidalCategory Y.sheaf
  let : SymmetricCategory A := SheafOfModules.symmetricCategory Y.sheaf
  have : MonoidalPreadditive A := Classical.choice (SheafOfModules.tensorClosed Y.sheaf).1
  let : MonoidalClosed A := Classical.choice (SheafOfModules.tensorClosed Y.sheaf).2.1
  have : CategoryTheory.Limits.HasColimitsOfSize.{0, 0} A :=
    CategoryTheory.Limits.hasColimitsOfSizeShrink.{0, 0, uAdj, uAdj} A
  have : Abelian.HasFunctorialFlatResolution A := schemeModule_hasFunctorialFlatResolution Y
  have : IsGrothendieckAbelian.{uAdj} A :=
    SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  let G : A ⥤ B := Scheme.Modules.tensorPullback f
  have : G.Additive := hAdd
  have : G.PreservesKFlatQuasiIso := by
    refine ⟨?_⟩
    intro P Q hP hQ s hs
    have toIsKFlat (P : CochainComplex A ℤ)
        (hP : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat P) :
        CochainComplex.IsKFlatTensor (R := Y.sheaf) P := by
      intro F hF
      have h := (HomotopyCategory.kFlat_iff_preserves_acyclic
        ((HomotopyCategory.quotient A (.up ℤ)).obj P)).mp
          ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp
        (h _ ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic F).mpr hF)).2
    exact tensorPullback_quasiIso_of_isKFlat f s (toIsKFlat P hP) (toIsKFlat Q hQ) hs
  change DerivedCategory.Qh ⋙ derivedPullback f ⟶
    G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh at ε
  have : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso A (.up ℤ)) := hε
  have : (DerivedCategory.Qh (C := A)).IsLocalization
      (HomotopyCategory.quasiIso A (.up ℤ)) := inferInstance
  have : (DerivedCategory.Qh (C := B)).IsLocalization
      (HomotopyCategory.quasiIso B (.up ℤ)) := inferInstance
  have : (derivedPullback f ⋙ schemeDerivedDirectImage f).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight ε (schemeDerivedDirectImage f))
      (HomotopyCategory.quasiIso A (.up ℤ)) :=
    (HomotopyCategory.quasiIso A (.up ℤ)).localizerMorphismKFlat
      |>.isLeftDerivedFunctor_comp_of_isLeftDerivabilityStructure ε
        (fun P ↦ G.derives_kFlat
          |>.isIso_of_isLeftDerivedFunctor ε P) (schemeDerivedDirectImage f)
  let β := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit
  have : (schemeDerivedDirectImage f ⋙ derivedPullback f).IsRightDerivedFunctor
      (Functor.whiskerRight β (derivedPullback f) ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso B (.up ℤ)) :=
    (HomotopyCategory.KInjectives.localizerMorphism B)
      |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure β
        (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives _)
          |>.isIso_of_isRightDerivedFunctor β I) (derivedPullback f)
  let adj : G.mapHomotopyCategory (.up ℤ) ⊣
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ) :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    |>.mapHomotopyCategory (.up ℤ)
  let d := adj.derived (L₁ := DerivedCategory.Qh (C := A))
    (L₂ := DerivedCategory.Qh (C := B)) (G' := derivedPullback f)
    (F' := schemeDerivedDirectImage f) (HomotopyCategory.quasiIso A (.up ℤ))
    (HomotopyCategory.quasiIso B (.up ℤ)) ε β
  refine ⟨d, ?_⟩
  intro M K a
  have fac := adj.derivedη_fac_app (L₁ := DerivedCategory.Qh (C := A))
    (L₂ := DerivedCategory.Qh (C := B)) (G' := derivedPullback f)
    (F' := schemeDerivedDirectImage f) (HomotopyCategory.quasiIso A (.up ℤ)) ε β M
  change d.unit.app (DerivedCategory.Qh.obj M) ≫
      (schemeDerivedDirectImage f).map (ε.app M ≫ DerivedCategory.Qh.map a) = _
  change d.unit.app (DerivedCategory.Qh.obj M) ≫
      (schemeDerivedDirectImage f).map (ε.app M) = _ at fac
  calc
    _ = (d.unit.app (DerivedCategory.Qh.obj M) ≫
        (schemeDerivedDirectImage f).map (ε.app M)) ≫
        (schemeDerivedDirectImage f).map (DerivedCategory.Qh.map a) := by
      rw [Functor.map_comp, Category.assoc]
    _ = ((DerivedCategory.Qh (C := A)).map (adj.unit.app M) ≫ β.app _) ≫
        (schemeDerivedDirectImage f).map (DerivedCategory.Qh.map a) :=
      congrArg (fun b ↦ b ≫ _) fac
    _ = (DerivedCategory.Qh (C := A)).map (adj.unit.app M) ≫
        ((DerivedCategory.Qh (C := A)).map ((RingedSpace.moduleDirectImage
          f.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ) |>.map a) ≫ β.app K) := by
      erw [Category.assoc, ← β.naturality a]
      rfl
    _ = _ := by
      erw [← Category.assoc, ← DerivedCategory.Qh.map_comp]
      rfl



/-- The canonical base-change map for a commutative square of schemes. In particular
apply this to the chosen fibre product, or to the cartesian square obtained by
restricting its upper row to an open W and its inverse image W'.

This is the counit description of Stacks, Remark 08HY: transpose under Lf'^* ⊣ Rf'_*
the composite Lf'^* Lg^* Rf_* E ≅ Lg'^* Lf^* Rf_* E → Lg'^* E.
It is equivalently the unit description of Lemma 02N7 in the node: transpose under
Lg^* ⊣ Rg_* the unit map followed by direct-image composition comparisons.
Those comparisons are the mates of the same derived-pullback composition comparisons.
The functor comparisons below are selected from their left-derived universal property,
not arbitrary isomorphisms. The adjunction Hom equivalences are pinned to the same
left-derived counits as these comparisons and to the recorded right-derived units, via
`exists_schemeDerivedAdjunction`; no independent adjunction choice is allowed.
Source: Stacks, cohomology.tex, Remark 08HY and Lemma 02N7
(blueprint: def-pc-derived-base-change-map). -/
def schemeDerivedBaseChangeMap
    [∀ Y : Scheme.{uBC},
      HasDerivedCategory.{wBC} (SheafOfModules.{uBC} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{uBC}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g) (E : schemeDerivedCategory X) :
    (derivedPullback g).obj ((schemeDerivedDirectImage f).obj E) ⟶
      (schemeDerivedDirectImage f').obj ((derivedPullback g').obj E) :=
  (Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f')
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f')
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f'))).homEquiv _ _
    (((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) f' g).hom.app
        ((schemeDerivedDirectImage f).obj E) ≫
      eqToHom (congrArg (fun k =>
        (derivedPullback k).obj ((schemeDerivedDirectImage f).obj E)) h.symm) ≫
      ((Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) g' f).inv.app
        ((schemeDerivedDirectImage f).obj E) ≫
      (derivedPullback g').map
        ((Classical.choose (exists_schemeDerivedAdjunction f
          (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
          ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
          ((Classical.choose (Classical.choose_spec
            (Classical.choose_spec exists_derivedPullbackComposition))) f))).counit.app E))

end AlgebraicGeometry
end
