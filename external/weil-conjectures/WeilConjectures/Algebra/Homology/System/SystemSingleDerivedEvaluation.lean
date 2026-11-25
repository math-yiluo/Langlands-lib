/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtensionBasic
public import WeilConjectures.Algebra.Homology.System.SystemSingleDerivedExtension
public import WeilConjectures.Algebra.Homology.System.SystemScalarDerivedExtension
public import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
public import WeilConjectures.Algebra.Homology.System.SystemDerivedTransition

/-! # Derived evaluation of singleton extension

Source: Zheng, Construction 4.1; Stacks 03D7 and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ} (h : m ≤ n)

/-- Exact localization of the identity agrees with the identity cochain model.
Source: functoriality of localization
(blueprint: lem-pur-system-single-derived-evaluation). -/
def systemSingleIdentityFactors :
    (DerivedCategory.Q (C := systemLevel B n)) ⋙ 𝟭 _ ≅
      (𝟭 (systemLevel B n)).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Iso.refl _

/-- The singleton comparison's right square is the localized actual transition.
Source: Zheng 4.1 (blueprint: lem-pur-system-single-derived-evaluation).
Proof: the identity functor and its factorization have identity components, so this
is precisely the representative formula for the strict derived transition. -/
theorem systemSingleDerivedSquare_rep (K : CochainComplex (StrictRingSystem B) ℤ) :
    ((Functor.rightUnitor (derivedSystemEvaluation B n)).hom ≫
      systemDerivedTransition B h).app (DerivedCategory.Q.obj K) ≫
        (systemRestriction B h).mapDerivedCategory.map
          ((systemEvaluation B m).mapDerivedCategoryFactors.hom.app K) ≫
        (systemRestriction B h).mapDerivedCategoryFactors.hom.app
          (((systemEvaluation B m).mapHomologicalComplex (.up ℤ)).obj K) =
    (𝟭 (DerivedCategory (systemLevel B n))).map
        ((systemEvaluation B n).mapDerivedCategoryFactors.hom.app K) ≫
      (systemSingleIdentityFactors B (n := n)).hom.app
        (((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        (((Functor.rightUnitor (systemEvaluation B n)).hom ≫
          strictSystemTransition B h).mapHomologicalComplex (.up ℤ) |>.app K) := by
  have hu : (((Functor.rightUnitor (systemEvaluation B n)).hom ≫
      strictSystemTransition B h).mapHomologicalComplex (.up ℤ)).app K =
      ((strictSystemTransition B h).mapHomologicalComplex (.up ℤ)).app K := by
    apply HomologicalComplex.hom_ext
    intro i
    rfl
  dsimp only [NatTrans.comp_app, Functor.rightUnitor_hom_app, systemSingleIdentityFactors,
    Iso.refl_hom, NatTrans.id_app, Functor.id_map]
  erw [Category.id_comp, Category.id_comp, hu]
  exact systemDerivedTransition_rep B h K

/-- The ordinary singleton comparison is the mate at the ordinary unit.
Source: Zheng 4.1 (blueprint: lem-pur-system-single-derived-evaluation).
Proof: use the ordinary transpose formula with the identity map; its transpose
under the singleton adjunction is its unit. -/
theorem systemSingleOrdinaryUnitSquare (P : systemLevel B n) :
    (systemTensorAdj S B h).homEquiv _ _ ((systemSingleBelow S T B n h).inv.app P) =
      (systemSingleAdjunction S T B n).unit.app P ≫
        ((systemSingleFunctor S T B n).obj P).transition h := by
  have ht := systemSingleTranspose S T B n h P
    ((systemSingleFunctor S T B n).obj P) (𝟙 _)
  have hi : StrictRingSystem.Hom.app (𝟙 ((systemSingleFunctor S T B n).obj P)) m =
      𝟙 (((systemSingleFunctor S T B n).obj P).level m) := rfl
  erw [hi, Category.comp_id,
    (systemSingleAdjunction S T B n).homEquiv_id] at ht
  exact ht

/-- Evaluating derived singleton extension below n is the derived scalar tensor.
Source: Zheng 4.1; Stacks 06YT and 0FND
(blueprint: lem-pur-system-single-derived-evaluation). -/
def systemSingleDerivedBelow (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) :
    (systemSingleDerivedExtension B n S T).derived ⋙ derivedSystemEvaluation B m ≅
      systemDerivedTensor S B h :=
  derivedExtensionEvaluationIso (systemSingleDerivedExtension B n S T)
    (systemScalarModelExtension (S (B.map (homOfLE h).op)))
    (𝟭 (systemLevel B n)) (systemEvaluation B m) (𝟭 _) (systemSingleIdentityFactors B (n := n))
    ((Functor.rightUnitor (derivedSystemEvaluation B n)).hom ≫ systemDerivedTransition B h)
    ((Functor.rightUnitor (systemEvaluation B n)).hom ≫ strictSystemTransition B h)
    (systemSingleDerivedSquare_rep B h)
    (Functor.leftUnitor (systemTensor S B h) ≪≫ (systemSingleBelow S T B n h).symm)
    (systemSingleOrdinaryUnitSquare S T B h)
    (systemLevel_kFlatResolution B n) (fun _ hP ↦ hP.1)

/-- The below-level derived tensor comparison preserves the two actual Hom transposes.
Source: Zheng 4.1; Stacks 0FND
(blueprint: lem-pur-system-single-derived-evaluation).
Proof: it is the inverse of the mate of the strict derived transition, so the general
mate-transpose identity gives exactly the displayed equation. -/
theorem systemSingleDerivedTranspose (P : DerivedCategory (systemLevel B n))
    (M : DerivedCategory (StrictRingSystem B))
    (f : (systemSingleDerivedExtension B n S T).derived.obj P ⟶ M) :
    (systemDerivedTensorAdj S B h).homEquiv P ((derivedSystemEvaluation B m).obj M)
      ((systemSingleDerivedBelow B h S T).inv.app P ≫
        (derivedSystemEvaluation B m).map f) =
    (systemSingleDerivedExtension B n S T).adjunction.homEquiv P M f ≫
      (systemDerivedTransition B h).app M := by
  have hh := derivedExtensionEvaluationIso_transpose (systemSingleDerivedExtension B n S T)
    (systemScalarModelExtension (S (B.map (homOfLE h).op)))
    (𝟭 (systemLevel B n)) (systemEvaluation B m) (𝟭 _) (systemSingleIdentityFactors B (n := n))
    ((Functor.rightUnitor (derivedSystemEvaluation B n)).hom ≫ systemDerivedTransition B h)
    ((Functor.rightUnitor (systemEvaluation B n)).hom ≫ strictSystemTransition B h)
    (systemSingleDerivedSquare_rep B h)
    (Functor.leftUnitor (systemTensor S B h) ≪≫ (systemSingleBelow S T B n h).symm)
    (systemSingleOrdinaryUnitSquare S T B h)
    (systemLevel_kFlatResolution B n) (fun _ hP ↦ hP.1) P M f
  dsimp only [systemSingleDerivedBelow, systemScalarModelExtension, systemDerivedTensorAdj,
    Functor.id_map, Functor.id_obj, NatTrans.comp_app, Functor.rightUnitor_hom_app] at hh ⊢
  exact hh.trans (congrArg
    (fun g ↦ (systemSingleDerivedExtension B n S T).adjunction.homEquiv P M f ≫ g)
    (Category.id_comp ((systemDerivedTransition B h).app M)))

/-- Derived singleton extension vanishes above its input level, without boundedness
conditions. Source: Zheng 4.1; Stacks 06YT
(blueprint: lem-pur-system-single-derived-evaluation).
Proof: represent P by a flat-term K-flat resolution. The derived extension is then
its ordinary extension, whose terms at m are zero. Exact evaluation and localization
preserve that zero complex. Transport vanishing back through the resolution and
canonical comparison isomorphisms. -/
theorem systemSingleDerivedAbove (m n : ℕ) (hm : n < m)
    (P : DerivedCategory (systemLevel B n)) :
    IsZero ((derivedSystemEvaluation B m).obj
      ((systemSingleDerivedExtension B n S T).derived.obj P)) := by
  let K := DerivedCategory.Q.objPreimage P
  obtain ⟨L, f, hL, hf⟩ := systemLevel_kFlatResolution B n K
  have := hf
  let F := systemSingleDerivedExtension B n S T
  have := F.computes L hL
  let V := systemEvaluation B m
  let e : (derivedSystemEvaluation B m).obj (F.derived.obj P) ≅
      DerivedCategory.Q.obj ((V.mapHomologicalComplex (.up ℤ)).obj
        ((F.ordinary.mapHomologicalComplex (.up ℤ)).obj L)) :=
    (V.mapDerivedCategory.mapIso (F.derived.mapIso
      (asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso P))).symm ≪≫
      V.mapDerivedCategory.mapIso (asIso (F.comparison.app L)) ≪≫
      V.mapDerivedCategoryFactors.app ((F.ordinary.mapHomologicalComplex (.up ℤ)).obj L)
  have hz : IsZero ((V.mapHomologicalComplex (.up ℤ)).obj
      ((F.ordinary.mapHomologicalComplex (.up ℤ)).obj L)) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro i
    exact (systemSingleLevelAbove S B n (L.X i) hm).eq_of_src _ _
  exact (Functor.map_isZero DerivedCategory.Q hz).of_iso e

end SheafOfModules
