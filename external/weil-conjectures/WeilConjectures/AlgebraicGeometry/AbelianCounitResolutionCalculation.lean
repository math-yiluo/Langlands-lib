/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AbelianCounitCocycleCalculation
import WeilConjectures.AlgebraicGeometry.AbelianResolutionComparisonEvaluation

/-! # The abelian counit on a resolution

Source: Stacks Project, Tags 01F7 and 06XR.
(blueprint: new-abelian-counit-resolution-calculation)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
attribute [local instance] AlgebraicGeometry.Scheme.Modules.instAddCommGroupH
attribute [local irreducible] abelianResolutionIso
attribute [local irreducible] Functor.rightDerivedObjIsoOfResolution
attribute [local irreducible] siteSectionsObjIso

attribute [local instance] cocycle_pushforward_additive

/-- Fix the standard abelian injective resolution before composing functors.
Source: Stacks, Tag 06XR. -/
@[irreducible]
def standardAbelianResolution (X : Scheme.{u}) (F : X.Modules) :
    InjectiveResolution ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj F) :=
  injectiveResolution _

/-- Forget the augmentation of a module resolution. Source: Stacks, Tag 03FD. -/
@[irreducible]
def forgottenAugmentation (X : Scheme.{u}) {F : X.Modules} (I : InjectiveResolution F) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.toSheaf (moduleRings X.toRingedSpace)) (.up ℕ) 0).inv.app F ≫
    ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).mapHomologicalComplex (.up ℕ)).map I.ι

/-- Exact forgetting preserves the resolution augmentation. Source: Stacks, Tag 03FD. -/
instance forgottenAugmentation_quasiIso (X : Scheme.{u}) {F : X.Modules}
    (I : InjectiveResolution F) : QuasiIso (forgottenAugmentation X I) := by
  delta forgottenAugmentation
  exact quasiIso_comp _ _

/-- Compare the forgotten module resolution with a concrete abelian injective resolution.
Source: Stacks, Tags 03FD and 013P. -/
@[irreducible]
def forgottenResolutionMap (X : Scheme.{u}) {F : X.Modules} (I : InjectiveResolution F) :=
  InjectiveResolution.descOfQuasiIso (𝟙 _)
    (standardAbelianResolution X F)
    (forgottenAugmentation X I)

/-- Sections of a direct image are sections on the source, using the top-open equality.
Source: Stacks, Tag 01F7. -/
def abelianPushforwardSectionsIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    abelianPushforward f ⋙ abelianSections Y ≅
      abelianSections X :=
  NatIso.ofComponents
    (fun G ↦ G.obj.mapIso (eqToIso (by simp) :
      op (f ⁻¹ᵁ (⊤ : Y.Opens)) ≅ op (⊤ : X.Opens)))
    (by intro G G' g; exact (g.hom.naturality _).symm)

/-- The exact inverse image of the forgotten source augmentation.
Source: Stacks, Tags 01F7 and 013P. -/
@[irreducible]
def counitSourceAugmentation {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (J : InjectiveResolution ((pushforward f).obj F)) :=
  (HomologicalComplex.singleMapHomologicalComplex (invImage f) (.up ℕ) 0).inv.app
      ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).obj ((pushforward f).obj F)) ≫
    ((invImage f).mapHomologicalComplex (.up ℕ)).map (forgottenAugmentation Y J)

/-- Exact inverse image preserves the forgotten augmentation. Source: Stacks, Tag 01F7. -/
instance counitSourceAugmentation_quasiIso {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (J : InjectiveResolution ((pushforward f).obj F)) :
    QuasiIso (counitSourceAugmentation f F J) := by
  delta counitSourceAugmentation
  exact quasiIso_comp _ _

/-- Lift the abelian counit from the inverse image of the forgotten source resolution.
Source: Stacks, Tag 013P. -/
@[irreducible]
def counitResolutionLift {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (J : InjectiveResolution ((pushforward f).obj F)) :=
  InjectiveResolution.descOfQuasiIso (coeff f (𝟙 ((pushforward f).obj F)))
    (standardAbelianResolution X F)
    (counitSourceAugmentation f F J)

/-- The adjoint of the counit lift, before taking sections.
Source: Stacks, Tag 01F7. -/
@[irreducible]
def counitResolutionAdjoint {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (J : InjectiveResolution ((pushforward f).obj F)) :
    ((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).mapHomologicalComplex
      (.up ℕ)).obj J.cocomplex ⟶
      ((abelianPushforward f).mapHomologicalComplex (.up ℕ)).obj
        (standardAbelianResolution X F).cocomplex :=
  (NatTrans.mapHomologicalComplex
    (abelianAdjunction f).unit (.up ℕ)).app
      (((SheafOfModules.toSheaf (moduleRings Y.toRingedSpace)).mapHomologicalComplex (.up ℕ)).obj
        J.cocomplex) ≫
    ((abelianPushforward f).mapHomologicalComplex (.up ℕ)).map
      (counitResolutionLift f F J)

/-- The section complex map that computes the abelian counit.
Source: Stacks, Tag 01F7. -/
@[irreducible]
def counitSectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    (J : InjectiveResolution ((pushforward f).obj F)) :
    ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      ((abelianSections X).mapHomologicalComplex (.up ℕ)).obj
        (standardAbelianResolution X F).cocomplex :=
  ((abelianSections Y).mapHomologicalComplex (.up ℕ)).map (counitResolutionAdjoint f F J) ≫
    (NatTrans.mapHomologicalComplex (abelianPushforwardSectionsIso f).hom (.up ℕ)).app
      (standardAbelianResolution X F).cocomplex

/-- The Ext counit is represented by the adjoint lift on abelian section complexes.
Source: Stacks Project, Tag 01F7, and Tag 06XR, injective-resolution Ext computation.
(blueprint: new-abelian-counit-resolution-calculation)

Proof: The forgotten augmentation of J is an acyclic resolution by 03FD. Its inverse
image remains a resolution because inverse image is exact. Lift coeff(f,identity)
from this resolution to the standard abelian injective resolution R of F, using
counitResolutionLift. Compute Ext by cocycles in Hom from the constant integer
sheaf into these resolutions. Applying inverse image to such a cocycle and composing
with the lift computes exact inverse image on Ext followed by the counit. The
constant-source comparison is constIso(f).symm. Evaluation on the integer generator
identifies these Hom complexes with sections: adjunction sends the lifted cocycle
to counitResolutionAdjoint, and restriction along the equality f-inverse(Y)=X is
abelianPushforwardSectionsIso. These identifications commute with differentials,
boundaries and the standard comparison from Ext to derived sections. Passing to
homology gives the asserted equality. The source acyclic-resolution comparison is
abelianResolutionIso(Y,J). On the target, the acyclic-resolution comparison
is the standard abelian-resolution comparison followed by the inverse of sections
of forgottenResolutionMap(X,I). Sections of this map is a quasi-isomorphism by
03FD and 015E; composing with its homology map cancels that inverse. Therefore
the target expression below is precisely the comparison computed on R.
This is independent of any module replacement K or quasi-isomorphism into K. The
same calculation includes degree zero, zero modules and empty schemes. -/
theorem abelian_counit_resolution_calculation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (J : InjectiveResolution ((pushforward f).obj F))
    (I : InjectiveResolution F) (p : ℕ) (x : H ((pushforward f).obj F) p) :
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
      (counitSectionMap f F J)) ((abelianResolutionIso Y J p).hom x) =
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
      (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
        (forgottenResolutionMap X I)))
      ((abelianResolutionIso X I p).hom (Sheaf.H.map (coeff f (𝟙 ((pushforward f).obj F))) p
        (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
          ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p x))) := by
  have hL : counitSourceAugmentation f F J ≫ counitResolutionLift f F J =
      (CochainComplex.single₀ _).map (coeff f (𝟙 ((pushforward f).obj F))) ≫
        (standardAbelianResolution X F).ι := by
    delta counitResolutionLift
    exact InjectiveResolution.descOfQuasiIso_commutes _ _ _
  have hs : ∀ G, (abelianPushforwardSectionsIso f).hom.app G = G.obj.map
      (eqToHom (by simp) : op (f ⁻¹ᵁ (⊤ : Y.Opens)) ⟶ op (⊤ : X.Opens)) := by
    intro G
    rfl
  simp only [counitSourceAugmentation, forgottenAugmentation] at hL
  simp only [Category.assoc] at hL
  have hc := abelian_counit_cocycle_calculation f ((pushforward f).obj F) F J
    (coeff f (𝟙 ((pushforward f).obj F)))
    (standardAbelianResolution X F) (counitResolutionLift f F J) hL
    (abelianPushforwardSectionsIso f) hs p x
  have hφ : forgottenAugmentation X I ≫ forgottenResolutionMap X I =
      (standardAbelianResolution X F).ι := by
    delta forgottenResolutionMap
    simp only [InjectiveResolution.descOfQuasiIso_commutes,
      CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [forgottenAugmentation, Category.assoc] at hφ
  have hz := abelian_resolution_comparison_evaluation X F I
    (standardAbelianResolution X F) (forgottenResolutionMap X I) hφ p
    (Sheaf.H.map (coeff f (𝟙 ((pushforward f).obj F))) p
      (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p x))
  unfold counitSectionMap counitResolutionAdjoint
  exact hc.trans hz.symm

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
