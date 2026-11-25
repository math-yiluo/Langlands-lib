/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all WeilConjectures.Algebra.Homology.LocallyFreeDerivedHom

/-! # Derived additive coyoneda and evaluation from a single complex -/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {A : Type v} [Category.{u} A] [Abelian A]
  [IsGrothendieckAbelian.{u} A] [HasDerivedCategory.{u} A]
  [HasDerivedCategory.{u} AddCommGrpCat.{u}]

private noncomputable def coyonedaInjectiveIso (P : A)
    (K : CochainComplex A ℤ) [K.IsKInjective] :
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj K).homology 0 ≅
      (preadditiveCoyoneda.obj
        (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj P)))).obj
          (DerivedCategory.Q.obj K) :=
  ((abstract_singleHomologyEquiv P K).trans
    (abstract_kInjectiveQuotientEquiv _ K)).toAddCommGrpIso

omit [IsGrothendieckAbelian.{u} A] [HasDerivedCategory.{u} AddCommGrpCat.{u}] in
private theorem coyonedaInjectiveIso_naturality (P : A)
    (K L : CochainComplex A ℤ) [K.IsKInjective] [L.IsKInjective] (f : K ⟶ L) :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).map f) 0 ≫
        (coyonedaInjectiveIso P L).hom =
      (coyonedaInjectiveIso P K).hom ≫
        (preadditiveCoyoneda.obj
          (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj P)))).map
            (DerivedCategory.Q.map f) := by
  ext x
  change abstract_kInjectiveQuotientEquiv _ L
      (abstract_singleHomologyEquiv P L (HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).map f) 0 x)) =
    abstract_kInjectiveQuotientEquiv _ K (abstract_singleHomologyEquiv P K x) ≫
      DerivedCategory.Q.map f
  have h := abstract_singleHomologyEquiv_naturality P P K L (𝟙 P) f
    (((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).map f)
    (by intro i a; exact (Category.id_comp _).symm) x
  rw [h]
  simpa only [Functor.map_id, Category.id_comp] using
    abstract_kInjectiveQuotientEquiv_naturality
      ((CochainComplex.singleFunctor A 0).obj P)
      ((CochainComplex.singleFunctor A 0).obj P) K L (𝟙 _) f
      (abstract_singleHomologyEquiv P K x)

private noncomputable def coyonedaDerivedZeroOnComplexes (P : A) :
    DerivedCategory.Q ⋙ preadditiveCoyoneda.obj
        (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj P))) ≅
      DerivedCategory.Q ⋙ (preadditiveCoyoneda.obj (op P)).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ 0 := by
  let H := preadditiveCoyoneda.obj (op P)
  let F := DerivedCategory.Q ⋙ preadditiveCoyoneda.obj
    (op (DerivedCategory.Q.obj ((CochainComplex.singleFunctor A 0).obj P)))
  let G := DerivedCategory.Q ⋙ H.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ 0
  let I := locallyFreeResolution (A := A)
  let η := locallyFreeResolutionUnit (A := A)
  have (K : CochainComplex A ℤ) : QuasiIso (η.app K) :=
    abstract_resolution_unit_quasiIso K
  have hFapp (K : CochainComplex A ℤ) :
      IsIso ((Functor.whiskerRight η F).app K) := by
    change IsIso ((preadditiveCoyoneda.obj _).map (DerivedCategory.Q.map (η.app K)))
    infer_instance
  have hF : IsIso (Functor.whiskerRight η F) := NatIso.isIso_of_isIso_app _
  have hGapp (K : CochainComplex A ℤ) :
      IsIso ((Functor.whiskerRight η G).app K) := by
    change IsIso ((DerivedCategory.homologyFunctor _ 0).map
      (H.rightDerivedFunctor.map (DerivedCategory.Q.map (η.app K))))
    infer_instance
  have hG : IsIso (Functor.whiskerRight η G) := NatIso.isIso_of_isIso_app _
  have hI (K : CochainComplex A ℤ) : (I.obj K).IsKInjective :=
    abstract_resolution_isKInjective K
  have hcmp (K : CochainComplex A ℤ) :
      IsIso ((locallyFreeDerivedComparison H).app (I.obj K)) :=
    locallyFreeDerivedComparison_isIso H (I.obj K)
  let a : F ≅ I ⋙ F := asIso (Functor.whiskerRight η F)
  let b : G ≅ I ⋙ G := asIso (Functor.whiskerRight η G)
  let c : I ⋙ F ≅ I ⋙ G := NatIso.ofComponents
    (fun K ↦ (coyonedaInjectiveIso P (I.obj K)).symm ≪≫
      asIso ((locallyFreeDerivedComparison H).app (I.obj K))) (by
        intro K L f
        change F.map (I.map f) ≫ _ = _ ≫ G.map (I.map f)
        simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom]
        rw [← cancel_epi (coyonedaInjectiveIso P (I.obj K)).hom]
        simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        dsimp only [F, Functor.comp_map]
        rw [← coyonedaInjectiveIso_naturality P (I.obj K) (I.obj L) (I.map f)]
        simp only [Category.assoc, Iso.hom_inv_id_assoc]
        exact (locallyFreeDerivedComparison H).naturality (I.map f))
  exact a ≪≫ c ≪≫ b.symm

/-- Additive coyoneda derived by K-injective resolutions computes maps from a single
complex, naturally on the unbounded derived category and in every integer degree.
Source: Stacks Project, Tags 08JJ and 0A8Z.
(auxiliary; not a blueprint node)

Proof: on K-injective complexes, zeroth homology of the ordinary Hom complex is the
additive group of homotopy classes, and localization identifies these with derived maps.
The comparison to the right derived functor is invertible on K-injectives.  Apply these
natural identifications after a functorial K-injective resolution and descend through
localization.  Commutation of right derivation with shift and the cohomology shift
isomorphism give every integer degree. -/
theorem derived_coyoneda_evaluation (P : A) (n : ℤ) : Nonempty
    (shiftFunctor (DerivedCategory A) n ⋙
        preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj P)) ≅
      (preadditiveCoyoneda.obj (op P)).rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor _ n) := by
  let H := preadditiveCoyoneda.obj (op P)
  let T := preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj P))
  let R := H.rightDerivedFunctor
  let e : T ≅ R ⋙ DerivedCategory.homologyFunctor _ 0 :=
    Localization.liftNatIso DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
      (DerivedCategory.Q ⋙ T) (DerivedCategory.Q ⋙ R ⋙
        DerivedCategory.homologyFunctor _ 0) T (R ⋙ DerivedCategory.homologyFunctor _ 0)
      (coyonedaDerivedZeroOnComplexes P)
  exact ⟨Functor.isoWhiskerLeft (shiftFunctor _ n) e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (R.commShiftIso n) (DerivedCategory.homologyFunctor _ 0) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft R ((DerivedCategory.homologyFunctor _ 0).isoShift n)⟩

end CategoryTheory
