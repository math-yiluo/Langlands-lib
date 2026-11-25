/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectPackageOnSiteSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Adjunction.Triple
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# The open-immersion piece of the projection formula

Source: Weil conjectures blueprint, proper base change, lemma 1269;
Stacks Project, Tags 03DI, 03DJ, 03EL, 06YQ and 07A4
(blueprint: lemma-internal-adjunction-two-exchange-formulas).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C}

private theorem localizedUnit_isIso {Z : Scheme.{u}} {X : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    IsIso (localizedModuleAdjunctionIndependent R (ProEt.mk j)).unit := by
  let U := ProEt.mk j
  let A := (sheafCompose (ProEt.topology Z)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let a := localizedModuleAdjunctionIndependent R U
  let b := SheafOfModules.overPushforwardOverAdj (R := A) U
  have : (Over.forget U).Full := by
    constructor
    intro V V' f
    refine ⟨Over.homMk f ?_, rfl⟩
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono j).1
    exact (MorphismProperty.Over.w (f ≫ V'.hom)).trans
      (MorphismProperty.Over.w V.hom).symm
  have : IsIso (Over.forgetAdjStar U).unit := inferInstance
  have : IsIso b.counit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [← isIso_iff_of_reflects_iso _
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)]
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    change IsIso (M.val.presheaf.map ((Over.forgetAdjStar U).unit.app V.unop).op)
    infer_instance
  let triple : Adjunction.Triple _ _ _ := ⟨a, b⟩
  exact triple.isIso_unit_iff_isIso_counit.mpr inferInstance

private theorem localizedDerivedUnit_isIso {Z X : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j]
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    IsIso (localizedModuleDerivedAdjunction R (ProEt.mk j)).unit := by
  let U := ProEt.mk j
  let adj := localizedModuleDerivedAdjunction R U
  letI := localizedUnit_isIso j R
  have hQ (P : CochainComplex (Mod (R.over U)) ℤ) :
      IsIso (adj.unit.app (DerivedCategory.Q.obj P)) := by
    have hP : IsIso
        (((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex (.up ℤ)).unit.app
          P) := by
      have hn : ∀ n : ℤ, IsIso
          ((((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex (.up ℤ)).unit.app
            P).f n) := fun n ↦ inferInstanceAs
        (IsIso ((localizedModuleAdjunctionIndependent R U).unit.app (P.X n)))
      exact HomologicalComplex.Hom.isIso_of_components _
    have hu : adj.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map
          (((localizedModuleAdjunctionIndependent R U).mapHomologicalComplex (.up ℤ)).unit.app
            P) ≫
          (localizedModuleRestriction R U).mapDerivedCategoryFactors.inv.app _ ≫
            (localizedModuleRestriction R U).mapDerivedCategory.map
              ((localizedModuleExtension R U).mapDerivedCategoryFactors.inv.app P) := by
      simp only [adj, localizedModuleDerivedAdjunction, Adjunction.localization_unit_app]
      rfl
    rw [hu]
    infer_instance
  have h (M : Der (R.over U)) : IsIso (adj.unit.app M) :=
    (NatTrans.isIso_app_iff_of_iso adj.unit (DerivedCategory.Q.objObjPreimageIso M)).mp
      (hQ (DerivedCategory.Q.objPreimage M))
  exact NatIso.isIso_of_isIso_app adj.unit

private theorem tensor_sheafification_naturality
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1})
    [(J.W.inverseImage (PresheafOfModules.toPresheaf.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)).IsMonoidal] :
    let := monoidalCategory R
    ∀ (A B X Y : SheafOfModules.{u + 1} ((sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (f : A ⟶ B) (g : X ⟶ Y),
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification B Y).hom =
      (tensorObjIsoSheafification A X).hom ≫
        (PresheafOfModules.sheafification.{u + 1} (𝟙 _)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  dsimp only
  intro A B X Y f g
  let S := PresheafOfModules.sheafification.{u + 1}
    (R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (𝟙 _)
  let c := asIso (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
      (𝟙 _)).counit
  have hf := c.inv.naturality f
  have hg := c.inv.naturality g
  change f ≫ c.inv.app B = c.inv.app A ≫ S.map f.val at hf
  change g ≫ c.inv.app Y = c.inv.app X ≫ S.map g.val at hg
  change (f ⊗ₘ g) ≫ ((c.inv.app B ⊗ₘ c.inv.app Y) ≫
    Functor.LaxMonoidal.μ S B.val Y.val) =
    ((c.inv.app A ⊗ₘ c.inv.app X) ≫ Functor.LaxMonoidal.μ S A.val X.val) ≫
      S.map (f.val ⊗ₘ g.val)
  rw [← Category.assoc, tensorHom_comp_tensorHom, hf, hg,
    ← tensorHom_comp_tensorHom, Category.assoc, Functor.LaxMonoidal.μ_natural,
    Category.assoc]
  rfl

private theorem naturality_comp {D : Type*} [Category* D]
    {A B C A' B' C' : D} {f : A ⟶ A'} {g : B ⟶ B'} {h : C ⟶ C'}
    {s : A ⟶ B} {s' : A' ⟶ B'} {t : B ⟶ C} {t' : B' ⟶ C'}
    (hs : f ≫ s' = s ≫ g) (ht : g ≫ t' = t ≫ h) :
    f ≫ (s' ≫ t') = (s ≫ t) ≫ h := by
  rw [← Category.assoc, hs, Category.assoc, ht, Category.assoc]

private theorem naturality_inv {D : Type*} [Category* D]
    {A B A' B' : D} (i : A ≅ B) (j : A' ≅ B')
    {f : A ⟶ A'} {g : B ⟶ B'} (h : f ≫ j.hom = i.hom ≫ g) :
    g ≫ j.inv = i.inv ≫ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

private theorem extension_tensor_natural
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1}) (U : C) :
    let := isMonoidal_W_independentCoefficients R
    let : HasSheafify (J.over U) AddCommGrpCat.{u + 1} :=
      hasSheafify_coefficientUniverse.{u + 1, u, u + 1} (J := J.over U)
    let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
      wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1} (J := J.over U)
    let := isMonoidal_W_independentCoefficients (R.over U)
    let := monoidalCategory R
    let : MonoidalCategory (SheafOfModules.{u + 1}
      (((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) :=
      monoidalCategory (R.over U)
    let A := (sheafCompose J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
    let L := localizedModuleExtension R U
    let V := localizedModuleRestriction R U
    ∃ e : ∀ (G : SheafOfModules.{u + 1} (A.over U))
      (F : SheafOfModules.{u + 1} A), L.obj (G ⊗ V.obj F) ≅ L.obj G ⊗ F,
      ∀ (G H : SheafOfModules.{u + 1} (A.over U))
        (F E : SheafOfModules.{u + 1} A) (a : G ⟶ H) (b : F ⟶ E),
        L.map (a ⊗ₘ V.map b) ≫ (e H E).hom =
          (e G F).hom ≫ (L.map a ⊗ₘ b) := by
  let := isMonoidal_W_independentCoefficients R
  let : HasSheafify (J.over U) AddCommGrpCat.{u + 1} :=
    hasSheafify_coefficientUniverse.{u + 1, u, u + 1} (J := J.over U)
  let : (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    wEqualsLocallyBijective_coefficientUniverse.{u + 1, u, u + 1} (J := J.over U)
  let := isMonoidal_W_independentCoefficients (R.over U)
  let := monoidalCategory R
  let := monoidalCategory (R.over U)
  let A := (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let : MonoidalCategory (SheafOfModules.{u + 1} (A.over U)) :=
    monoidalCategory (R.over U)
  let L := localizedModuleExtension R U
  let V := localizedModuleRestriction R U
  obtain ⟨e⟩ := ringedSlice_extension_tensor.{u + 1, u + 1, u} J R U
  refine ⟨fun G F ↦ L.mapIso (tensorObjIsoSheafification (R := R.over U) G (V.obj F)) ≪≫
    e.app (G, F) ≪≫ (tensorObjIsoSheafification (R := R) (L.obj G) F).symm, ?_⟩
  intro G H F E a b
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  have h₁ := congrArg L.map (tensor_sheafification_naturality (R.over U)
    G H (V.obj F) (V.obj E) a (V.map b))
  have h₂ := e.hom.naturality (X := (G, F)) (Y := (H, E)) (a, b)
  have h₃ := tensor_sheafification_naturality R (L.obj G) (L.obj H) F E (L.map a) b
  simp only [Functor.map_comp] at h₁
  simp only [Functor.comp_map, Functor.prod_map, MonoidalCategory.tensor_map] at h₂
  exact naturality_comp h₁ (naturality_comp h₂
    (naturality_inv (tensorObjIsoSheafification (R := R) (L.obj G) F)
      (tensorObjIsoSheafification (R := R) (L.obj H) E) h₃))

private theorem extension_total_iso (R : Sheaf J CommRingCat.{u + 1}) (U : C)
    (P : CochainComplex (Mod (R.over U)) ℤ) (Q : CochainComplex (Mod R) ℤ) :
    Nonempty (((localizedModuleExtension R U).mapHomologicalComplex (.up ℤ)).obj
        ((total (R.over U)).obj
          (P, ((localizedModuleRestriction R U).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      (total R).obj
        (((localizedModuleExtension R U).mapHomologicalComplex (.up ℤ)).obj P, Q)) := by
  classical
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory (R.over U)
  letI : MonoidalCategory (SheafOfModules.{u + 1}
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over U)) :=
    SheafOfModules.monoidalCategory (R.over U)
  let L := localizedModuleExtension R U
  let V := localizedModuleRestriction R U
  haveI : L.IsLeftAdjoint := (localizedModuleAdjunctionIndependent R U).isLeftAdjoint
  let LC := L.mapHomologicalComplex (.up ℤ)
  let VC := V.mapHomologicalComplex (.up ℤ)
  obtain ⟨e, he⟩ := extension_tensor_natural J R U
  let T := (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj P).obj
    (VC.obj Q)
  haveI : L.PreservesTotalComplex T (.up ℤ) := fun _ ↦ inferInstance
  let t := (HomologicalComplex₂.mapTotalIso L T (.up ℤ)).symm
  let f :
      (((L.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj T) ≅
      (((curriedTensor _).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
        (LC.obj P)).obj Q :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ e (P.X p) (Q.X q)) (by
          intro q q' hq
          change (e (P.X p) (Q.X q)).hom ≫
            whiskerLeft (L.obj (P.X p)) (Q.d q q') =
            L.map (whiskerLeft (P.X p) (V.map (Q.d q q'))) ≫
              (e (P.X p) (Q.X q')).hom
          have hh := he (P.X p) (P.X p) (Q.X q) (Q.X q') (𝟙 _) (Q.d q q')
          rw [L.map_id, id_tensorHom, id_tensorHom] at hh
          exact hh.symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (P.X p) (Q.X q)).hom ≫
          whiskerRight (L.map (P.d p p')) (Q.X q) =
          L.map (whiskerRight (P.d p p') (V.obj (Q.X q))) ≫
            (e (P.X p') (Q.X q)).hom
        have hh := he (P.X p) (P.X p') (Q.X q) (Q.X q) (P.d p p') (𝟙 _)
        rw [V.map_id, tensorHom_id, tensorHom_id] at hh
        exact hh.symm)
  exact ⟨t ≪≫ HomologicalComplex₂.total.mapIso f (.up ℤ)⟩

end SheafOfModules
