/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.Algebra.Homology.Functor

/-!
# K-flat replacements of strict diagrams

Source: Stacks Project, Cohomology on Sites, Tags 077J, 0G7E and 06YY,
via functorial flat resolutions (blueprint: lem-weil-pbc-diagram-kflat-replacements).

A strict diagram of complexes is a functor into cochain complexes. Applying a single
functorial flat resolution preserves all its transition maps. Adding contractible flat
disks in the diagram category makes its augmentation degreewise epimorphic. Module pullback
is specified by its adjunction to the induced module direct image: this characterizes the
usual inverse image followed by extension of scalars.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

namespace CochainComplex

/-- Transpose a strict diagram into a complex in the functor category. -/
private def diagramComplex
    {A I : Type*} [Category A] [HasZeroMorphisms A] [Category I]
    (M : I ⥤ CochainComplex A ℤ) : CochainComplex (I ⥤ A) ℤ where
  X n := M ⋙ HomologicalComplex.eval A (.up ℤ) n
  d n m :=
    { app := fun j ↦ (M.obj j).d n m
      naturality := fun j k a ↦ (M.map a).comm n m }
  shape n m h := by ext j; exact (M.obj j).shape n m h
  d_comp_d' n m k _ _ := by ext j; exact (M.obj j).d_comp_d n m k

/-- Transpose a natural transformation into a chain map. -/
private def diagramComplexMap
    {A I : Type*} [Category A] [HasZeroMorphisms A] [Category I]
    {M N : I ⥤ CochainComplex A ℤ} (f : M ⟶ N) :
    diagramComplex M ⟶ diagramComplex N where
  f n := Functor.whiskerRight f (HomologicalComplex.eval A (.up ℤ) n)
  comm' n m _ := by ext j; exact (f.app j).comm n m

/-- Add the contractible complex with terms `P i ⊞ P (i - 1)`, where `P i` covers
`H.X i`. Its map to `H` is epimorphic in each degree and adding it preserves the
homotopy type and the resolving class of the terms.
Source: Stacks Project, Derived Categories, proof of `lemma-special-direct-system`. -/
private theorem epicification
    {A : Type*} [Category A] [Abelian A]
    (W : ObjectProperty A) [W.IsClosedUnderIsomorphisms]
    (hsum : ∀ {X Y : A}, W X → W Y → W (X ⊞ Y))
    (hcover : ∀ M : A, ∃ (P : A) (p : P ⟶ M), W P ∧ Epi p)
    (E H : CochainComplex A ℤ) (f : E ⟶ H)
    (hflat : ∀ i : ℤ, W (E.X i)) :
    ∃ (F : CochainComplex A ℤ) (g : F ⟶ H) (e : HomotopyEquiv E F),
      (∀ i : ℤ, W (F.X i)) ∧
      (∀ i : ℤ, Epi (g.f i)) ∧ e.hom ≫ g = f := by
  classical
  choose Q p hQ hp using hcover
  let P (i : ℤ) := Q (H.X i)
  let q (i : ℤ) : P i ⟶ H.X i := p (H.X i)
  have hP (i : ℤ) : W (P i) := hQ _
  have hq (i : ℤ) : Epi (q i) := hp _
  let X (i : ℤ) := P i ⊞ P (i - 1)
  let dd (i j : ℤ) : X i ⟶ X j :=
    if hij : i + 1 = j then
      biprod.fst ≫ eqToHom (by congr 1; omega) ≫ biprod.inr
    else 0
  let D : CochainComplex _ ℤ :=
    { X := X
      d := dd
      shape := fun i j hij ↦ dite_eq_right hij
      d_comp_d' := by
        intro i j k hij hjk
        change i + 1 = j at hij
        change j + 1 = k at hjk
        simp [dd, hij, hjk, Category.assoc] }
  let a : D ⟶ H := CochainComplex.ofHom
    (fun i ↦ biprod.desc (q i) (q (i - 1) ≫ H.d (i - 1) i)) (by
      intro i
      have hi : i + 1 - 1 = i := by omega
      apply biprod.hom_ext'
      · simp only [D, dd, dite_eq_left rfl, Category.assoc,
          biprod.inl_fst_assoc, biprod.inr_desc]
        simpa using (eqToHom_naturality
          (fun k ↦ q k ≫ H.d k (i + 1)) hi.symm)
      · simp [D, dd, Category.assoc])
  have ha (i : ℤ) : Epi (a.f i) := by
    have := hq i
    exact epi_of_epi_fac (by simp [a] :
      (biprod.inl : P i ⟶ X i) ≫ a.f i = q i)
  let hh (i j : ℤ) : D.X i ⟶ D.X j :=
    if hij : j + 1 = i then
      biprod.snd ≫ eqToHom (by congr 1; omega) ≫ biprod.inl
    else 0
  have hcontract : Homotopy (𝟙 D) 0 := by
    refine { hom := hh, zero := ?_, comm := ?_ }
    · intro i j hij
      exact dite_eq_right hij
    · intro i
      rw [dNext_eq hh (show (ComplexShape.up ℤ).Rel i (i + 1) by rfl),
        prevD_eq hh (show (ComplexShape.up ℤ).Rel (i - 1) i by change i - 1 + 1 = i; omega)]
      have hi' : i - 1 + 1 = i := by omega
      simp only [D, dd, hh, dite_eq_left rfl, dite_eq_left hi', HomologicalComplex.id_f,
        HomologicalComplex.zero_f, Category.assoc, biprod.inr_snd_assoc,
        biprod.inl_fst_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        add_zero]
      exact (biprod.total (X := P i) (Y := P (i - 1))).symm
  let F := E ⊞ D
  let s : E ⟶ F := biprod.inl
  let g : F ⟶ H := biprod.desc f a
  let e : HomotopyEquiv E F :=
    { hom := s
      inv := biprod.fst
      homotopyHomInvId := Homotopy.ofEq (by simp [s])
      homotopyInvHomId := by
        let h₁ := (hcontract.compRight (biprod.inr : D ⟶ F)).compLeft
          (biprod.snd : F ⟶ D)
        let h₂ := (Homotopy.refl (biprod.fst ≫ s)).add h₁
        exact (Homotopy.ofEq (by simp [s])).trans
          (h₂.symm.trans (Homotopy.ofEq (by
            simpa only [s, Category.id_comp] using biprod.total (X := E) (Y := D)))) }
  refine ⟨F, g, e, ?_, ?_, ?_⟩
  · intro i
    exact ObjectProperty.prop_of_iso _ (HomologicalComplex.biprodXIso E D i).symm
      (hsum (hflat i) (hsum (hP i) (hP (i - 1))))
  · intro i
    have := ha i
    exact epi_of_epi_fac (HomologicalComplex.biprod_inr_desc_f f a i)
  · simp [e, s, g]

set_option synthInstance.maxSize 1024 in
/-- Strict diagrams admit objectwise K-flat resolutions with flat terms.
Source: Stacks Project, Tags 077J and 06YS, functorial resolution construction
(blueprint: lem-weil-pbc-diagram-kflat-replacements).

Proof:
1. Use the functorial flat cover constructed in the proof of Tag 06YS. Its reduced
   left resolution gives a functor on all cochain complexes, with a natural
   quasi-isomorphism to the identity. Compose the given diagram with this functor.
2. Its values are filtered colimits of bounded-above flat complexes, hence K-flat
   with flat terms. Functoriality retains the transition maps and all equations.
3. Transpose the diagrams to complexes of diagrams. The flat cover also acts on
   diagrams by composition. In each degree take such a cover of the target term;
   adjacent covers form a contractible disk complex mapping degreewise epimorphically
   to the target. Add this disk complex to the resolution and its augmentation.
4. Evaluation preserves the resulting homotopy equivalence, flat terms and
   epimorphisms. The original augmentation factors through the new one and the
   homotopy equivalence, proving that the new augmentation is a quasi-isomorphism. -/
theorem exists_diagram_isKFlatResolution
    {C : Type u} [SmallCategory C] (T : GrothendieckTopology C)
    (R : Sheaf T CommRingCat.{u}) {J : Type u} [SmallCategory J]
    (M : J ⥤ CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) :
    ∃ (P : J ⥤ CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)) ℤ) (p : P ⟶ M),
      (∀ j : J, (P.obj j).IsAcyclicTensorKFlat) ∧
      (∀ (j : J) (q : ℤ), SheafOfModules.IsFlat ((P.obj j).X q)) ∧
      (∀ j : J, QuasiIso (p.app j)) ∧
      (∀ (j : J) (q : ℤ), Epi ((p.app j).f q)) := by
  classical
  let A := ringedSiteModules.{u, u, u, u}
    ((sheafCompose T (forget₂ CommRingCat RingCat)).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfi (R := R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  have := SheafOfModules.hasExactColimits_int_kfi R
  let := SheafOfModules.hasFunctorialFlatResolution_kfi R
  have (X : A) : PreservesColimitsOfShape ℤ ((curriedTensor A).flip.obj X) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft X)
      (NatIso.ofComponents (fun Y ↦ β_ X Y) (by intros; simp [curriedTensor]))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ A))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ A).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  have hflat (j : J) (n : ℤ) :
      ObjectProperty.flat ((Λ.resolutionFunctor.obj (M.obj j)).X n) := by
    have := CochainComplex.closedUnderColimitsOfShape_flat A ℤ
    let c := Λ.colimitOfShapeResolutionFunctorObj (M.obj j)
    exact ObjectProperty.prop_of_isColimit _
      (isColimitOfPreserves (HomologicalComplex.eval A (.up ℤ) n) c.isColimit)
      (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))
  let E := diagramComplex (M ⋙ Λ.resolutionFunctor)
  let H := diagramComplex M
  let f : E ⟶ H := diagramComplexMap
    (Functor.whiskerLeft M Λ.resolutionNatTrans ≫ M.rightUnitor.hom)
  let W : ObjectProperty (J ⥤ A) := fun N ↦ ∀ j : J, ObjectProperty.flat (N.obj j)
  have : W.IsClosedUnderIsomorphisms :=
    ⟨fun e h j ↦ ObjectProperty.prop_of_iso _ (e.app j) (h j)⟩
  have hsum {X Y : J ⥤ A} (hX : W X) (hY : W Y) : W (X ⊞ Y) := by
    intro j
    have : PreservesBinaryBiproducts ((evaluation J A).obj j) :=
      preservesBinaryBiproducts_of_preservesBinaryProducts _
    exact ObjectProperty.prop_of_iso _
      (((evaluation J A).obj j).mapBiprod X Y).symm
      (flat_biprod_kfi (hX j) (hY j))
  have hcover (N : J ⥤ A) : ∃ (P : J ⥤ A) (p : P ⟶ N), W P ∧ Epi p := by
    let P := N ⋙ Λ.F ⋙ ObjectProperty.flat.ι
    let p : P ⟶ N :=
      { app := fun j ↦ Λ.π.app (N.obj j)
        naturality := fun j k a ↦ Λ.π.naturality (N.map a) }
    refine ⟨P, p, fun j ↦ (Λ.F.obj (N.obj j)).property, ?_⟩
    exact (NatTrans.epi_iff_epi_app p).2 (fun j ↦ inferInstance)
  obtain ⟨F, g, e, hF, hepi, hcomp⟩ :=
    epicification W hsum hcover E H f (fun n j ↦ hflat j n)
  let p : F.asFunctor ⟶ M :=
    { app := fun j ↦
        { f := fun n ↦ (g.f n).app j
          comm' := fun n m _ ↦ NatTrans.congr_app (g.comm n m) j }
      naturality := by
        intro j k a
        ext n : 1
        exact (g.f n).naturality a }
  refine ⟨F.asFunctor, p, ?_, ?_, ?_, ?_⟩
  · intro j
    let ev := (evaluation J A).obj j
    have hk := Λ.kFlat_resolutionFunctor_obj hι (M.obj j)
    have hkF : (HomologicalComplex.quasiIso A (.up ℤ)).kFlat (F.asFunctor.obj j) := by
      rw [← HomotopyCategory.kFlat_quotient_obj_iff] at hk ⊢
      exact ObjectProperty.prop_of_iso _
        (HomotopyCategory.isoOfHomotopyEquiv (ev.mapHomotopyEquiv e)) hk
    intro Z hZ
    let U := tensorRight (F.asFunctor.obj j)
    have hz : QuasiIso (0 : (0 : CochainComplex A ℤ) ⟶ Z) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
    have hmap : QuasiIso (U.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) := hkF.2 _ hz
    have htzero : (U.obj (0 : CochainComplex A ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (U.map_isZero (isZero_zero _))
    exact fun i ↦ (exactAt_iff_of_quasiIsoAt
      (U.map (0 : (0 : CochainComplex A ℤ) ⟶ Z)) i).1 (htzero i)
  · exact fun j n ↦ (hF n j).2
  · intro j
    let ev := (evaluation J A).obj j
    have : QuasiIso ((ev.mapHomotopyEquiv e).hom) := (ev.mapHomotopyEquiv e).quasiIso_hom
    have heq : (ev.mapHomotopyEquiv e).hom ≫ p.app j =
        Λ.resolutionNatTrans.app (M.obj j) := by
      ext n : 1
      exact NatTrans.congr_app (congrArg (fun h ↦ h.f n) hcomp) j
    have : QuasiIso ((ev.mapHomotopyEquiv e).hom ≫ p.app j) := by
      rw [heq]
      infer_instance
    exact quasiIso_of_comp_left (ev.mapHomotopyEquiv e).hom (p.app j)
  · intro j n
    have := hepi n
    exact ((evaluation J A).obj j).map_epi (g.f n)

end CochainComplex
