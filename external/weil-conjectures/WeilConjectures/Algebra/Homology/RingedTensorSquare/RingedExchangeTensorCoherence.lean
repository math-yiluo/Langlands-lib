/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedSquareTensorCompatibility
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
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
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
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
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent

/-!
# Projection-formula coherence for a square of ringed topoi

Source: Stacks Project, Cohomology on Sites, Tags 0E48, 07A4 and 0D6D
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence).
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false in
private theorem tensor_mate_coherence
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D} {K : C ⥤ D} {S : D ⥤ C}
    (adj : F ⊣ R) (adj' : K ⊣ S)
    (T : A × A ⥤ A) (U : B × B ⥤ B) (V : C × C ⥤ C) (W : D × D ⥤ D)
    (tF : T ⋙ F ⟶ (F.prod F) ⋙ U) (tG : T ⋙ G ⟶ (G.prod G) ⋙ V)
    (tH : U ⋙ H ⟶ (H.prod H) ⋙ W) (tK : V ⋙ K ⟶ (K.prod K) ⋙ W)
    (theta : G ⋙ K ≅ F ⋙ H)
    (hc : ∀ P Q : A,
      theta.hom.app (T.obj (P, Q)) ≫ H.map (tF.app (P, Q)) ≫
        tH.app (F.obj P, F.obj Q) =
      K.map (tG.app (P, Q)) ≫ tK.app (G.obj P, G.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (theta.hom.app P) (theta.hom.app Q)))
    (E : B) (Q : A) :
    G.map (adj.homEquiv _ _ (tF.app (R.obj E, Q) ≫
        U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))) ≫
      (mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).app
        (U.obj (E, F.obj Q)) ≫
      S.map (tH.app (E, F.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (𝟙 (H.obj E)) (theta.inv.app Q))) =
    tG.app (R.obj E, Q) ≫
      V.map (CategoryTheory.Prod.mkHom
        ((mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom)).app E)
        (𝟙 (G.obj Q))) ≫
      adj'.homEquiv _ _ (tK.app (S.obj (H.obj E), G.obj Q) ≫
        W.map (CategoryTheory.Prod.mkHom (adj'.counit.app (H.obj E))
          (𝟙 (K.obj (G.obj Q))))) := by
  let ex := (mateEquiv adj adj' (TwoSquare.mk G F K H theta.hom))
  let pi := adj.homEquiv _ _ (tF.app (R.obj E, Q) ≫
    U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))))
  have hex (Z : B) : K.map (ex.app Z) ≫ adj'.counit.app (H.obj Z) =
      theta.hom.app (R.obj Z) ≫ H.map (adj.counit.app Z) :=
    mateEquiv_counit adj adj' (TwoSquare.mk G F K H theta.hom) Z
  dsimp only [Functor.id_obj, Functor.comp_obj]
  apply (adj'.homEquiv _ _).symm.injective
  change (adj'.homEquiv _ _).symm (G.map pi ≫ ex.app _ ≫ S.map _) = _
  rw [adj'.homEquiv_naturality_left_symm,
    adj'.homEquiv_naturality_right_symm]
  rw [adj'.homEquiv_counit, hex]
  simp only [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hn := theta.hom.naturality pi
  dsimp at hn
  dsimp only [Functor.id_obj] at *
  simp only [← Category.assoc]
  rw [hn]
  have hpi : F.map pi ≫ adj.counit.app (U.obj (E, F.obj Q)) =
      tF.app (R.obj E, Q) ≫
        U.map (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q))) := by
    exact (adj.homEquiv _ _).symm_apply_apply _
  simp only [Category.assoc]
  rw [← H.map_comp_assoc, hpi, H.map_comp, Category.assoc]
  have htH := tH.naturality
    (CategoryTheory.Prod.mkHom (adj.counit.app E) (𝟙 (F.obj Q)))
  have htK := tK.naturality
    (CategoryTheory.Prod.mkHom (ex.app E) (𝟙 (G.obj Q)))
  dsimp at htH htK
  rw [reassoc_of% htH, reassoc_of% htK]
  rw [reassoc_of% (hc (R.obj E) Q)]
  simp only [← W.map_comp]
  congr 2
  congr 1
  ext
  · simpa using (hex E).symm
  · simp

private theorem localization_iso_existsUnique
    {A B C : Type*} [Category A] [Category B] [Category C]
    (L : A ⥤ B) (Z : MorphismProperty A) [L.IsLocalization Z]
    (F G : B ⥤ C) (F' G' : A ⥤ C)
    (a : L ⋙ F ≅ F') (b : L ⋙ G ≅ G') (c : F' ≅ G') :
    ∃! t : F ≅ G, ∀ X : A,
      t.hom.app (L.obj X) ≫ b.hom.app X = a.hom.app X ≫ c.hom.app X := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L Z C
  let t := ff.preimageIso (a ≪≫ c ≪≫ b.symm)
  have ht : Functor.whiskerLeft L t.hom = (a ≪≫ c ≪≫ b.symm).hom :=
    ff.map_preimage _
  refine ⟨t, ?_, ?_⟩
  · intro X
    have hx := congr_app ht X
    dsimp at hx
    rw [hx]
    simp
  · intro t' ht'
    apply Iso.ext
    apply ff.map_injective
    ext X
    dsimp
    rw [← cancel_mono (b.hom.app X), ht']
    have hx := congr_app ht X
    dsimp at hx
    rw [hx]
    simp

namespace SheafOfModules

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

private abbrev CornerModules (A : RingedTensorCorner.{u, w}) :=
  SheafOfModules.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

set_option backward.isDefEq.respectTransparency false in
private theorem edge_epsilon_isIso
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (P : CochainComplex (CornerModules A) ℤ)
    (hp : P.IsAcyclicTensorKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) :
    IsIso (e.epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨L, eps, hL, _, _, heps, _⟩ :=
    ringedTopoiDerivedPullback e.inverse e.direct e.adjunction e.algebraic e.ringMap
      e.pullback e.object_eq e.map_eq
  let W := HomotopyCategory.quasiIso (CornerModules A) (.up ℤ)
  have : L.IsLeftDerivedFunctor eps W := hL
  have : e.left.IsLeftDerivedFunctor e.epsilon W := e.isLeftDerived
  let t := Functor.leftDerivedUnique L e.left e.epsilon eps W
  have h := Functor.leftDerivedNatTrans_app e.left L e.epsilon eps W
    (Iso.refl _).hom ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  have heq : t.hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      eps.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      e.epsilon.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) := by
    simpa only [t, Functor.leftDerivedNatIso_hom, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id] using h
  rw [← heq]
  have := heps P hp hf
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem edge_preserves_flat_kflat
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (P : CochainComplex (CornerModules A) ℤ)
    (hp : P.IsAcyclicTensorKFlat) (hf : ∀ n : ℤ, (P.X n).IsFlat) :
    CochainComplex.IsAcyclicTensorKFlat ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ n : ℤ, (((e.pullback.mapHomologicalComplex (.up ℤ)).obj P).X n).IsFlat := by
  have hf' (n : ℤ) : IsFlatOnSite (J := A.topology) (R := A.ring) (P.X n) := by
    let := monoidalCategory A.ring
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso A.ring (P.X n)).symm
      (hf n)
  obtain ⟨hk, ht⟩ := isKFlat_ringedToposPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp) hf'
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro n
  let := monoidalCategory B.ring
  exact ObjectProperty.prop_of_iso (exactFunctor _ _)
    (siteSheafTensorRightIso B.ring _) (ht n)

/-- The canonical ordinary module square applied termwise to a complex.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorSquare.complexComparison
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    g.pullback.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      k.pullback.mapHomologicalComplex (ComplexShape.up ℤ) ≅
    f.pullback.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      h.pullback.mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.mapHomologicalComplex s.modules (ComplexShape.up ℤ)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def edge_composite_epsilon
    {A B C : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (e' : RingedTensorEdge B C) :
    DerivedCategory.Qh ⋙ e.left ⋙ e'.left ⟶
      e.pullback.mapHomotopyCategory (.up ℤ) ⋙
        e'.pullback.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight e.epsilon e'.left ≫
    Functor.whiskerLeft (e.pullback.mapHomotopyCategory (.up ℤ)) e'.epsilon

set_option backward.isDefEq.respectTransparency false in
private noncomputable def square_homotopy_comparison
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    g.pullback.mapHomotopyCategory (.up ℤ) ⋙ k.pullback.mapHomotopyCategory (.up ℤ) ≅
      f.pullback.mapHomotopyCategory (.up ℤ) ⋙ h.pullback.mapHomotopyCategory (.up ℤ) :=
  NatIso.ofComponents
    (fun P ↦ (HomotopyCategory.quotient _ (.up ℤ)).mapIso
      (s.complexComparison.app P.as)) (by
      rintro ⟨P⟩ ⟨Q⟩ ⟨a : P ⟶ Q⟩
      simp only [HomotopyCategory.quot_mk_eq_quotient_map, Functor.comp_map,
        Functor.mapHomotopyCategory_map, Functor.mapIso_hom]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (HomotopyCategory.quotient _ (.up ℤ)).map
        (s.complexComparison.hom.naturality a))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem composite_complex_epsilon
    {A B C : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (e' : RingedTensorEdge B C)
    (P : CochainComplex (CornerModules A) ℤ) :
    e'.left.map (derivedPullbackComplexComparison e.pullback e.left e.epsilon P) ≫
      derivedPullbackComplexComparison e'.pullback e'.left e'.epsilon
        ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
    (e.left ⋙ e'.left).map ((DerivedCategory.quotientCompQhIso (CornerModules A)).inv.app P) ≫
      (edge_composite_epsilon e e').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        (DerivedCategory.quotientCompQhIso (CornerModules C)).hom.app
          ((e'.pullback.mapHomologicalComplex (.up ℤ)).obj
            ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P)) := by
  have factors (D E : RingedTensorCorner.{u, w}) (d : RingedTensorEdge D E)
      (K : CochainComplex (CornerModules D) ℤ) :
      DerivedCategory.Qh.map ((d.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom.app K) =
        𝟙 (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient _ (.up ℤ)).obj
            ((d.pullback.mapHomologicalComplex (.up ℤ)).obj K))) := by
    change DerivedCategory.Qh.map (𝟙 _) = 𝟙 _
    exact CategoryTheory.Functor.map_id _ _
  dsimp only [Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift,
    Functor.comp_obj, HomotopyCategory.quotient, CategoryTheory.Quotient.functor]
  simp only [derivedPullbackComplexComparison, factors,
    Functor.map_comp, edge_composite_epsilon, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map, Category.assoc]
  simp only [← e'.left.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.mapHomotopyCategory, CategoryTheory.Quotient.lift,
    Functor.comp_obj, HomotopyCategory.quotient, CategoryTheory.Quotient.functor]
  simp only [Category.id_comp, Category.comp_id]

private theorem square_transport_cancel_iff
    {C : Type*} [Category C] {A B A' B' D E D' E' : C}
    {i : A ⟶ A'} [Epi i] {j : B ⟶ B'} {q : D ⟶ D'} [Mono q] {r : E ⟶ E'}
    {t : A ⟶ B} {t' : A' ⟶ B'} {a : B' ⟶ D} {b : A' ⟶ E}
    {c : B ⟶ D'} {d : A ⟶ E'} {m : E ⟶ D} {n : E' ⟶ D'}
    (hc : c = j ≫ a ≫ q) (hd : d = i ≫ b ≫ r)
    (ht : i ≫ t' = t ≫ j) (hm : m ≫ q = r ≫ n) :
    (t ≫ c = d ≫ n) ↔ (t' ≫ a = b ≫ m) := by
  simp only [hc, hd, Category.assoc, ← reassoc_of% ht, ← hm]
  rw [cancel_epi]
  simp only [← Category.assoc, cancel_mono]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem square_condition_transport
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (theta : g.left ⋙ k.left ≅ f.left ⋙ h.left)
    (P : CochainComplex (CornerModules Y) ℤ) :
    (theta.hom.app (DerivedCategory.Q.obj P) ≫
        h.left.map (derivedPullbackComplexComparison f.pullback f.left f.epsilon P) ≫
        derivedPullbackComplexComparison h.pullback h.left h.epsilon
          ((f.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
      k.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
        derivedPullbackComplexComparison k.pullback k.left k.epsilon
          ((g.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map (s.complexComparison.hom.app P)) ↔
    (theta.hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
        (edge_composite_epsilon f h).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      (edge_composite_epsilon g k).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((square_homotopy_comparison s).hom.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by
  have hsquare : DerivedCategory.Qh.map
      ((square_homotopy_comparison s).hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        (s.complexComparison.hom.app P)) := rfl
  -- Normalize and cancel in an abstract diagram, avoiding rewrites over the complex types.
  simpa only [Category.assoc, hsquare, Functor.comp_obj] using
    (square_transport_cancel_iff
      (composite_complex_epsilon f h P) (composite_complex_epsilon g k P)
      (theta.hom.naturality ((DerivedCategory.quotientCompQhIso (CornerModules Y)).inv.app P))
      (DerivedCategory.quotientCompQhIso_hom_naturality (s.complexComparison.hom.app P)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The representative square determines the derived commutation isomorphism uniquely.
Proof: use the resolving homotopy subcategory and localization equivalence of
lem-weil-pbc-site-derived-tensor-descent. The specified left-derived counits are
invertible there by uniqueness of left derived functors and the representative
computation in lem-weil-pbc-ringed-topoi-derived-pullback. Successive pullbacks stay
flat K-flat by lem-weil-pbc-ringed-pullback-preserves-kflat; the tensor-right
identification bridges its flatness convention. Compose the two counits on each
route and apply the ordinary square termwise. Full faithfulness of precomposition
along localization gives a unique derived isomorphism. Naturality of the comparison
between Qh and Q, followed by cancellation of its components, gives precisely the
stated complex representative equation. This also proves uniqueness.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
theorem RingedTensorSquare.derivedComparison_existsUnique
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    ∃! theta : g.left ⋙ k.left ≅ f.left ⋙ h.left,
      ∀ (P : CochainComplex (SheafOfModules.{u} ((sheafCompose Y.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj Y.ring)) ℤ),
        P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
        theta.hom.app (DerivedCategory.Q.obj P) ≫
          h.left.map (derivedPullbackComplexComparison f.pullback f.left f.epsilon P) ≫
          derivedPullbackComplexComparison h.pullback h.left h.epsilon
            ((f.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
        k.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
          derivedPullbackComplexComparison k.pullback k.left k.epsilon
            ((g.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (s.complexComparison.hom.app P) := by
  classical
  obtain ⟨P, hP, ⟨M, hM, ⟨fac⟩⟩, _, _⟩ :=
    site_derived_tensor_descent.{u, w, u + 1, w} Y.topology Y.ring
  let V := (HomotopyCategory.quasiIso (CornerModules Y) (.up ℤ)).inverseImage P.ι
  let L := P.ι ⋙ (DerivedCategory.Qh :
    HomotopyCategory (CornerModules Y) (.up ℤ) ⥤ DerivedCategory (CornerModules Y))
  have : M.IsEquivalence := hM
  have : L.IsLocalization V := Functor.IsLocalization.of_iso V fac
  let ag := Functor.whiskerLeft P.ι (edge_composite_epsilon g k)
  let af := Functor.whiskerLeft P.ι (edge_composite_epsilon f h)
  have isocomp {B C : RingedTensorCorner.{u, w}}
      (e : RingedTensorEdge Y B) (e' : RingedTensorEdge B C) :
      IsIso (Functor.whiskerLeft P.ι (edge_composite_epsilon e e')) := by
    apply (NatTrans.isIso_iff_isIso_app _).2
    intro Z
    obtain ⟨hp, hf⟩ := (hP Z.obj).1 Z.property
    obtain ⟨hp', hf'⟩ := edge_preserves_flat_kflat e Z.obj.as hp hf
    have h₁ : IsIso (e.epsilon.app Z.obj) := edge_epsilon_isIso e Z.obj.as hp hf
    have h₂ : IsIso (e'.epsilon.app
        ((e.pullback.mapHomotopyCategory (.up ℤ)).obj Z.obj)) := by
      exact edge_epsilon_isIso e'
        ((e.pullback.mapHomologicalComplex (.up ℤ)).obj Z.obj.as) hp' hf'
    change IsIso (e'.left.map (e.epsilon.app Z.obj) ≫
      e'.epsilon.app ((e.pullback.mapHomotopyCategory (.up ℤ)).obj Z.obj))
    infer_instance
  have : IsIso ag := isocomp g k
  have : IsIso af := isocomp f h
  let m := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft P.ι (square_homotopy_comparison s)) DerivedCategory.Qh
  obtain ⟨theta, ht, hu⟩ := localization_iso_existsUnique L V
    (g.left ⋙ k.left) (f.left ⋙ h.left) _ _ (asIso ag) (asIso af) m
  refine ⟨theta, ?_, ?_⟩
  · intro K hp hf
    apply (square_condition_transport s theta K).2
    exact ht ⟨(HomotopyCategory.quotient _ (.up ℤ)).obj K, (hP _).2 ⟨hp, hf⟩⟩
  · intro theta' ht'
    apply hu theta'
    intro Z
    obtain ⟨hp, hf⟩ := (hP Z.obj).1 Z.property
    exact (square_condition_transport s theta' Z.obj.as).1 (ht' Z.obj.as hp hf)

/-- The specified derived commutation isomorphism, selected by its unique
K-flat representative characterization. Only a uniqueness-determining proof is postponed.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorSquare.derivedComparison
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    g.left ⋙ k.left ≅ f.left ⋙ h.left :=
  Classical.choose s.derivedComparison_existsUnique.exists

/-- The exchange transformation is exactly the mate of the canonical derived square,
using the existing Mathlib mate equivalence (def-weil-pbc-adjunction-mate).
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorSquare.exchange
    (s : RingedTensorSquare Y X Y' X' f g h k) :
    f.right ⋙ g.left ⟶ h.left ⋙ k.right :=
  (mateEquiv f.derivedAdjunction k.derivedAdjunction
    (TwoSquare.mk g.left f.left k.left h.left s.derivedComparison.hom))

/-- The projection map is the adjunct of tensor comparison followed by counit tensor
identity. In particular no projection-formula isomorphism is assumed.
Source: Stacks, Cohomology on Sites, Tags 07A4, 0D6D, 0E48
(blueprint: lem-weil-pbc-ringed-exchange-tensor-coherence). -/
noncomputable def RingedTensorEdge.projection
    {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (a : RingedTensorModel A) (b : RingedTensorModel B)
    (E : DerivedCategory (SheafOfModules.{u} ((sheafCompose B.topology (forget₂ CommRingCat.{u}
      RingCat.{u})).obj B.ring))) (Q : DerivedCategory (SheafOfModules.{u} ((sheafCompose
      A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring))) :
    A.tensor.obj (e.right.obj E, Q) ⟶ e.right.obj (B.tensor.obj (E, e.left.obj Q)) :=
  e.derivedAdjunction.homEquiv _ _
    ((e.tensorComparison a b).hom.app (e.right.obj E, Q) ≫
      B.tensor.map (CategoryTheory.Prod.mkHom (e.derivedAdjunction.counit.app E)
        (𝟙 (e.left.obj Q))))

end SheafOfModules
