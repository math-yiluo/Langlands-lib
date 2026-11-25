/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.ProperBaseChange.ResolvingRepresentativeWhiskeringSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The fixed tensor comparison normalized on flat representatives.

## References

* Stacks Project, Cohomology on Sites, Tags 06YP, 06YS, 06YU and 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso
  proEtaleRingDerivedPullbackFactors CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
  HomologicalComplex₂.total
private theorem resolutionTensor_quasiIso
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (P : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P)
    {H M : CochainComplex (proEtaleRingModules Z RZ) ℤ} (q : H ⟶ M)
    (hq : QuasiIso q) : QuasiIso (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Z
        RZ).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).map (Prod.mkHom (𝟙 P) q)))
            := by
  obtain ⟨_, ht⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated RZ
  have hp := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1
  have hh := (ht P hp hP.2).1 H M q hq |>.1
  let T := (proEtaleOrdinaryTensor Z RZ).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  have he : ((Functor.uncurry.obj ((proEtaleOrdinaryTensor Z RZ).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).map (Prod.mkHom (𝟙 P) q)) =
            (T.obj P).map q := by
    change (T.map (𝟙 P)).app H ≫ (T.obj P).map q = _
    rw [T.map_id, NatTrans.id_app, Category.id_comp]
  rw [he]
  exact hh

private theorem resolutionRepresentative_whiskering
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :
    Nonempty (((Functor.whiskeringLeft
      ((proEtaleFlatRepresentatives Z RZ).FullSubcategory ×
        (proEtaleFlatRepresentatives Z RZ).FullSubcategory)
      (DerivedCategory (proEtaleRingModules Z RZ) ×
        DerivedCategory (proEtaleRingModules Z RZ))
      (DerivedCategory (proEtaleRingModules Z RZ))).obj
      (((proEtaleFlatRepresentatives Z RZ).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives Z RZ).ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let A := proEtaleRingModules Z RZ
  let PR := proEtaleFlatRepresentatives Z RZ
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun K ↦ PR K.as
  have hres : ∀ K : HomotopyCategory A (.up ℤ),
      ∃ (V : H.FullSubcategory) (q : V.obj ⟶ K), HomotopyCategory.quasiIso A (.up ℤ) q := by
    intro K
    obtain ⟨P, q, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := RZ) K.as
    have hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology Z) (R := RZ)
        (P.X n) := fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso RZ (P.X n)).symm (hf n)
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hp, hflat⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map q, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
  obtain ⟨ff⟩ := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory A)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  exact ⟨ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory A)).mapIso
    (NatIso.prod (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (Functor.isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))⟩

private theorem extendFixedTensorComparison
    {K D : Type*} [Category* K] [Category* D]
    (Q : K ⥤ D) (W : MorphismProperty K) [Q.IsLocalization W]
    (PR : ObjectProperty K) (t : K × K ⥤ K) (a : D × D ⥤ D)
    (r : (PR.ι.prod PR.ι) ⋙ t ⋙ Q ≅ ((PR.ι ⋙ Q).prod (PR.ι ⋙ Q)) ⋙ a)
    (ff : ((Functor.whiskeringLeft (PR.FullSubcategory × PR.FullSubcategory)
      (D × D) D).obj ((PR.ι ⋙ Q).prod (PR.ι ⋙ Q))).FullyFaithful)
    (p : PR.FullSubcategory)
    (hinv : W.IsInvertedBy (((Functor.const K).obj p.obj).prod' (𝟭 K) ⋙ t ⋙ Q)) :
    ∃ d : ((Functor.const K).obj p.obj).prod' (𝟭 K) ⋙ t ⋙ Q ≅
        Q ⋙ ((Functor.const D).obj (Q.obj p.obj)).prod' (𝟭 D) ⋙ a,
      ∀ V : PR.FullSubcategory, d.hom.app V.obj = r.hom.app (p, V) := by
  let T := ((Functor.const K).obj p.obj).prod' (𝟭 K) ⋙ t
  let G := ((Functor.const D).obj (Q.obj p.obj)).prod' (𝟭 D) ⋙ a
  let H := T ⋙ Q
  let Hb := Localization.lift H hinv Q
  let φ : Q ⋙ Hb ≅ H := Localization.fac H hinv Q
  let e₀ : PR.ι ⋙ H ≅ PR.ι ⋙ Q ⋙ G := NatIso.ofComponents
    (fun V ↦ r.app (p, V)) (by
      intro V V' g
      have hn := r.hom.naturality (X := (p, V)) (Y := (p, V'))
        (Prod.mkHom (𝟙 p) g)
      dsimp only [Functor.comp_map, Functor.prod_map] at hn
      rw [PR.ι.map_id p, Q.map_id] at hn
      exact hn)
  let e := Functor.isoWhiskerLeft PR.ι φ ≪≫ e₀
  let e₂ : ((PR.ι ⋙ Q).prod (PR.ι ⋙ Q)) ⋙ (CategoryTheory.Prod.snd D D ⋙ Hb) ≅
      ((PR.ι ⋙ Q).prod (PR.ι ⋙ Q)) ⋙ (CategoryTheory.Prod.snd D D ⋙ G) :=
    NatIso.ofComponents (fun V ↦ e.app V.2) (by
      intro V V' g
      exact e.hom.naturality g.2)
  let η := ff.preimageIso e₂
  let d : H ≅ Q ⋙ G := φ.symm ≪≫
    Functor.isoWhiskerLeft Q
      (Functor.isoWhiskerLeft (((Functor.const D).obj (Q.obj p.obj)).prod' (𝟭 D)) η)
  refine ⟨d, ?_⟩
  intro V
  have hh := congr_app (ff.map_preimage e₂.hom) (p, V)
  change η.hom.app (Q.obj p.obj, Q.obj V.obj) = φ.hom.app V.obj ≫
    r.hom.app (p, V) at hh
  change φ.inv.app V.obj ≫ η.hom.app (Q.obj p.obj, Q.obj V.obj) = _
  rw [hh, ← Category.assoc, φ.inv_hom_id_app, Category.id_comp]

/-- The fixed tensor comparison normalized on flat representatives. -/
theorem proEtale_fixed_tensor_representative_comparison
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel Z RZ)
    (P : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P) :
    ∃ d : ((Functor.const _).obj P).prod' (𝟭 _) ⋙ (Functor.uncurry.obj ((proEtaleOrdinaryTensor Z
        RZ).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))) ⋙
        DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ ((Functor.const _).obj (DerivedCategory.Q.obj P)).prod' (𝟭 _) ⋙
        a.tensor,
      ∀ (H : CochainComplex (proEtaleRingModules Z RZ) ℤ)
        (hH : proEtaleFlatRepresentatives Z RZ H),
        d.hom.app H = a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩) := by
  obtain ⟨ff⟩ := resolutionRepresentative_whiskering Z RZ
  obtain ⟨d, hd⟩ := extendFixedTensorComparison
    DerivedCategory.Q (HomologicalComplex.quasiIso (proEtaleRingModules Z RZ) (.up ℤ))
    (proEtaleFlatRepresentatives Z RZ) ((Functor.uncurry.obj ((proEtaleOrdinaryTensor Z
        RZ).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))))
    a.tensor a.representative ff ⟨P, hP⟩ (by
      intro M M' q hq
      exact Localization.inverts DerivedCategory.Q
        (HomologicalComplex.quasiIso (proEtaleRingModules Z RZ) (.up ℤ))
        (((Functor.uncurry.obj ((proEtaleOrdinaryTensor Z RZ).map₂HomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))).map (Prod.mkHom (𝟙 P) q)))
        (resolutionTensor_quasiIso Z RZ P hP q hq))
  exact ⟨d, fun H hH ↦ hd ⟨H, hH⟩⟩

end AlgebraicGeometry.Scheme
