/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClopenIdempotent
public import Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChange

/-! # The clopen-factor description of the canonical proper comparison

Source: the ordered exterior-product and comparison paragraphs of
sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance 40000] CategoryTheory.sheafIsAbelian
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
private theorem derived_comp_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
    (F F' : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [F'.Additive] [G.Additive] [H.Additive]
    [F.PreservesKInjectiveComplexes] [F'.PreservesKInjectiveComplexes]
    (e : F ≅ F') (c : F' ⋙ G ≅ H) :
    Functor.whiskerRight (Functor.rightDerivedFunctorNatIso e).hom G.rightDerivedFunctor ≫
      (Functor.rightDerivedFunctorCompIso' F' G c).hom =
    (Functor.rightDerivedFunctorCompIso' F G
      (Functor.isoWhiskerRight e G ≪≫ c)).hom := by
  refine Functor.rightDerived_ext (F.rightDerivedFunctor ⋙ G.rightDerivedFunctor)
    (Functor.rightDerivedFunctorCompUnit F G)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) _ _ _ ?_
  ext X
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [Functor.rightDerivedFunctorNatIso, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightDerivedFunctorCompUnit_app, Category.assoc]
  rw [← G.rightDerivedFunctor.map_comp_assoc,
    Functor.rightDerivedFunctorNatTrans_app, G.rightDerivedFunctor.map_comp]
  have hn := G.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory e.hom (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))
  simp only [Functor.comp_map] at hn
  simp only [Category.assoc]
  erw [← reassoc_of% hn, Functor.rightDerivedFunctorCompIso'_fac_app,
    Functor.rightDerivedFunctorCompIso'_fac_app]
  simp only [← DerivedCategory.Qh.map_comp_assoc]
  congr 1

namespace AlgebraicGeometry.ProEtale

/-- The canonical proper factorization through derived direct image of the clopen part. -/
def properModelComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [HasCompactification f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ≅
      (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor := by
  let B := ModuleCat.{u + 1} A
  let c := HasCompactification.compactification f
  letI := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range B c.i
    (c.isClopen_range_openImmersion inferInstance).isClosed
  letI := preservesFiniteColimits_lowerStar_of_isClosed_range B c.i
    (c.isClopen_range_openImmersion inferInstance).isClosed
  letI := (upperStarLowerStarAdjunction B c.i).preservesKInjectiveComplexes
  exact Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso (asIso (openImmersionLowerShriekToLowerStar B c.i)) ≪≫
        (lowerStar B c.i).rightDerivedFunctorIsoMapDerivedCategory.symm) _ ≪≫
    Functor.rightDerivedFunctorCompIso' (lowerStar B c.i) (lowerStar B c.g)
      (lowerStarFactor B c.comm.symm)

/-- The published proper comparison equals the direct-image factorization.
Source: blueprint latest, sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, ordered compact-support composition;
parent node proof Step 3 (blueprint: lem-pur-closed-proper-derived-factor).

Proof: let c=(j,p) be the chosen compactification. Properness of f makes j clopen.
Put J=j_!, I=j_* and e:J≅I the canonical sheaf comparison. Both are exact and preserve
K-injective complexes. The underived comparison f_!→f_* is p_*(e) followed by the
specified direct-image factorization. Apply right derivation to this equality.
Naturality of the composition comparison identifies R(p_*e) with Rp_*(Re).
Naturality of RF≅D(F) for exact functors identifies Re with D(e). The inverse exact
comparisons then give precisely the displayed factorization. All the equalities
are equalities of natural transformations: they follow by right-derived uniqueness
from their pasted-unit equations on homotopy representatives. Thus neither an
arbitrary compactification choice nor a new choice of isomorphism is used. -/
theorem closedProperDerivedFactor (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [HasCompactification f] :
    rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar (ModuleCat.{u + 1} A) f =
      properModelComparison A f := by
  let B := ModuleCat.{u + 1} A
  let c := HasCompactification.compactification f
  have := isIso_openImmersionLowerShriekToLowerStar_of_isClosed_range B c.i
    (c.isClopen_range_openImmersion inferInstance).isClosed
  have := preservesFiniteColimits_lowerStar_of_isClosed_range B c.i
    (c.isClopen_range_openImmersion inferInstance).isClosed
  have := (upperStarLowerStarAdjunction B c.i).preservesKInjectiveComplexes
  let e := asIso (openImmersionLowerShriekToLowerStar B c.i)
  have := Functor.preservesKInjectiveComplexes_of_iso e.symm
  have ha : asIso (lowerShriekToLowerStar B f) =
      Functor.isoWhiskerRight e (lowerStar B c.g) ≪≫ lowerStarFactor B c.comm.symm := by
    apply Iso.ext
    rw [← lowerStarComp_trans_lowerStarCongr]
    rfl
  apply Iso.ext
  ext K
  have hn := congr_app (derived_comp_naturality
    (openImmersionLowerShriek B c.i) (lowerStar B c.i) (lowerStar B c.g)
    (lowerStar B f) e (lowerStarFactor B c.comm.symm)) K
  simp only [Functor.whiskerRight_app, NatTrans.comp_app] at hn
  have he := Etale.rightDerivedFunctorNatIso_hom_app_comp_isoMapDerivedCategory_hom_app e K
  have ht : (openImmersionLowerShriek B c.i).rightDerivedFunctorIsoMapDerivedCategory.inv.app K ≫
      (Functor.rightDerivedFunctorNatIso e).hom.app K =
      (Functor.mapDerivedCategoryNatIso e).hom.app K ≫
        (lowerStar B c.i).rightDerivedFunctorIsoMapDerivedCategory.inv.app K := by
    apply (cancel_mono
      ((lowerStar B c.i).rightDerivedFunctorIsoMapDerivedCategory.hom.app K)).1
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [he, Iso.inv_hom_id_app_assoc]
  change (lowerStar B c.g).rightDerivedFunctor.map
      ((openImmersionLowerShriek B c.i).rightDerivedFunctorIsoMapDerivedCategory.inv.app K) ≫
        (Functor.rightDerivedFunctorCompIso' (openImmersionLowerShriek B c.i)
          (lowerStar B c.g) (asIso (lowerShriekToLowerStar B f))).hom.app K = _
  rw [ha, ← hn, ← (lowerStar B c.g).rightDerivedFunctor.map_comp_assoc, ht]
  rfl
end AlgebraicGeometry.ProEtale
