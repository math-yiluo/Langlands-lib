/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricOrdinaryRealization
import WeilConjectures.CategoryTheory.ScalarInverseImageIndependent
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarEvaluationTransposeExistence
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence

/-! # The normalized geometric coefficient pullback mate

Source: Zheng Construction 4.1; Stacks 03EL, 0G7E and 07A6.
(blueprint: lem-coef-geometric-coefficient-pullback-mate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.defeqAttrib.useBackward true
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)

variable (A : Data.{c, v, r} J B τ)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)
  (target : Data.{c, v, r} J' O.coefficients O.coefficientTransition)

private theorem coefficientCompatibility {m n : ℕ} (h : n ≤ m) :
    uInv.map ((sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r})).map
        (coefficientMap.{c, v, max c v r} J B τ h)) ≫
        (O.inverseImage n).ringUnderlying.hom =
      (O.inverseImage m).ringUnderlying.hom ≫
        (sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r})).map
          (coefficientMap.{c, v, max c v r} J'
            O.coefficients O.coefficientTransition h) := by
  let α : rings.{c, v, max c v r} J B τ ⋙
        sheafCompose J (CategoryTheory.forget CommRingCat.{max c v r}) ⋙ uInv ⟶
      rings.{c, v, max c v r} J' O.coefficients O.coefficientTransition ⋙
        sheafCompose J' (CategoryTheory.forget CommRingCat.{max c v r}) :=
    NatTrans.ofOpSequence (fun n ↦ (O.inverseImage n).ringUnderlying.hom) (by
      intro n
      simpa only [Functor.comp_map, rings, Functor.ofOpSequence_map_homOfLE_succ] using
        O.coefficient_compatibility n)
  exact α.naturality (homOfLE h).op

-- Normalize the two scalar adjunctions before passing to underlying sheaves.
private theorem ordinaryScalarMate_isIso [PreservesFiniteLimits uInv]
    {m n : ℕ} (h : n ≤ m) :
    IsIso ((mateEquiv (A.scalar h).ordinaryAdjunction
      (target.scalar h).ordinaryAdjunction).symm
        (TwoSquare.mk _ _ _ _ (O.restrictionPullback h).hom)) := by
  classical
  let S := A.scalar h
  let T := target.scalar h
  let F := (O.inverseImage m).modules
  let G := (O.inverseImage n).modules
  let δ := O.restrictionPullback h
  let a := ((mateEquiv S.ordinaryAdjunction T.ordinaryAdjunction).symm
    (TwoSquare.mk _ _ _ _ δ.hom))
  obtain ⟨e, he⟩ :=
    SheafOfModules.ScalarIndependent.exists_scalarInverseImageIndependent
      uInv uPush adjSet (O.inverseImage m) (O.inverseImage n)
      (coefficientMap.{c, v, max c v r} J B τ h)
      (coefficientMap.{c, v, max c v r} J' O.coefficients O.coefficientTransition h)
      (coefficientCompatibility J B τ J' uInv uPush adjSet O h)
      S.model.E T.model.E S.ordinaryAdjunction T.ordinaryAdjunction
  have ha : a = e.inv := by
    apply NatTrans.ext
    funext M
    apply (T.ordinaryAdjunction.homEquiv _ _).injective
    have hm := unit_mateEquiv_symm S.ordinaryAdjunction T.ordinaryAdjunction
      (TwoSquare.mk _ _ _ _ δ.hom) M
    change T.ordinaryAdjunction.homEquiv _ _ (a.app M) = _
    simp only [Adjunction.homEquiv_unit]
    change F.map (S.ordinaryAdjunction.unit.app M) ≫
      δ.hom.app (S.model.E.obj M) =
        T.ordinaryAdjunction.unit.app (F.obj M) ≫
          (res (coefficientMap J' O.coefficients O.coefficientTransition h)).map
            (a.app M) at hm
    rw [← hm]
    apply (underlying.{c, v, r} J' (O.coefficients m)).map_injective
    let U := underlying.{c, v, r} J' (O.coefficients m)
    let V := underlying.{c, v, r} J' (O.coefficients n)
    let W := underlying.{c, v, r} J (B m)
    have hn := (O.inverseImage m).moduleUnderlying.hom.naturality
      (S.ordinaryAdjunction.unit.app M)
    have hd := O.restrictionPullback_underlying h (S.model.E.obj M)
    have hh := he M
    change uInv.map (W.map (S.ordinaryAdjunction.unit.app M)) ≫
      (O.inverseImage n).moduleUnderlying.inv.app (S.model.E.obj M) ≫
        V.map (e.hom.app M) =
      (O.inverseImage m).moduleUnderlying.inv.app M ≫
        U.map (T.ordinaryAdjunction.unit.app (F.obj M)) at hh
    have hl : U.map (F.map (S.ordinaryAdjunction.unit.app M) ≫
        δ.hom.app (S.model.E.obj M)) =
      (O.inverseImage m).moduleUnderlying.hom.app M ≫
        uInv.map (W.map (S.ordinaryAdjunction.unit.app M)) ≫
          (O.inverseImage n).moduleUnderlying.inv.app (S.model.E.obj M) := by
      rw [U.map_comp]
      apply (cancel_mono ((O.inverseImage n).moduleUnderlying.hom.app
        (S.model.E.obj M))).mp
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [hd, Category.comp_id]
      exact hn
    rw [hl]
    change _ = U.map (T.ordinaryAdjunction.unit.app (F.obj M)) ≫ V.map (e.inv.app M)
    have hv : V.map (e.inv.app M) ≫ V.map (e.hom.app M) = 𝟙 _ := by
      rw [← V.map_comp, e.inv_hom_id_app, V.map_id]
    apply (cancel_mono (V.map (e.hom.app M))).mp
    simp only [Category.assoc, hv]
    erw [Category.comp_id]
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using
      congrArg (fun f ↦ (O.inverseImage m).moduleUnderlying.hom.app M ≫ f) hh
  rw [show ((mateEquiv (A.scalar h).ordinaryAdjunction
    (target.scalar h).ordinaryAdjunction).symm
      (TwoSquare.mk _ _ _ _ (O.restrictionPullback h).hom)) = a from rfl, ha]
  infer_instance

private theorem inverseImage_good [PreservesFiniteLimits uInv] (n : ℕ)
    (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := B n) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := O.coefficients n)
        (((O.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J') (R := O.coefficients n)
        ((((O.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P).X i) := by
  classical
  let F := (O.inverseImage n).modules
  let S := Classical.choice
    (SheafOfModules.nonempty_systemScalarModel (𝟙 (O.coefficients n)))
  have ht := SheafOfModules.isKFlat_ringedToposPullback uInv uPush adjSet
    (O.inverseImage n) (𝟙 (O.coefficients n)) (F ⋙ S.model.E)
    (fun M ↦ S.model.obj_eq (F.obj M))
    (fun f ↦ S.model.map_eq (F.map f)) P hP hf
  let i : F ⋙ S.model.E ≅ F :=
    Functor.isoWhiskerLeft F (SheafOfModules.systemScalarModelUnit rfl S) ≪≫ F.rightUnitor
  let ic := (NatIso.mapHomologicalComplex i (.up ℤ)).app P
  exact ⟨SheafOfModules.kFlat_iso_independent (O.coefficients n) ic ht.1,
    fun k ↦ SheafOfModules.flatOnSite_of_iso (O.coefficients n)
      ((HomologicalComplex.eval _ (.up ℤ) k).mapIso ic) (ht.2 k)⟩

-- The representative comparison elaborates several independent coefficient universes.
/-- The inverse mate of coefficient restriction and geometric pullback is invertible.
Source: Zheng, Construction 4.1 and the paragraph preceding Lemma 4.10;
Stacks 03EL, 0G7E, 06YY and 07A6.
(blueprint: lem-coef-geometric-coefficient-pullback-mate).

Proof: the ordinary scalar inverse-image comparison intertwines the two ordinary
scalar units. The identity-on-underlying-sheaves restriction comparison therefore
has this isomorphism's inverse as its left mate. On a flat-term K-flat complex,
inverse image preserves K-flatness. The normalized scalar adjunction transposes
identify the derived mate with that ordinary isomorphism, conjugated by the two
K-flat model comparisons and the exact inverse-image localization comparisons.
All of these factors are invertible. Every derived object is isomorphic to such
a representative, so naturality proves invertibility on every derived object. -/
theorem geometricCoefficientPullbackMate_isIso [PreservesFiniteLimits uInv]
    {m n : ℕ} (h : n ≤ m) :
    IsIso ((mateEquiv (A.scalar h).adjunction (target.scalar h).adjunction).symm
      (TwoSquare.mk _ _ _ _
        ((Functor.mapDerivedCategoryCompIso _ _ ≪≫
          Functor.mapDerivedCategoryNatIso (O.restrictionPullback h) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).hom))) := by
  classical
  let S := A.scalar h
  let T := target.scalar h
  let R := res.{c, v, max c v r} (coefficientMap.{c, v, max c v r} J B τ h)
  let R' := res.{c, v, max c v r}
    (coefficientMap.{c, v, max c v r} J' O.coefficients O.coefficientTransition h)
  let F := (O.inverseImage m).modules
  let G := (O.inverseImage n).modules
  let δ := O.restrictionPullback h
  let δD := Functor.mapDerivedCategorySquareIso δ
  let a := ((mateEquiv S.ordinaryAdjunction T.ordinaryAdjunction).symm
    (TwoSquare.mk _ _ _ _ δ.hom))
  have ha : IsIso a := ordinaryScalarMate_isIso J B τ J' uInv uPush adjSet A O target h
  let aD := ((mateEquiv S.adjunction T.adjunction).symm
    (TwoSquare.mk _ _ _ _ δD.hom))
  have hrep (P : CochainComplex (Mod.{c, v, max c v r} J (B m)) ℤ)
      (hP : P.IsKFlatIndependentCoefficients)
      (hp : CochainComplex.IsKFlatIndependentCoefficients (R := O.coefficients m)
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :
      aD.app (DerivedCategory.Q.obj P) ≫
          G.mapDerivedCategory.map (S.model.ε.app P) ≫
          G.mapDerivedCategoryFactors.hom.app
            ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P) =
        T.T.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          T.model.ε.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
            (@asIso _ _ _ _ a ha) (.up ℤ)).hom.app P) := by
    refine mate_comparison_at
      (S.ordinaryAdjunction.mapHomologicalComplex (.up ℤ))
      (T.ordinaryAdjunction.mapHomologicalComplex (.up ℤ))
      S.adjunction T.adjunction S.model.ε T.model.ε
      R.mapDerivedCategoryFactors R'.mapDerivedCategoryFactors
      F.mapDerivedCategoryFactors G.mapDerivedCategoryFactors P
      ?_ ?_ (TwoSquare.mk _ _ _ _ (δ.hom.mapHomologicalComplex (.up ℤ)))
      (TwoSquare.mk _ _ _ _ δD.hom) ?_
      (NatIso.mapHomologicalComplex (@asIso _ _ _ _ a ha) (.up ℤ)).hom ?_
    · intro K f
      apply (cancel_mono (R.mapDerivedCategoryFactors.hom.app K)).mp
      rw [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      exact S.transpose_model P K hP f
    · intro K f
      apply (cancel_mono (R'.mapDerivedCategoryFactors.hom.app K)).mp
      rw [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
      exact T.transpose_model _ K hp f
    · intro K
      exact exactSquare_fac δ K
    · intro K
      apply HomologicalComplex.hom_ext
      intro i
      exact (unit_mateEquiv_symm S.ordinaryAdjunction T.ordinaryAdjunction
        (TwoSquare.mk _ _ _ _ δ.hom) (K.X i)).symm
  have hi (P : CochainComplex (Mod.{c, v, max c v r} J (B m)) ℤ)
      (hP : P.IsKFlatIndependentCoefficients)
      (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := B m) (P.X i)) :
      IsIso (aD.app (DerivedCategory.Q.obj P)) := by
    have hp := (inverseImage_good J B τ J' uInv uPush adjSet O m P hP hf).1
    have := S.model.computes P hP
    have := T.model.computes _ hp
    have : IsIso (aD.app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategory.map (S.model.ε.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P)) := by
      rw [hrep P hP hp]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (G.mapDerivedCategory.map (S.model.ε.app P) ≫
        G.mapDerivedCategoryFactors.hom.app
          ((S.model.E.mapHomologicalComplex (.up ℤ)).obj P))
  have hX (X : D.{c, v, max c v r} J (B m)) : IsIso (aD.app X) := by
    let K := DerivedCategory.Q.objPreimage X
    obtain ⟨P, q, hP, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := B m) K
    have hflat (i : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := B m) (P.X i) :=
      (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso _ (P.X i)).symm (hf i)
    have := hq
    let z : DerivedCategory.Q.obj P ≅ X :=
      asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso X
    exact (NatTrans.isIso_app_iff_of_iso aD z).mp (hi P hP hflat)
  exact NatIso.isIso_of_isIso_app aD

end WeilConjectures.SemilinearSections
