/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantSliceDerivedStalkComparison
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import all WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.Ring.Colimits
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.AB
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Point.Over
import all WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import all Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Algebraic isomorphism extracted from a constant adic quotient realization -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

private def scalarConstantIso (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] :
    adicLisseConstantModules X B ⋙ scalarRestriction X B ≅
      constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} B) :=
  FiniteConstantSliceStalkProof.constantScalarIso (ProEt.topology X) B
    (adicLisseRing X B) (adicLisseConstantUnit X B)

private def pulledConstantIso {X Z : Scheme.{u}} (h : Z ⟶ X)
    (B : Type (u + 1)) [CommRing B] :
    adicLisseConstantModules X B ⋙
        proEtaleRingModulePullback h (adicLisseConstantRing X B)
          (adicLisseConstantRing Z B) (constantCoefficients h B) ⋙ scalarRestriction Z B ≅
      constantSheaf (ProEt.topology Z) (ModuleCat.{u + 1} B) :=
  Functor.isoWhiskerLeft _ (pullbackEncoding h B) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (scalarConstantIso X B) _ ≪≫
    (((constantSheafΓAdj _ (ModuleCat.{u + 1} B)).comp
      (AlgebraicGeometry.ProEtale.upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} B) h)).ofNatIsoRight
          (AlgebraicGeometry.ProEtale.globalSectionsLowerStarIso
            (ModuleCat.{u + 1} B) h)).leftAdjointUniq
              (constantSheafΓAdj _ (ModuleCat.{u + 1} B))

/-- The point-stalk extraction step underlying the homology-level lift.

Source: Stacks Project, algebra.tex, Tag 031C (completion quotients);
sites-modules.tex, Tag 093J (exact constants); sites.tex, section "Points"
(constant sheaves and fibers).
(blueprint: lem-weil-pbc-constant-adic-quotient-realization-iso-lift).

Proof: restriction along the finite-quotient/completion-quotient ring map is an
equivalence. Transport the realized isomorphism across the coefficient
comparison and the scalar-restriction/pullback square. Decode the resulting
constant-ring module sheaves as sheaves of modules over the coefficient ring.
Pullback takes a constant sheaf to the corresponding constant sheaf. Choose a
geometric point above the supplied point of the etale chart. Its exact fiber
functor, composed with the constant-sheaf functor, is naturally isomorphic to
the identity. Deriving these natural comparisons recovers an isomorphism of
coefficient complexes after quotient scalar restriction. The latter is an
equivalence, so it lifts that isomorphism to the original coefficient category.
Take its forward morphism.
-/
theorem constantAdicQuotientRealization_iso_lift
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (W : Y.Etale) (_w : W.left)
    (E F : DerivedCategory (ModuleCat.{u + 1} (AdicCompletion d.ideal A ⧸
      (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))))
    (h : Nonempty ((constantAdicQuotientRealization (W.hom ≫ g) d n).obj E ≅
      (constantAdicQuotientRealization (W.hom ≫ g) d n).obj F)) :
    ∃ f : E ⟶ F, IsIso f := by
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1}
      (AdicCompletion d.ideal A ⧸
        (d.ideal.map (algebraMap A (AdicCompletion d.ideal A))) ^ (n + 1))) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let j := W.hom ≫ g
  let B := A ⧸ d.ideal ^ (n + 1)
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} B) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  let : HasDerivedCategory.{u + 2}
      (Sheaf (ProEt.topology W.left) (ModuleCat.{u + 1} B)) :=
    HasDerivedCategory.standard _
  let Q := ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
    (constantAdicQuotientMap d.ideal n)
  let C := adicLisseConstantModules X B
  let b := pbcLevelConstantComparison X d n
  let V := pbcRestrict b.inv
  let c := constantCoefficients j B
  let a := (adicTowerInverseImage j).map b.inv ≫ c.hom
  let U := pbcRestrict a
  let P := proEtaleRingModulePullback j (adicLisseConstantRing X B)
    (adicLisseConstantRing W.left B) c
  let S := scalarRestriction W.left B
  let K := constantSheaf (ProEt.topology W.left) (ModuleCat.{u + 1} B)
  let eqv := RingEquiv.ofBijective (constantAdicQuotientMap d.ideal n)
    (quotient_map_bijective d.ideal d.finitelyGenerated n)
  have : Q.IsEquivalence :=
    inferInstanceAs (ModuleCat.restrictScalars eqv.toRingHom).IsEquivalence
  have : S.IsEquivalence := scalarRestriction_equivalence W.left B
  have : S.Additive := Functor.additive_of_preserves_binary_products S
  have : C.Additive := CompletedConstantReduction.constant_additive X B
  have : PreservesFiniteLimits C := (constantAdicFinite_constant_exact X B).1
  have : PreservesFiniteColimits C := (constantAdicFinite_constant_exact X B).2
  have : IsIso a := by dsimp only [a]; infer_instance
  have : U.IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence W.left ((adicLisseForget W.left).mapIso
      (asIso a))).functor.IsEquivalence
  have : U.mapDerivedCategory.IsEquivalence := Functor.isEquivalence_mapDerivedCategory U
  have : Q.mapDerivedCategory.{u + 1, u + 1}.IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory Q
  let k := proEtaleRingRestrictionDerivedPullback j
    ((pbcAdicRings X d).obj (op n)) (adicLisseConstantRing X B)
    ((adicTowerInverseImage j).obj ((pbcAdicRings X d).obj (op n)))
    (adicLisseConstantRing W.left B) b.inv a (Iso.refl _) c (Category.id_comp a)
  let e₀ : (constantAdicQuotientModules X d n).mapDerivedCategory.{u + 1, u + 2} ≅
      (Q ⋙ C).mapDerivedCategory.{u + 1, u + 2} ⋙ V.mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso (Functor.associator Q C V).symm ≪≫
      (Functor.mapDerivedCategoryCompIso (Q ⋙ C) V).symm
  let e₁ : constantAdicQuotientRealization j d n ≅
      ((Q ⋙ C).mapDerivedCategory.{u + 1, u + 2} ⋙ P.mapDerivedCategory) ⋙ U.mapDerivedCategory :=
    Functor.isoWhiskerRight e₀ (adicTowerPullback j ((pbcAdicRings X d).obj (op n))) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ k.symm ≪≫ (Functor.associator _ _ _).symm
  obtain ⟨e⟩ := h
  let eP := U.mapDerivedCategory.preimageIso ((e₁.app E).symm ≪≫ e ≪≫ e₁.app F)
  let x : Spec (.of (AlgebraicClosure (W.left.residueField _w))) ⟶ W.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (W.left.residueField _w)
      (AlgebraicClosure (W.left.residueField _w)))) ≫ W.left.fromSpecResidueField _w
  let Φ := AlgebraicGeometry.ProEtale.geometricPoint x
  let T : Sheaf (ProEt.topology W.left) (ModuleCat.{u + 1} B) ⥤ ModuleCat.{u + 1} B :=
    Φ.sheafFiber
  have : T.Additive := Functor.additive_of_preserves_binary_products T
  have : (C ⋙ P ⋙ S).Additive := by infer_instance
  let e₂ : C.mapDerivedCategory.{u + 1, u + 2} ⋙ P.mapDerivedCategory ⋙
      S.mapDerivedCategory.{u + 2, u + 2} ≅
      K.mapDerivedCategory.{u + 1, u + 2} :=
    Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryCompIso P S) ≪≫
      Functor.mapDerivedCategoryCompIso C (P ⋙ S) ≪≫
      Functor.mapDerivedCategoryNatIso (pulledConstantIso j B)
  let e₃ : K.mapDerivedCategory.{u + 1, u + 2} ⋙ T.mapDerivedCategory.{u + 2, u + 1} ≅
      𝟭 (DerivedCategory.{u + 1} (ModuleCat.{u + 1} B)) :=
    Functor.mapDerivedCategoryCompIso K T ≪≫
      Functor.mapDerivedCategoryNatIso
        (Φ.constantSheafCompSheafFiberIso (ProEt.topology W.left) (ModuleCat.{u + 1} B)) ≪≫
      Functor.mapDerivedCategoryIdIso _
  let H := P.mapDerivedCategory ⋙ S.mapDerivedCategory.{u + 2, u + 2} ⋙
    T.mapDerivedCategory.{u + 2, u + 1}
  let eC : C.mapDerivedCategory.{u + 1, u + 2} ⋙ H ≅ 𝟭 _ :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e₂ T.mapDerivedCategory.{u + 2, u + 1} ≪≫ e₃
  let eQ (M) : H.obj ((Q ⋙ C).mapDerivedCategory.{u + 1, u + 2}.obj M) ≅
      Q.mapDerivedCategory.{u + 1, u + 1}.obj M :=
    H.mapIso ((Functor.mapDerivedCategoryCompIso Q C).symm.app M) ≪≫
      eC.app (Q.mapDerivedCategory.{u + 1, u + 1}.obj M)
  let eEF : E ≅ F := Q.mapDerivedCategory.{u + 1, u + 1}.preimageIso
    ((eQ E).symm ≪≫
      (S.mapDerivedCategory.{u + 2, u + 2} ⋙ T.mapDerivedCategory.{u + 2, u + 1}).mapIso eP ≪≫
      eQ F)
  exact ⟨eEF.hom, inferInstance⟩

end AlgebraicGeometry.Scheme
