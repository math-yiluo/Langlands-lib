/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleUniversalNormalization
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.CategoryTheory.Adjunction.Comma

/-! # Universal scalar arrows on an etale source

Source: Stacks Project, Tags 06YS, 0G7E, 0D6D and 03ED.
(blueprint: lem-weil-pbc-etale-source-normalization-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem universal_of_isIso_scalarMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂) {F : A ⥤ C} {G : B ⥤ D}
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂)
    [IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)))]
    {P : A} {N : B} (d : P ⟶ U₁.obj N)
    (h : StructuredArrow.IsUniversal (StructuredArrow.mk d)) :
    Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk (F.map d ≫ τ.app N) : StructuredArrow (F.obj P) U₂)) := by
  let e := (mkInitialOfLeftAdjoint _ a₁ P).uniqueUpToIso h
  let α : E₁.obj P ≅ N := (StructuredArrow.proj P U₁).mapIso e
  have hα : a₁.unit.app P ≫ U₁.map α.hom = d := e.hom.w
  let m := ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ))
  let t : E₂.obj (F.obj P) ≅ G.obj N := (asIso m).app P ≪≫ G.mapIso α
  have ht : a₂.unit.app (F.obj P) ≫ U₂.map t.hom = F.map d ≫ τ.app N := by
    have hu := unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ τ) P
    change F.map (a₁.unit.app P) ≫ τ.app (E₁.obj P) =
      a₂.unit.app (F.obj P) ≫ U₂.map (m.app P) at hu
    simp only [t, Iso.trans_hom, Iso.app_hom, asIso_hom, Functor.mapIso_hom,
      Functor.map_comp, ← Category.assoc]
    rw [← hu]
    have hn := τ.naturality α.hom
    dsimp only [Functor.comp_map] at hn
    rw [Category.assoc, ← hn, ← F.map_comp_assoc, hα]
  let i : (StructuredArrow.mk (a₂.unit.app (F.obj P)) : StructuredArrow (F.obj P) U₂) ≅
      StructuredArrow.mk (F.map d ≫ τ.app N) := StructuredArrow.isoMk t ht
  exact ⟨(mkInitialOfLeftAdjoint _ a₂ (F.obj P)).ofIso i⟩

private def normalizationEtaleCoefficientIso (Z : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) (V : Z.Etale) :
    Sheaf.restrictScalars Z.smallEtaleTopology q ⋙
        Etale.upperStar (ModuleCat.{u + 1} R) V.hom ≅
      Etale.upperStar (ModuleCat.{u + 1} S) V.hom ⋙
        Sheaf.restrictScalars V.left.smallEtaleTopology q := by
  letI : (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ V.hom).IsContinuous
      Z.smallEtaleTopology V.left.smallEtaleTopology :=
    Etale.isContinuous_overPullback V.hom
  exact normalizationPullbackIso Z.smallEtaleTopology
    (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ V.hom)
    V.left.smallEtaleTopology q

set_option synthInstance.maxSize 2048 in
private theorem etaleNormalizationScalarMate_isIso (Z : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) (V : Z.Etale) :
    IsIso (((mateEquiv
      (ProEtale.scalarDerivedAdjunctionData Z.smallEtaleTopology q).adjunction
      (ProEtale.scalarDerivedAdjunctionData V.left.smallEtaleTopology q).adjunction).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso
        (normalizationEtaleCoefficientIso Z q V)).hom))) := by
  let c := normalizationEtaleCoefficientIso Z q V
  have hOrd : IsIso (((mateEquiv
      (ProEtale.scalarAdjunction Z.smallEtaleTopology q)
      (ProEtale.scalarAdjunction V.left.smallEtaleTopology q)).symm
      (TwoSquare.mk _ _ _ _ c.hom))) := by
    let F := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ V.hom
    have : F.IsContinuous Z.smallEtaleTopology V.left.smallEtaleTopology :=
      Etale.isContinuous_overPullback V.hom
    let aR := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      F (ModuleCat.{u + 1} R) Z.smallEtaleTopology V.left.smallEtaleTopology
    let aS := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      F (ModuleCat.{u + 1} S) Z.smallEtaleTopology V.left.smallEtaleTopology
    apply ProEtale.isIso_left_mate_of_iterated
      (ProEtale.scalarAdjunction Z.smallEtaleTopology q)
      (ProEtale.scalarAdjunction V.left.smallEtaleTopology q) aR aS
    let γ := TwoSquare.mk
      (F.sheafPushforwardContinuous (ModuleCat.{u + 1} S)
        Z.smallEtaleTopology V.left.smallEtaleTopology)
      (Sheaf.restrictScalars V.left.smallEtaleTopology q)
      (Sheaf.restrictScalars Z.smallEtaleTopology q)
      (F.sheafPushforwardContinuous (ModuleCat.{u + 1} R)
        Z.smallEtaleTopology V.left.smallEtaleTopology) (𝟙 _)
    change IsIso ((mateEquiv aS aR ((mateEquiv aS aR).symm γ)))
    rw [Equiv.apply_symm_apply]
    change IsIso (𝟙 _)
    infer_instance
  have : IsIso (((mateEquiv
      (ProEtale.scalarAdjunction Z.smallEtaleTopology q)
      (ProEtale.scalarAdjunction V.left.smallEtaleTopology q)).symm
      (TwoSquare.mk _ _ _ _ c.symm.inv))) := by
    simpa only [Iso.symm_inv] using hOrd
  have h := ProEtale.derived_mate_isIso_of_flat
    (A := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))
    (B := Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} S))
    (C := Sheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} R))
    (D := Sheaf V.left.smallEtaleTopology (ModuleCat.{u + 1} S))
    (ProEtale.scalarAdjunction Z.smallEtaleTopology q)
    (ProEtale.scalarAdjunction V.left.smallEtaleTopology q)
    (ProEtale.scalarDerivedAdjunctionData Z.smallEtaleTopology q)
    (ProEtale.scalarDerivedAdjunctionData V.left.smallEtaleTopology q)
    (Etale.upperStar (ModuleCat.{u + 1} R) V.hom)
    (Etale.upperStar (ModuleCat.{u + 1} S) V.hom) c.symm
  have hs : (Functor.mapDerivedCategoryNatIso c.symm).inv =
      (Functor.mapDerivedCategoryNatIso c).hom := by
    simpa only [Iso.symm_symm_eq] using
      (Functor.mapDerivedCategoryNatIso_symm c.symm).symm
  simpa only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, hs, Category.assoc] using h

/-- An initial coefficient arrow stays initial on every etale source.

Source: `sites-cohomology.tex`, K-flat resolutions (06YS), their pullback (0G7E),
and composition of derived pullbacks (0D6D); the small etale site (03ED).
(blueprint: lem-weil-pbc-etale-source-normalization-universal).

Proof: pass from fixed-ring module sheaves to modules over their constant ring
sheaves. Let L be derived extension along q, left adjoint to exact restriction.
Initiality of the supplied arrow identifies its target with L applied to its
source, with the arrow equal to the adjunction unit followed by that isomorphism.
Choose a K-flat resolution with flat terms. Inverse image to an etale source
preserves K-flatness and flatness. Both applying inverse image before extension
and applying extension before inverse image are represented by the same
sheafified balanced tensor complex. This gives an invertible inverse scalar mate.
The tensor unit x maps to 1 tensor x, so its unit identity is exactly the localized
normalizationPullbackIso used in etaleIsomorphismNormalizationArrow. Consequently
the displayed arrow is the new adjunction unit followed by the tensor comparison
and the pulled target isomorphism. Transport of the initial unit gives its
universality. No boundedness, flatness of S over R, or nonemptiness of the source
is needed; zero objects and zero coefficient rings are included.
-/
theorem etaleSourceNormalization_universal (Z : Scheme.{u})
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    {C : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} R))}
    {C' : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} S))}
    (δ : C ⟶ (normalizationRestrict Z.smallEtaleTopology q).obj C')
    (h : Nonempty (StructuredArrow.IsUniversal
      (StructuredArrow.mk δ : StructuredArrow _
        (normalizationRestrict Z.smallEtaleTopology q))))
    (V : Z.Etale) :
    Nonempty (StructuredArrow.IsUniversal (StructuredArrow.mk
      (etaleIsomorphismNormalizationArrow Z q δ V))) := by
  have := etaleNormalizationScalarMate_isIso Z q V
  exact universal_of_isIso_scalarMate
    (ProEtale.scalarDerivedAdjunctionData Z.smallEtaleTopology q).adjunction
    (ProEtale.scalarDerivedAdjunctionData V.left.smallEtaleTopology q).adjunction
    (Functor.mapDerivedCategorySquareIso
      (normalizationEtaleCoefficientIso Z q V)).hom δ h.some

end AlgebraicGeometry.Scheme
