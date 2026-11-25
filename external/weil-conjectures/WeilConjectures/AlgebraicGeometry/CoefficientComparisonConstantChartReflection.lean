/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonPresentationSheafification

/-! # Reflection of one constant comparison chart

Source: Stacks Project, Tags 099T and 099Y, comparison and localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
local instance (priority := 20000) chartModuleSheafify
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A] : HasSheafify J (ModuleCat.{w} A) := by
  let : PreservesFilteredColimitsOfSize.{w, w} (forget (ModuleCat.{w} A)) :=
    ModuleCat.FilteredColimits.forget_preservesFilteredColimits (R := A)
  infer_instance

local instance (priority := 20000) chartWeakModuleSheafify
    {C : Type w} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type w) [CommRing A] : HasWeakSheafify J (ModuleCat.{w} A) :=
  (chartModuleSheafify J A).isRightAdjoint

private instance chartSmallUpEquivalence {C : Type*} [Category* C] :
    (AsSmall.up : C ⥤ AsSmall.{w} C).IsEquivalence :=
  (AsSmall.equiv (C := C)).isEquivalence_functor

private instance chartSmallDownEquivalence {C : Type*} [Category* C] :
    (AsSmall.down : AsSmall.{w} C ⥤ C).IsEquivalence :=
  (AsSmall.equiv (C := C)).isEquivalence_inverse

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
private theorem chartComparisonUnit_isIso (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] :
    IsIso (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).unit := by
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let G := Scheme.smallModelComparisonInclusion.{u, v} X
  let U : X.Etale ⥤ Scheme.smallModelComparisonEtaleSite.{u, v} X := AsSmall.up
  have : U.IsDenseSubsite X.smallEtaleTopology J := by
    change (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).functor.IsDenseSubsite
      X.smallEtaleTopology
      ((AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse.inducedTopology
        X.smallEtaleTopology)
    infer_instance
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let E := U.sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} A)
    X.smallEtaleTopology J
  let B := (Scheme.AffineEtale.Spec X).sheafPushforwardContinuous
    (ModuleCat.{max v (u + 1)} A) (Scheme.AffineEtale.topology X) X.smallEtaleTopology
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{max v (u + 1)} A) J K
  suffices IsIso ((E ⋙ B ⋙ sheafToPresheaf _ _).map (a.unit.app F)) from
    isIso_of_reflects_iso _ (E ⋙ B ⋙ sheafToPresheaf _ _)
  -- The sheaf unit is the Kan unit followed by the sheafification unit.
  have hunit : (a.unit.app F).hom = G.op.lanUnit.app F.obj ≫
      G.op.whiskerLeft (toSheafify K (G.op.lan.obj F.obj)) := by
    change (sheafToPresheaf J _).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
        (ModuleCat.{max v (u + 1)} A) J K).unit.app F) = _
    rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      Adjunction.map_restrictFullyFaithful_unit_app]
    simp
  change IsIso ((Scheme.AffineEtale.Spec X).op.whiskerLeft
    (U.op.whiskerLeft (a.unit.app F).hom))
  rw [hunit, Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
  have hs : IsIso ((Scheme.AffineEtale.Spec X).op.whiskerLeft
      (U.op.whiskerLeft (G.op.whiskerLeft (toSheafify K (G.op.lan.obj F.obj))))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Y
    have : IsAffine ((Scheme.AffineEtale.Spec X).obj Y.unop).left :=
      inferInstanceAs (IsAffine (Scheme.Spec.obj Y.unop.left))
    let W := (Scheme.toProEt X).obj ((Scheme.AffineEtale.Spec X).obj Y.unop)
    -- A constant presentation places every affine etale object in the proved case.
    let P : AffinePresentation X PUnit.{u + 2} :=
      { diagram := (Functor.const _).obj W
        affine := fun _ ↦ inferInstanceAs (IsAffine ((Scheme.AffineEtale.Spec X).obj Y.unop).left)
        etale := fun _ ↦ inferInstanceAs (Etale ((Scheme.AffineEtale.Spec X).obj Y.unop).hom)
        cone := constCone _ W
        affineVertex := inferInstanceAs
          (IsAffine ((Scheme.AffineEtale.Spec X).obj Y.unop).left)
        isLimit := isLimitOfPreserves (Scheme.ProEt.forget X) (isLimitConstCone _ W) }
    exact (coefficientComparison_presentation_toSheafify_isIso X A F P).1
  infer_instance

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A constant comparison chart on one etale object descends with the identical module.
There are no covering, local-constancy, finiteness or Noetherian assumptions.
Source: Stacks Project, Tag 099T, lemma-fully-faithful, and Tag 099Y,
lemma-compare-locally-constant, localization step
(auxiliary; not a blueprint node).

Proof: let U be the etale X-scheme underlying V. The equivalences between the slice
sites and the sites of U identify restriction of comparison inverse image with
comparison inverse image on U. This follows by taking left mates of the commuting
square of sectionwise direct images. Both constant sheaf functors are left adjoints
to terminal-object evaluation, so comparison carries the constant etale sheaf of M
to the constant pro-etale sheaf of the same M. Thus the supplied isomorphism is an
isomorphism between the inverse images of F restricted to U and constant M.
The comparison unit is invertible by Tag 099T: the filtered-colimit formula for
inverse image, followed by sheafification, leaves sections on etale objects
unchanged. This argument works with ModuleCat in the coefficient universe, since
filtered colimits of modules are exact and computed on underlying modules. Full
faithfulness therefore lifts the supplied isomorphism to the etale site of U.
Transport back to the slice over V using AsSmall and the slice-site equivalences.
No model is resized. If U is empty both sheaf categories are terminal, so the same
unit and constant comparisons apply, including M zero and the zero ring. -/
theorem coefficientComparison_constant_over_reflect (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (V : Scheme.smallModelComparisonEtaleSite.{u, v} X)
    (M : ModuleCat.{max v (u + 1)} A)
    (e : ((Functor.sheafPullbackConstruction.sheafPullback
      (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj F).over
        ((Scheme.smallModelComparisonInclusion.{u, v} X).obj V) ≅
      (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, v} X).over
        ((Scheme.smallModelComparisonInclusion.{u, v} X).obj V))
        (ModuleCat.{max v (u + 1)} A)).obj M) :
    Nonempty (F.over V ≅
      (constantSheaf ((Scheme.smallModelComparisonEtaleTopology.{u, v} X).over V)
        (ModuleCat.{max v (u + 1)} A)).obj M) := by
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let G := Scheme.smallModelComparisonInclusion.{u, v} X
  let D := ModuleCat.{max v (u + 1)} A
  let L := Functor.sheafPullbackConstruction.sheafPullback G D J K
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G D J K
  have hu : IsIso a.unit := chartComparisonUnit_isIso X A
  have : PreservesFiniteLimits G := by
    dsimp [G, Scheme.smallModelComparisonInclusion]
    infer_instance
  have : RepresentablyFlat (Over.post (X := V) G) := flat_of_preservesFiniteLimits _
  have : (Over.post (X := V) G).IsContinuous (J.over V) (K.over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G J K).overPost V)
  let R := G.sheafPushforwardContinuous D J K
  let Rv := (Over.post (X := V) G).sheafPushforwardContinuous D
    (J.over V) (K.over (G.obj V))
  let T := ⊤_ (Scheme.smallModelComparisonEtaleSite.{u, v} X)
  -- Both composites are left adjoint to evaluation at the terminal object.
  let c := ((constantSheafAdj J D (terminalIsTerminal (C :=
      Scheme.smallModelComparisonEtaleSite.{u, v} X))).comp a).ofNatIsoRight
    (G.sheafPushforwardContinuousCompSheafSectionsObjIso D J K (op T))
  let k : L.obj ((constantSheaf J D).obj M) ≅ (constantSheaf K D).obj M :=
    (c.leftAdjointUniq (constantSheafAdj K D
      ((terminalIsTerminal (C := Scheme.smallModelComparisonEtaleSite.{u, v} X)).isTerminalObj
        G T))).app M
  let d : (constantSheaf J D).obj M ≅ R.obj ((constantSheaf K D).obj M) :=
    asIso (a.unit.app ((constantSheaf J D).obj M)) ≪≫ R.mapIso k
  -- Direct image and restriction commute by literal sectionwise precomposition.
  let q (H : Sheaf K D) : (R.obj H).over V ≅ Rv.obj (H.over (G.obj V)) :=
    ObjectProperty.isoMk _ (Iso.refl _)
  let j := (J.overPullbackConstantSheafIso D V).app M
  let l := (K.overPullbackConstantSheafIso D (G.obj V)).app M
  exact ⟨(J.overPullback D V).mapIso (asIso (a.unit.app F)) ≪≫
    q (L.obj F) ≪≫ Rv.mapIso e ≪≫ Rv.mapIso l.symm ≪≫
    (q ((constantSheaf K D).obj M)).symm ≪≫
    ((J.overPullback D V).mapIso d).symm ≪≫ j⟩

end AlgebraicGeometry.ProEtale
