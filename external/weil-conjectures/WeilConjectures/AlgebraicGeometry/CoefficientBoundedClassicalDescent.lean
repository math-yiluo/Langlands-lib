/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ClassicalContinuityMap
public import WeilConjectures.AlgebraicGeometry.ConstructibleProEtaleComparisonData
import WeilConjectures.AlgebraicGeometry.CoefficientClassicalModuleOrigin
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonInjectiveAcyclic
import WeilConjectures.AlgebraicGeometry.ConstructibleComparisonModuleExact
import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunctionAcyclic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
/-! # Bounded classical descent on coefficient-sized derived categories
Source: blueprint classical derived equivalence, Stacks Tag 09AL.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
/-- Cohomology vanishes outside one ordered finite integer interval.
Source: Stacks Tag 05RU (auxiliary; not a blueprint node). -/
def coefficientCohomologyBounded {C : Type w} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})
    (K : ConstantCompletion.D R) : Prop :=
  ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
    IsZero ((coefficientModelCohomology R q).obj K)

private theorem boundedBelow_map_bijective
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [EnoughInjectives E] {L : C ⥤ E} {R : E ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) [IsIso adj.derivedPlus.unit]
    (K M : DerivedCategory.Plus C) :
    Function.Bijective (L.mapDerivedCategory.map :
      (K.obj ⟶ M.obj) → (L.mapDerivedCategory.obj K.obj ⟶
        L.mapDerivedCategory.obj M.obj)) := by
  let ff := adj.derivedPlus.fullyFaithfulLOfIsIsoUnit
  constructor
  · intro f g h
    have he : L.mapDerivedCategoryPlus.map (ObjectProperty.homMk f : K ⟶ M) =
        L.mapDerivedCategoryPlus.map (ObjectProperty.homMk g : K ⟶ M) := by
      apply ObjectProperty.hom_ext
      exact h
    exact congrArg (fun f : K ⟶ M ↦ f.hom) (ff.map_injective he)
  · intro f
    obtain ⟨g, hg⟩ := ff.map_surjective (ObjectProperty.homMk f)
    exact ⟨g.hom, congrArg (fun f ↦ f.hom) hg⟩

private theorem bounded_origin_of_homology_origin
    {C E : Type*} [Category C] [Category E] [Abelian C] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory E]
    [EnoughInjectives E] {L : C ⥤ E} {R : E ⥤ C}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) [IsIso adj.derivedPlus.unit]
    (K : DerivedCategory.Plus E) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ q, L.essImage ((DerivedCategory.Plus.homologyFunctor E q).obj K)) :
    ∃ M : DerivedCategory C, Nonempty (L.mapDerivedCategory.obj M ≅ K.obj) := by
  let adjD := adj.derivedPlus
  let F := L.mapDerivedCategoryPlus
  let G := R.rightDerivedFunctorPlus
  let : G.CommShift ℤ := adjD.rightAdjointCommShift ℤ
  let : adjD.CommShift ℤ := adjD.commShift_of_leftAdjoint ℤ
  let : G.IsTriangulated := adjD.isTriangulated_rightAdjoint
  let ff := adjD.fullyFaithfulLOfIsIsoUnit
  let : F.Full := ff.full
  let : F.Faithful := ff.faithful
  have hsingle : ∀ Y, L.essImage Y →
      IsIso (adjD.counit.app ((DerivedCategory.Plus.singleFunctor E 0).obj Y)) := by
    intro Y hY
    obtain ⟨Z, ⟨e⟩⟩ := hY
    let e' : F.obj ((DerivedCategory.Plus.singleFunctor C 0).obj Z) ≅
        (DerivedCategory.Plus.singleFunctor E 0).obj Y :=
      (L.mapDerivedCategoryPlusSingleFunctor 0).app Z ≪≫
        (DerivedCategory.Plus.singleFunctor E 0).mapIso e
    exact adjD.isIso_counit_app_of_iso e'.symm
  have : IsIso (adjD.counit.app K) :=
    DerivedCategory.Plus.isIso_app_of_bounded adjD.counit L.essImage hsingle K a b hK
  refine ⟨(G.obj K).obj, ⟨?_⟩⟩
  exact (L.mapDerivedCategoryPlusCompatibility.app (G.obj K)).symm ≪≫
    DerivedCategory.Plus.ι.mapIso (asIso (adjD.counit.app K))

/-- Derived comparison is fully faithful between bounded objects, and an object
with bounded classical cohomology has an etale derived antecedent. No constructibility
or finiteness of its cohomology modules is imposed here.
Source: blueprint det-pe-classical-derived-equivalence and
theorem-bounded-below-cohomology-comparison; Stacks Tag 09AL (auxiliary; not a blueprint node).

Proof: exactness of intrinsic module comparison and enough injectives give its
bounded-below derived adjunction. The ordinary unit on injectives and acyclicity
of their pullbacks make the derived unit invertible, hence the derived pullback
fully faithful on D+. This gives the Hom-set bijection for bounded objects after
the fully faithful inclusion into the unbounded derived category. For descent,
continuity puts each cohomology module in the ordinary essential image. The
counit is invertible on single complexes in that image; finite truncation
devissage makes it invertible on every bounded complex with such cohomology.
The derived direct image is its antecedent. Finally, localization uniqueness
identifies the given D with the exact derived pullback, and naturality transports
both conclusions. No constructibility or finiteness hypothesis is used. -/
theorem coefficientComparison_boundedClassical (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (D : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A) ⥤
          ConstantCompletion.D (ConstantCompletion.constant
            (Scheme.coefficientProEtaleModelTopology.{u, v} X) A))
    (hD : Nonempty (ConstantCompletion.Q _ ⋙ D ≅
      constructibleComparisonComplexPullback X A ⋙ ConstantCompletion.Q _)) :
    (∀ K L : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
      coefficientCohomologyBounded _ K → coefficientCohomologyBounded _ L →
        Function.Bijective (D.map : (K ⟶ L) → (D.obj K ⟶ D.obj L))) ∧
    (∀ K : ConstantCompletion.D (ConstantCompletion.constant
        (Scheme.coefficientProEtaleModelTopology.{u, v} X) A),
      coefficientCohomologyBounded _ K →
      (∀ q : ℤ, ∀ {I : Type (u + 1)} [SmallCategory I] [IsCofiltered I]
        (P : AffinePresentation X I),
        IsIso (continuityMap P
          ((AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X).op ⋙
            ((coefficientModelFixedScalars _ A).obj
              ((coefficientModelCohomology _ q).obj K)).obj))) →
      ∃ M, Nonempty (D.obj M ≅ K)) := by
  let : HasSheafify (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let : HasSheafify (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  let C := ConstantCompletion.Mod (ConstantCompletion.constant
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)
  let E := ConstantCompletion.Mod (ConstantCompletion.constant
    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)
  let : HasDerivedCategory C := HasDerivedCategory.standard C
  let : HasDerivedCategory E := HasDerivedCategory.standard E
  let : IsGrothendieckAbelian.{max v (u + 1)} C :=
    SheafOfModules.isGrothendieckAbelian _
  let : IsGrothendieckAbelian.{max v (u + 1)} E :=
    SheafOfModules.isGrothendieckAbelian _
  let L := constructibleComparisonPullback.{u, v} X A
  let R := SheafOfModules.pushforward.{max v (u + 1)}
      (F := Scheme.smallModelComparisonInclusion.{u, v} X)
      (constructibleComparisonRingMap.{u, v} X A)
  let adj : L ⊣ R := SheafOfModules.pullbackPushforwardAdjunction.{max v (u + 1)}
        (F := Scheme.smallModelComparisonInclusion.{u, v} X)
    (constructibleComparisonRingMap.{u, v} X A)
  have : PreservesFiniteLimits L := (constructibleComparisonPullback_exact_faithful.{u, v} X A).1
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint L
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : R.Additive := adj.right_adjoint_additive
  have : R.IsRightAdjoint := adj.isRightAdjoint
  have : PreservesFiniteLimits R := inferInstance
  have : IsIso adj.derivedPlus.unit := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    exact adj.isIso_derivedPlus_unit_app_of_rightAcyclic
      (fun I _ ↦ (coefficientComparison_injectiveAcyclic.{u, v} X A adj I).1)
      (fun I _ ↦ (coefficientComparison_injectiveAcyclic.{u, v} X A adj I).2) K
  obtain ⟨eD⟩ := hD
  let Q := ConstantCompletion.Q (ConstantCompletion.constant
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A)
  let W := HomologicalComplex.quasiIso C (.up ℤ)
  let T := constructibleComparisonComplexPullback.{u, v} X A ⋙ ConstantCompletion.Q _
  let : Localization.Lifting Q W T D := ⟨eD⟩
  let : Localization.Lifting Q W T L.mapDerivedCategory := ⟨L.mapDerivedCategoryFactors⟩
  let e : L.mapDerivedCategory ≅ D :=
    Localization.liftNatIso Q W T T L.mapDerivedCategory D (Iso.refl _)
  constructor
  · intro K M hK hM
    obtain ⟨a, b, hab, hK⟩ := hK
    obtain ⟨c, d, hcd, hM⟩ := hM
    have hgeK : K.IsGE a := (DerivedCategory.isGE_iff K a).mpr
      (fun q hq ↦ hK q (Or.inl hq))
    have hgeM : M.IsGE c := (DerivedCategory.isGE_iff M c).mpr
      (fun q hq ↦ hM q (Or.inl hq))
    let Kp : DerivedCategory.Plus C := ⟨K, a, hgeK⟩
    let Mp : DerivedCategory.Plus C := ⟨M, c, hgeM⟩
    have hb := boundedBelow_map_bijective adj Kp Mp
    let t : (L.mapDerivedCategory.obj K ⟶ L.mapDerivedCategory.obj M) ≃
        (D.obj K ⟶ D.obj M) := (e.app K).homCongr (e.app M)
    have heq : (D.map : (K ⟶ M) → _) = t ∘ L.mapDerivedCategory.map := by
      funext f
      change D.map f = e.inv.app K ≫ L.mapDerivedCategory.map f ≫ e.hom.app M
      rw [e.hom.naturality f, Iso.inv_hom_id_app_assoc]
    rw [heq]
    exact t.bijective.comp hb
  · intro K hK hclass
    obtain ⟨a, b, hab, hK⟩ := hK
    have hge : K.IsGE a := (DerivedCategory.isGE_iff K a).mpr
      (fun q hq ↦ hK q (Or.inl hq))
    have hle : K.IsLE b := (DerivedCategory.isLE_iff K b).mpr
      (fun q hq ↦ hK q (Or.inr hq))
    let Kp : DerivedCategory.Plus E := ⟨K, a, hge⟩
    have : Kp.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff Kp a).mp hge
    have : Kp.IsLE b := (DerivedCategory.Plus.isLE_ι_obj_iff Kp b).mp hle
    have horigin : ∀ q, L.essImage
        ((DerivedCategory.Plus.homologyFunctor E q).obj Kp) := by
      intro q
      exact coefficientClassicalModule_origin.{u, v} X A
        ((coefficientModelCohomology _ q).obj K) (hclass q)
    obtain ⟨M, ⟨hM⟩⟩ := bounded_origin_of_homology_origin adj Kp a b horigin
    exact ⟨M, ⟨(e.app M).symm ≪≫ hM⟩⟩
end AlgebraicGeometry.ProEtale
