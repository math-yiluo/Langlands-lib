/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.AdicResidueFieldTensor
import WeilConjectures.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The bounded constructible residue locus is triangulated

Source: Bhatt--Scholze, the residue condition and the observation following Definition 6.5.1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- Bounded constructible etale origin with finite Tor amplitude of the residue.
Source: Bhatt--Scholze, Definition 6.5.1, condition on the first derived reduction
(auxiliary; not a blueprint node). -/
def SfbConstructibleResidue (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
    ∃ C : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ,
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q)) ∧
      (∀ q : ℤ, IsConstructibleSheaf (C.homology q)) ∧
      Nonempty (DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅
        DerivedCategory.Q.obj
          (((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex (.up ℤ)).obj C)) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))))
          (q : ℤ), (q < a ∨ b < q) →
            IsZero ((sfbEtaleTensorDegreeZero X (A ⧸ I ^ (0 + 1)) C N).homology q)

private theorem fixedScalar_exact (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    PreservesFiniteLimits (sfbFixedScalarRestriction X k) ∧
      PreservesFiniteColimits (sfbFixedScalarRestriction X k) := by
  let F := sfbFixedScalarRestriction X k
  let T := sheafCompose (ProEt.topology X)
    (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1})
  have hlimT : PreservesFiniteLimits T := by
    have : PreservesFiniteLimits (T ⋙ sheafToPresheaf _ _) :=
      inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
        (Functor.whiskeringRight _ _ _).obj
          (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1})))
    exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
  have hleft : (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom k)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} (Int.castRingHom k)).isLeftAdjoint
    exact inferInstanceAs (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom k) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
  have hcolT : PreservesFiniteColimits T := by
    let adj := Adjunction.ofIsLeftAdjoint
      (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1})
    have : PreservesLimitsOfSize.{u, u + 1}
        (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).rightAdjoint :=
      adj.rightAdjoint_preservesLimits
    have : (ProEt.topology X).HasSheafCompose
        (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}).rightAdjoint :=
      hasSheafCompose_of_preservesLimitsOfSize _
    have : T.IsLeftAdjoint := (sheafComposeAdjunction (ProEt.topology X) adj).isLeftAdjoint
    infer_instance
  have : ReflectsFiniteLimits T :=
    { reflects := fun _ _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms }
  have : ReflectsFiniteColimits T :=
    { reflects := fun _ _ _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteLimits (F ⋙ T) := by
    change PreservesFiniteLimits (SheafOfModules.toSheaf
      ((adicLisseForget X).obj (adicLisseConstantRing X k)))
    infer_instance
  have : PreservesFiniteColimits (F ⋙ T) := by
    change PreservesFiniteColimits (SheafOfModules.toSheaf
      ((adicLisseForget X).obj (adicLisseConstantRing X k)))
    infer_instance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F T,
    preservesFiniteColimits_of_reflects_of_preserves F T⟩

private theorem etaleOrigin_triangulated (X : Scheme.{u}) (k : Type (u + 1)) [Field k] :
    (ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} k) X).IsTriangulated := by
  let P := Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} k) X
  have : (Etale.constructibleSheaf (ModuleCat.{u + 1} k) X).IsClosedUnderExtensions := by
    constructor
    intro S hS h₁ h₃
    have := (Etale.constructibleSheaf_iff _ _ _).mp h₁
    have := (Etale.constructibleSheaf_iff _ _ _).mp h₃
    exact (Etale.constructibleSheaf_iff _ _ _).mpr
      (IsConstructibleSheaf.of_shortExact_of_isNoetherianRing hS)
  let F := P.ι ⋙ (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).mapDerivedCategory
  have : F.Full := ⟨fun {K L} f ↦ by
    obtain ⟨g, hg⟩ := (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
      K.obj L.obj L.property.1.1).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩⟩
  have hp : ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} k) X =
      F.essImage := by
    funext K
    apply propext
    constructor
    · rintro ⟨L, hL, e⟩
      exact ⟨⟨L, hL⟩, e⟩
    · rintro ⟨L, e⟩
      exact ⟨L.obj, L.property, e⟩
  rw [hp]
  infer_instance

/-- The bounded constructible residue condition is invariant under isomorphisms
and triangulated. Completeness is a separate vanishing condition.
Source: Bhatt--Scholze, Definition 6.5.1, observation following the definition
(auxiliary; not a blueprint node).

Proof: Fixed-scalar restriction retains the underlying additive sheaf. Forgetting
scalar structure preserves finite limits and colimits and reflects them, so this
restriction is exact. Derived reduction and its composite with this exact functor
are triangulated. On the etale site, bounded complexes with constructible cohomology
are triangulated: kernels and cokernels are constructible, and the Noetherian
extension argument applies also to infinite residue fields. Derived comparison is
fully faithful on bounded-below objects, so its restriction to these bounded objects
has triangulated essential image. The residue condition is the inverse image of
this essential image under the preceding composite. To check this equality, pass
between an etale derived object and its quotient-functor preimage using the canonical
isomorphism, and transport homology, constructibility and bounds along that
isomorphism. Over the residue field tensor with every etale module sheaf is exact,
so these bounds imply the Tor clause. Inverse image preserves isomorphism closure
and triangulatedness. This includes empty X and infinite residue fields. -/
theorem adicConstructible_residueTriangulated (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A]
    (I : Ideal A) (hI : I.IsMaximal) :
    ObjectProperty.IsClosedUnderIsomorphisms (SfbConstructibleResidue X I) ∧
      ObjectProperty.IsTriangulated (SfbConstructibleResidue X I) := by
  classical
  have hmax : (I ^ (0 + 1)).IsMaximal := by simpa using hI
  let := hmax
  let k := A ⧸ I ^ (0 + 1)
  let : Field k := Ideal.Quotient.field _
  let F := sfbFixedScalarRestriction X k
  have : PreservesFiniteLimits F := (fixedScalar_exact X k).1
  have : PreservesFiniteColimits F := (fixedScalar_exact X k).2
  let L := completedAdicDerivedChange X (limit.π (adicLisseRingSystem X I) (op 0))
  have hL := (completedAdicChangeData X
    (limit.π (adicLisseRingSystem X I) (op 0))).choose_spec.choose_spec.choose_spec.choose_spec.2.2
  obtain ⟨sL, tL⟩ := hL.choose_spec.choose_spec.2.1
  let : L.CommShift ℤ := sL
  have : L.IsTriangulated := tL
  let D := L ⋙ F.mapDerivedCategory
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X
  let P := ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} k) X
  have : P.IsTriangulated := etaleOrigin_triangulated X k
  let c (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
      DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅ D.obj K :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage (L.obj K))).symm ≪≫
      F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso (L.obj K))
  have hp : SfbConstructibleResidue X I = P.inverseImage D := by
    funext K
    apply propext
    constructor
    · rintro ⟨C, ⟨a, b, hab, hb⟩, hc, ⟨e⟩, _⟩
      have hQC : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} k) X
          (DerivedCategory.Q.obj C) := by
        refine ⟨⟨⟨a, (DerivedCategory.isGE_iff _ a).mpr ?_⟩,
          ⟨b, (DerivedCategory.isLE_iff _ b).mpr ?_⟩⟩, ?_⟩
        · intro q hq
          exact (hb q (Or.inl hq)).of_iso
            ((DerivedCategory.homologyFunctorFactors _ q).app C)
        · intro q hq
          exact (hb q (Or.inr hq)).of_iso
            ((DerivedCategory.homologyFunctorFactors _ q).app C)
        · intro q
          have : IsConstructibleSheaf (C.homology q) := hc q
          exact IsConstructibleSheaf.of_iso (F := C.homology q)
            ((DerivedCategory.homologyFunctorFactors _ q).app C).symm
      exact ⟨DerivedCategory.Q.obj C, hQC,
        ⟨N.mapDerivedCategoryFactors.app C ≪≫ e.symm ≪≫ c K⟩⟩
    · rintro ⟨M, ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩, ⟨e⟩⟩
      let C := DerivedCategory.Q.objPreimage M
      let eC := DerivedCategory.Q.objObjPreimageIso M
      let ec (q : ℤ) : C.homology q ≅ (DerivedCategory.homologyFunctor _ q).obj M :=
        ((DerivedCategory.homologyFunctorFactors _ q).app C).symm ≪≫
          (DerivedCategory.homologyFunctor _ q).mapIso eC
      have hbound : ∀ q : ℤ, (q < min a b ∨ max a b < q) → IsZero (C.homology q) := by
        intro q hq
        rcases hq with hq | hq
        · exact ((DerivedCategory.isGE_iff M a).mp ha q
            (lt_of_lt_of_le hq (min_le_left _ _))).of_iso (ec q)
        · exact ((DerivedCategory.isLE_iff M b).mp hb q
            (lt_of_le_of_lt (le_max_right _ _) hq)).of_iso (ec q)
      refine ⟨C, ⟨min a b, max a b, min_le_max, hbound⟩, ?_, ?_, ?_⟩
      · intro q
        have : IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ q).obj M) := hc q
        exact IsConstructibleSheaf.of_iso (ec q).symm
      · exact ⟨c K ≪≫ e.symm ≪≫ N.mapDerivedCategory.mapIso eC.symm ≪≫
          N.mapDerivedCategoryFactors.app C⟩
      · exact ⟨min a b, max a b, min_le_max,
          sfbFieldTensor_bounds X k C (min a b) (max a b) hbound⟩
  rw [hp]
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
