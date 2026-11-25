/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import WeilConjectures.AlgebraicGeometry.AdicConstructibleLocalModels
import WeilConjectures.AlgebraicGeometry.AdicConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.AdicPerfectModelsResidueOrigin
import WeilConjectures.AlgebraicGeometry.AdicResidueFieldTensor
import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Adic constructibility and stratified perfect models

Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.3 and Proposition 6.6.11
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject MonoidalClosed.FunctorCategory

attribute [local instance] HasDerivedCategory.standard

private theorem sfbCompleteModel_triangulated
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {O S : Sheaf J CommRingCat.{u + 1}} (q : O ⟶ S) :
    ObjectProperty.IsClosedUnderIsomorphisms (ConstantCompletion.IsComplete q) ∧
      ObjectProperty.IsTriangulated (ConstantCompletion.IsComplete q) := by
  classical
  let P : ObjectProperty (ConstantCompletion.D O) := ConstantCompletion.IsComplete q
  let hRshift (U : C) : (ringedDerivedRestriction O U).CommShift ℤ := by
    let F := SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) U
    exact inferInstanceAs (F.mapDerivedCategory.CommShift ℤ)
  let hRtri (U : C) : (ringedDerivedRestriction O U).IsTriangulated := by
    let F := SheafOfModules.overFunctor.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) U
    exact inferInstanceAs (F.mapDerivedCategory.IsTriangulated)
  let H (U : C) (f : O.obj.obj (op U)) :=
    (Functor.curry.obj (derivedInternalHom (J.over U) (O.over U))).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))))
  have hPiso : P.IsClosedUnderIsomorphisms := by
    constructor
    intro K L e hK U f hf
    exact (((ringedDerivedRestriction O U ⋙ H U f).mapIso e).isZero_iff).mp (hK U f hf)
  have hPzero : P (0 : ConstantCompletion.D O) := by
    intro U f _
    obtain ⟨s, ht⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1
      ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f)))
    let G := ringedDerivedRestriction O U ⋙ H U f
    exact G.map_isZero (isZero_zero _)
  have hPshift : P.IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK U f hf
    obtain ⟨s, ht⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1
      ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f)))
    let G := ringedDerivedRestriction O U ⋙ H U f
    exact (((G.commShiftIso n).app K).isZero_iff).mpr
      ((shiftFunctor _ n).map_isZero (hK U f hf))
  have hPtri : P.IsTriangulated := by
    refine {
      exists_zero := ⟨0, isZero_zero _, hPzero⟩
      toIsTriangulatedClosed₂ := .mk' ?_ }
    intro T hT h₁ h₃ U f hf
    obtain ⟨s, ht⟩ := (ringedInternalHom_exact (J.over U) (O.over U)).1
      ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalization (O.over U) (ringedSliceSection O U f)))
    let G := ringedDerivedRestriction O U ⋙ H U f
    exact Pretriangulated.Triangle.isZero₂_of_isZero₁₃ _ (G.map_distinguished T hT)
      (h₁ U f hf) (h₃ U f hf)
  exact ⟨hPiso, hPtri⟩

namespace AlgebraicGeometry.Scheme

private def sfbToModelEquivalence (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :=
  CategoryTheory.Equivalence.mk (proEtaleModuleToModel R) (proEtaleModuleFromModel R)
    (NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget R).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ Iso.refl _))))
    (NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ Iso.refl _))))

private instance sfbToModel_isEquivalence (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) RingCat.{u + 1}) :
    (proEtaleModuleToModel R).IsEquivalence :=
  (sfbToModelEquivalence X R).isEquivalence_functor

private theorem sfbComplete_triangulated (X : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    ObjectProperty.IsClosedUnderIsomorphisms (IsSfbAdicComplete X I) ∧
      ObjectProperty.IsTriangulated (IsSfbAdicComplete X I) := by
  let F : proEtaleRingModules X (adicLisseCompletedRing X I) ⥤
      ConstantCompletion.Mod ((sfbModelRings X).obj (adicLisseCompletedRing X I)) :=
    proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  let : F.Additive := ⟨by intros; ext U x; rfl⟩
  have : F.IsEquivalence := (sfbToModelEquivalence X
    ((adicLisseForget X).obj (adicLisseCompletedRing X I))).isEquivalence_functor
  let := HasDerivedCategory.standard
    (ConstantCompletion.Mod ((sfbModelRings X).obj (adicLisseCompletedRing X I)))
  let G := F.mapDerivedCategory
  let q := (sfbModelRings X).map (limit.π (adicLisseRingSystem X I) (op 0))
  obtain ⟨hi, ht⟩ := sfbCompleteModel_triangulated q
  let P : ObjectProperty _ := ConstantCompletion.IsComplete q
  have : P.IsClosedUnderIsomorphisms := hi
  have : P.IsTriangulated := ht
  let c (N : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :=
    (F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage N)).symm ≪≫
      G.mapIso (DerivedCategory.Q.objObjPreimageIso N)
  have hp : IsSfbAdicComplete X I = P.inverseImage G := by
    funext N
    exact propext (P.prop_iff_of_iso (c N))
  rw [hp]
  exact ⟨inferInstance, inferInstance⟩

/-- Adic constructibility is equivalent to stratified perfect local models; these objects
are bounded and form a full triangulated subcategory.
Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.3 and Proposition 6.6.11
(auxiliary; not a blueprint node).

Proof: The geometric forward lemma gives the finite-projective local representatives;
each represents a perfect object by using itself as witness. The geometric reverse
lemma gives completeness, global cohomological bounds, and a bounded constructible etale
residue representative. Exact tensor over the residue field gives its finite Tor
amplitude in the same interval. These two implications prove the equivalence, and the
reverse lemma gives boundedness.

For the remaining assertions, use an independent categorical argument. Local derived
completeness is the intersection of vanishing conditions for exact slice restriction
followed by derived internal Hom from a section localization. It is therefore closed
under isomorphisms, shifts and triangles. The proved residue-closure theorem expresses
bounded constructible etale residue origin as the inverse image of a triangulated
essential image under exact reduction and fixed-scalar restriction. The intersection of
these two triangulated properties is exactly IsSfbAdicConstructible. Its standard
ObjectProperty API gives zero, isomorphism and shift invariance, and all three ambient
triangle implications. This closure argument does not depend on the geometric lemmas.
All definitions, coefficients, universes and the statement are unchanged. -/
theorem adic_stratified_perfect (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (_hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A] :
    (∀ K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)),
      IsSfbAdicConstructible X I K ↔ IsSfbStratifiedPerfect X I K) ∧
    (∀ K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)),
      IsSfbAdicConstructible X I K → ∃ a b : ℤ, a ≤ b ∧ K.IsGE a ∧ K.IsLE b) ∧
    IsSfbAdicConstructible X I (0 : DerivedCategory
      (proEtaleRingModules X (adicLisseCompletedRing X I))) ∧
    (∀ (K L : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))),
      Nonempty (K ≅ L) → IsSfbAdicConstructible X I K → IsSfbAdicConstructible X I L) ∧
    (∀ (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) (n : ℤ),
      IsSfbAdicConstructible X I K → IsSfbAdicConstructible X I (K⟦n⟧)) ∧
    ∀ T : Triangle (DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))),
      T ∈ distTriang _ →
        (IsSfbAdicConstructible X I T.obj₁ ∧ IsSfbAdicConstructible X I T.obj₂ →
          IsSfbAdicConstructible X I T.obj₃) ∧
        (IsSfbAdicConstructible X I T.obj₂ ∧ IsSfbAdicConstructible X I T.obj₃ →
          IsSfbAdicConstructible X I T.obj₁) ∧
        (IsSfbAdicConstructible X I T.obj₃ ∧ IsSfbAdicConstructible X I T.obj₁ →
          IsSfbAdicConstructible X I T.obj₂) := by
  classical
  have hmax : (I ^ (0 + 1)).IsMaximal := by simpa using _hI.1
  let := hmax
  let k := A ⧸ I ^ (0 + 1)
  let : Field k := Ideal.Quotient.field _
  let P : ObjectProperty
      (DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :=
    IsSfbAdicConstructible X I
  have models (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
      (hK : IsSfbAdicConstructible X I K) : IsSfbStratifiedPerfect X I K := by
    obtain ⟨s, hs, hm⟩ := adicConstructible_localModels X A I _hI K hK
    refine ⟨s, hs, ?_⟩
    intro α
    obtain ⟨V, hV, hmodels⟩ := hm α
    refine ⟨V, hV, ?_⟩
    intro U f hf
    obtain ⟨P, a, b, ha, hb, hP, e⟩ := hmodels U f hf
    exact ⟨P, a, b, ⟨P, a, b, ha, hb, hP, ⟨Iso.refl _⟩⟩, ha, hb, hP, e⟩
  have rev (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
      (hK : IsSfbStratifiedPerfect X I K) : IsSfbAdicConstructible X I K := by
    obtain ⟨hc, _, C, hb, hC, e⟩ := adicPerfectModels_residueOrigin X A I _hI K hK
    refine ⟨hc, C, hb, hC, e, ?_⟩
    obtain ⟨a, b, hab, h⟩ := hb
    exact ⟨a, b, hab, sfbFieldTensor_bounds X k C a b h⟩
  obtain ⟨hciso, hctri⟩ := sfbComplete_triangulated X I
  obtain ⟨hriso, hrtri⟩ := adicConstructible_residueTriangulated X A I _hI.1
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsSfbAdicComplete X I) := hciso
  have : ObjectProperty.IsTriangulated (IsSfbAdicComplete X I) := hctri
  have : ObjectProperty.IsClosedUnderIsomorphisms (SfbConstructibleResidue X I) := hriso
  have : ObjectProperty.IsTriangulated (SfbConstructibleResidue X I) := hrtri
  have : P.IsClosedUnderIsomorphisms :=
    inferInstanceAs (ObjectProperty.IsClosedUnderIsomorphisms
      ((IsSfbAdicComplete X I : ObjectProperty _) ⊓ SfbConstructibleResidue X I))
  have : P.IsTriangulated :=
    inferInstanceAs (ObjectProperty.IsTriangulated
      ((IsSfbAdicComplete X I : ObjectProperty _) ⊓ SfbConstructibleResidue X I))
  refine ⟨?_, ?_, P.prop_zero, ?_, ?_, ?_⟩
  · intro K
    exact ⟨models K, rev K⟩
  · intro K hK
    obtain ⟨_, ⟨a, b, hab, h⟩, _⟩ := adicPerfectModels_residueOrigin X A I _hI K
      (models K hK)
    exact ⟨a, b, hab, (DerivedCategory.isGE_iff K a).mpr
      (fun q hq ↦ h q (Or.inl hq)), (DerivedCategory.isLE_iff K b).mpr
        (fun q hq ↦ h q (Or.inr hq))⟩
  · rintro K L ⟨e⟩ hK
    exact P.prop_of_iso e hK
  · intro K n hK
    exact P.le_shift n K hK
  · intro T hT
    exact ⟨fun h ↦ P.ext_of_isTriangulatedClosed₃ T hT h.1 h.2,
      fun h ↦ P.ext_of_isTriangulatedClosed₁ T hT h.1 h.2,
      fun h ↦ P.ext_of_isTriangulatedClosed₂ T hT h.2 h.1⟩

end AlgebraicGeometry.Scheme
