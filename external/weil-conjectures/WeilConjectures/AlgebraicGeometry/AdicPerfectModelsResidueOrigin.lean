/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import all WeilConjectures.AlgebraicGeometry.AdicConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.AdicPerfectModelsCohomologicalBounds
import WeilConjectures.AlgebraicGeometry.AdicPerfectModelsCompleteness
import WeilConjectures.AlgebraicGeometry.AdicPerfectModelsResidueHomology

/-! # Completeness, bounds and etale residue origin from perfect local models

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication, and Lemma 6.5.3.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

private theorem bounded_residueOrigin (X : Scheme.{u})
    (k : Type (u + 1)) [Field k]
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k)))
    (hb : ∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, q < a ∨ b < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj K))
    (hc : ∀ q : ℤ, ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k),
      IsConstructibleSheaf G ∧
        Nonempty ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X).obj G ≅
          (DerivedCategory.homologyFunctor _ q).obj K)) :
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} k) X K := by
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X
  let P : ObjectProperty (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k)) :=
    fun F ↦ ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k),
      IsConstructibleSheaf G ∧ Nonempty (N.obj G ≅ F)
  have : P.IsClosedUnderIsomorphisms := ⟨by
    rintro F G e ⟨H, hH, ⟨d⟩⟩
    exact ⟨H, hH, ⟨d ≪≫ e⟩⟩⟩
  let Q := ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} k) X
  have : Q.IsTriangulated := etaleOrigin_triangulated X k
  apply DerivedCategory.prop_of_bounded Q P
  · rintro F ⟨G, hG, ⟨e⟩⟩
    have := hG
    exact ⟨(DerivedCategory.singleFunctor _ 0).obj G,
      Etale.DerivedCategory.boundedConstructible_singleFunctor_obj G 0,
      ⟨(N.mapDerivedCategorySingleFunctor 0).app G ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso e⟩⟩
  · obtain ⟨a, b, _, h⟩ := hb
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).mpr (fun q hq ↦ h q (.inl hq))⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).mpr (fun q hq ↦ h q (.inr hq))⟩⟩
  · exact hc

/-- Stratified perfect models give global completeness and bounds, and bounded
constructible etale origin of the residue. The Tor condition is deliberately separate:
it follows from field-valued tensor exactness.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication, and Lemma 6.5.3
(auxiliary; not a blueprint node).

Proof: On each model cover, transport the given finite-projective complex to the small
site and apply adicPerfectModel_complete_reduction. It gives completeness and vanishing
of both the model and its residue outside the termwise bounds; the residue cohomology
is the constant realization of finite-dimensional coefficient cohomology. Restriction
along the stratum immersion and then to the slice commutes with this calculation by
the finite-projection scalar comparisons. Detect completeness by
adicStratumCompletionUnit_detection. For bounds, choose finitely many quasi-compact
pieces of the covering schemes over each of the finitely many Noetherian strata, and
take the minimum of their lower bounds and maximum of their upper bounds. Exact
restriction commutes with cohomology and finite-stratum detection proves the global
vanishing, for K and its residue separately. This is
exists_global_bounds_of_stratified_local_bounds. If the selected family is empty, use
[0,0] and the empty-cover sheaf axiom. The residue cohomology is intrinsically
constructible on the given strata, with finite-dimensional, hence finitely presented,
constant module values. Noetherian global constructibility and the bounded derived
constructible comparison equivalence descend this bounded residue to an etale complex
C. Exact fully faithful comparison identifies its cohomology, bounds and the required
residue isomorphism. Fixed-scalar restriction and the small-site equivalences give the
stated presentation without changing the coefficients or the quotient projection. -/
theorem adicPerfectModels_residueOrigin (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) :
    IsSfbAdicComplete X I K ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
      ∃ C : CochainComplex
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ,
        (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q)) ∧
        (∀ q : ℤ, IsConstructibleSheaf (C.homology q)) ∧
        Nonempty (DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅
          DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex
                (.up ℤ)).obj C)) := by
  classical
  have hmax : (I ^ (0 + 1)).IsMaximal := by simpa using hI.1
  let := hmax
  let k := A ⧸ I ^ (0 + 1)
  let : Field k := Ideal.Quotient.field _
  obtain ⟨hbound, hresidue⟩ := adicPerfectModels_cohomologicalBounds X A I hI K hK
  refine ⟨adicPerfectModels_completeness X A I hI K hK, hbound, ?_⟩
  let R := DerivedCategory.Q.obj (sfbResidueComplex X I K)
  obtain ⟨M, ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩, ⟨e⟩⟩ :=
    bounded_residueOrigin X k R hresidue
      (adicPerfectModels_residueHomology X A I hI K hK)
  let C := DerivedCategory.Q.objPreimage M
  let eC := DerivedCategory.Q.objObjPreimageIso M
  let ec (q : ℤ) : C.homology q ≅ (DerivedCategory.homologyFunctor _ q).obj M :=
    ((DerivedCategory.homologyFunctorFactors _ q).app C).symm ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso eC
  refine ⟨C, ⟨min a b, max a b, min_le_max, ?_⟩, ?_, ?_⟩
  · intro q hq
    rcases hq with hq | hq
    · exact ((DerivedCategory.isGE_iff M a).mp ha q
        (lt_of_lt_of_le hq (min_le_left _ _))).of_iso (ec q)
    · exact ((DerivedCategory.isLE_iff M b).mp hb q
        (lt_of_le_of_lt (le_max_right _ _) hq)).of_iso (ec q)
  · intro q
    have : IsConstructibleSheaf ((DerivedCategory.homologyFunctor _ q).obj M) := hc q
    exact IsConstructibleSheaf.of_iso (ec q).symm
  · let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} k) X
    exact ⟨e.symm ≪≫ N.mapDerivedCategory.mapIso eC.symm ≪≫
      N.mapDerivedCategoryFactors.app C⟩

end AlgebraicGeometry.Scheme
