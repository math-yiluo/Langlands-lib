import Langlands.Representation.Plancherel.AvailableRenardAmbientComparison
import Langlands.Representation.Plancherel.RenardLeviCentralizerCompatibility
import Langlands.BruhatTits.SpecialCompact.AvailableSpecialLeviCompactProof
import Langlands.BruhatTits.SpecialCompact.JointBasisReductionProof
import Langlands.Geometry.Building.CrossTorusComposition

/-! # Cartan compatibility at the same compact subgroup under global validity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.GroupScheme.RealTorusSpace Langlands.BruhatTits.Cartan

namespace Langlands.Plancherel.RenardCartan

section CentralizerTransport

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- Coverage and norm-kernel classification are independent of the representative
of the same actual torus centralizer. -/
theorem specialCompactCartanComparison_changeCentralizer
    (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
    (ν : cocharacterLattice S) (C E : CentralizerDatum i)
    (hc : SpecialCompactCartanComparison D x ν C.j C.s C.bijective) :
    SpecialCompactCartanComparison D x ν E.j E.s E.bijective := by
  let ψ := C.basedComparisonIso E (Iso.refl S) (Iso.refl G)
    (torusTransport_identity_square i)
  have hmap (z : rationalPoints C.Z) :
      rationalPoints.map E.j (rationalPoints.map ψ.hom z) = rationalPoints.map C.j z := by
    simpa only [rationalPoints.map_apply, Iso.refl_hom, Grp.id_hom_hom,
      Category.comp_id] using C.basedComparisonIso_map_comp E (Iso.refl S) (Iso.refl G)
        (torusTransport_identity_square i) z
  have hval (z : rationalPoints C.Z) :
      (centralizerValuation E.s E.bijective (rationalPoints.map ψ.hom z)).toAdd =
        (centralizerValuation C.s C.bijective z).toAdd := by
    have ht := C.basedComparisonIso_translation E (Iso.refl S) (Iso.refl G)
      (torusTransport_identity_square i) z
    simp only [cocharacterRealCongr_refl] at ht
    change -(centralizerValuation C.s C.bijective z).toAdd =
      -(centralizerValuation E.s E.bijective (rationalPoints.map ψ.hom z)).toAdd at ht
    exact neg_injective ht.symm
  have hdom (z : rationalPoints C.Z) :
      rationalPoints.map ψ.hom z ∈ dominantCentralizer i ν E.s E.bijective ↔
        z ∈ dominantCentralizer i ν C.s C.bijective := by
    simp only [dominantCentralizer, Set.mem_ofPred_eq, hval]
  constructor
  · intro g
    obtain ⟨z, hz⟩ := hc.1 g
    refine ⟨⟨rationalPoints.map ψ.hom z.val, (hdom z.val).mpr z.property⟩, ?_⟩
    change DoubleCoset.mk _ _ (rationalPoints.map E.j (rationalPoints.map ψ.hom z.val)) = _
    rw [hmap]
    exact hz
  · rintro ⟨z, hz⟩ ⟨z', hz'⟩
    obtain ⟨a, rfl⟩ := (isoPointsEquiv ψ (Over.mk (𝟙 _))).surjective z
    obtain ⟨b, rfl⟩ := (isoPointsEquiv ψ (Over.mk (𝟙 _))).surjective z'
    change DoubleCoset.mk _ _ (rationalPoints.map E.j (rationalPoints.map ψ.hom a)) =
        DoubleCoset.mk _ _ (rationalPoints.map E.j (rationalPoints.map ψ.hom b)) ↔
      rationalPoints.map ψ.hom b * (rationalPoints.map ψ.hom a)⁻¹ ∈ rationalCommonNormKernel E.Z
    rw [hmap, hmap, ← map_inv, ← map_mul, ValuationBuildingData.mem_rationalCommonNormKernel_mapIso_iff]
    exact hc.2 ⟨a, (hdom a).mp hz⟩ ⟨b, (hdom b).mp hz'⟩

/-- A Cartan comparison on an available apartment with the prescribed torus and
compact subgroup gives coverage and classification on that subgroup for any
actual representative of its torus centralizer. -/
theorem specialCompactCartanComparison_on_subgroup_of_heq
    {S' : CommGroupScheme (Spec (CommRingCat.of F))}
    {i' : S'.toGrp ⟶ G} [Mono i'.hom.hom.left]
    (D' : KPApartmentData i' (localFieldOrder F)) (x' : D'.Apartment)
    (C : CentralizerDatum i') (E : CentralizerDatum i)
    (hS : S' = S) (hi : HEq i' i)
    (K : Subgroup (rationalPoints G)) (hK : D'.specialCompactSubgroup x' = K)
    (hc : ∀ ν' : cocharacterLattice S', IsGenericCocharacter i' ν' →
      SpecialCompactCartanComparison D' x' ν' C.j C.s C.bijective)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν) :
    (∀ g : rationalPoints G, ∃ z : dominantCentralizer i ν E.s E.bijective,
      DoubleCoset.mk K K (rationalPoints.map E.j z.val) = DoubleCoset.mk K K g) ∧
    (∀ a b : dominantCentralizer i ν E.s E.bijective,
      DoubleCoset.mk K K (rationalPoints.map E.j a.val) =
          DoubleCoset.mk K K (rationalPoints.map E.j b.val) ↔
        b.val * a.val⁻¹ ∈ rationalCommonNormKernel E.Z) := by
  subst hS
  obtain rfl := eq_of_heq hi
  subst K
  exact specialCompactCartanComparison_changeCentralizer D' x' ν C E (hc ν hν)

end CentralizerTransport

section ValidAssignment

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)

/-- Global validity supplies the comparison on the fixed ambient compact's
Levi preimage, using the canonical factor of the ambient centralizer. -/
theorem validSameCompactLeviCartanComparison :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid →
      let B := (𝔅.datum F G hG).base
      ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
        ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
          ∀ J ⊆ simpleRelativeRoots B.i ν,
            SameCompactLeviCartanComparison B.apartment x ν J
              (standardLeviCentralizerDatum B.i B.centralizer ν J).j
              B.centralizer.s B.centralizer.bijective := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν x hx J hJ
  let B := (𝔅.datum F G hG).base
  let : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
  let : Mono (Standard.leviTorusHom B.i ν J).hom.hom.left :=
    mono_of_isMaximalSplitTorus
      (Standard.isMaximalSplitTorus_leviTorusHom B.i ν J B.isMaximalSplitTorus)
  let CM := standardLeviCentralizerDatum B.i B.centralizer ν J
  obtain ⟨hM, 𝔅M, hAM, hSM, hiM, xM, hxM, hK⟩ :=
    Langlands.BruhatTits.SpecialCompact.availableSpecialLeviCompact
      F G hG 𝔅 h𝔅 ν hν x hx J hJ
  let BM := (𝔅M.datum F (Standard.leviScheme B.i ν J) hM).base
  exact specialCompactCartanComparison_on_subgroup_of_heq BM.apartment xM
    BM.centralizer CM hSM hiM _ hK
    (fun ν' hν' =>
      (availableSpecialCompactRenardComparison F _ hM 𝔅M hAM ν' hν' xM hxM).1)
    ν (Langlands.BruhatTits.SpecialCompact.isGenericCocharacter_leviTorusHom hν J)

/-- The actual Levi valuation chamber parametrizes the fixed compact's Levi
double cosets under global validity, with no Cartan comparison premise. -/
def validSpecialCompactStandardLeviChamberEquiv :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (𝔅 : KPBuildingAssignment.{u}) (_ : 𝔅.IsValid),
      let B := (𝔅.datum F G hG).base
      ∀ (ν : cocharacterLattice B.S) (_ : IsGenericCocharacter B.i ν)
        (x : B.Apartment) (_ : B.apartment.IsSpecialApartmentVertex x)
        (J : Set (characterLattice B.S)) (_ : J ⊆ simpleRelativeRoots B.i ν),
        haveI : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
          (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
        dominantValuationImage (Standard.leviTorusHom B.i ν J) ν
            B.centralizer.s B.centralizer.bijective ≃
          DoubleCoset.Quotient
            (B.apartment.specialCompactLeviSubgroup ν J x :
              Set (rationalPoints (Standard.leviScheme B.i ν J)))
            (B.apartment.specialCompactLeviSubgroup ν J x) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν x hx J hJ
  let B := (𝔅.datum F G hG).base
  let : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
  exact sameCompactLeviChamberEquiv B.apartment x ν J
    (standardLeviCentralizerDatum B.i B.centralizer ν J).j
    B.centralizer.s B.centralizer.bijective
    (validSameCompactLeviCartanComparison F G hG 𝔅 h𝔅 ν hν x hx J hJ)

/-- Global validity supplies the ambient and same-compact standard-Levi
comparisons at the original special vertex and centralizer. -/
theorem validSpecialCompactRenardCartanComparison :
    haveI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ 𝔅 : KPBuildingAssignment.{u}, 𝔅.IsValid →
      let B := (𝔅.datum F G hG).base
      ∀ ν : cocharacterLattice B.S, IsGenericCocharacter B.i ν →
        ∀ x : B.Apartment, B.apartment.IsSpecialApartmentVertex x →
          SpecialCompactRenardComparison B.apartment x ν
              B.centralizer.j B.centralizer.s B.centralizer.bijective ∧
            SpecialCompactStandardLeviCompatibility B.apartment x ν
              B.centralizer.s B.centralizer.bijective B.centralizer.j := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  intro 𝔅 h𝔅
  dsimp only
  intro ν hν x hx
  let B := (𝔅.datum F G hG).base
  have hA : 𝔅.IsAvailableFor F G hG := h𝔅.isAvailableFor
  refine ⟨availableSpecialCompactRenardComparison F G hG 𝔅 hA ν hν x hx, ?_⟩
  intro J hJ
  let : IsAffineHom (Standard.leviScheme B.i ν J).X.hom :=
    (Standard.isClosedSubgroup_leviHom B.i ν J).isAffineHom
  let : Mono (Standard.leviTorusHom B.i ν J).hom.hom.left :=
    mono_of_isMaximalSplitTorus
      (Standard.isMaximalSplitTorus_leviTorusHom B.i ν J B.isMaximalSplitTorus)
  let CM := standardLeviCentralizerDatum B.i B.centralizer ν J
  have hcompare := validSameCompactLeviCartanComparison F G hG 𝔅 h𝔅 ν hν x hx J hJ
  exact ⟨CM.j, CM.isClosedSubgroup, CM.isRepresentedBy,
    standardLeviCentralizerFactor_comp B.i ν J B.centralizer.j
      B.centralizer.isRepresentedBy,
    CM.comp_eq, positiveRelativeRoots_standardLevi_subset B.i ν J, hcompare,
    dominantLattice_standardLevi B.i B.isMaximalSplitTorus ν
      B.centralizer.s B.centralizer.bijective J⟩

end ValidAssignment

end Langlands.Plancherel.RenardCartan
