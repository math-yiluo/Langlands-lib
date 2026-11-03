import Langlands.Representation.Aubert.General.Parabolic
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Jacquet.IwahoriStablePairingData
import Langlands.Representation.Jacquet.IwahoriStablePairingAdmits

/-! # Coherent normalized Jacquet duality from opposite Iwahori contractions -/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.Aubert.General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]

/-- A chosen family of opposite normalized Jacquet duality isomorphisms on
admissible objects, together with its naturality for every actual morphism. -/
structure NaturalNormalizedJacquetDuality
    (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O) where
  iso : ∀ (A : SmoothRep.{0, uG, uV} ℂ G), A.IsAdmissible →
    ((normalizedJacquetFunctor.{uG, uV} U M hU hMU).obj A.contragredient ≅
      ((normalizedJacquetFunctor.{uG, uV} O M hO hMO).obj A).contragredient)
  naturality : ∀ (A B : SmoothRep.{0, uG, uV} ℂ G)
    (hA : A.IsAdmissible) (hB : B.IsAdmissible) (f : A ⟶ B),
    (normalizedJacquetFunctor.{uG, uV} U M hU hMU).map
        (SmoothRep.contragredientHom f) ≫ (iso A hA).hom =
      (iso B hB).hom ≫ SmoothRep.contragredientHom
        ((normalizedJacquetFunctor.{uG, uV} O M hO hMO).map f)

/-- The actual normalized Jacquet functors admit a coherent duality family on
admissible objects when the same element gives cofinal opposite Iwahori
contractions and the actual inverse-half Haar characters are reciprocal. -/
theorem exists_naturalNormalizedJacquetDuality_of_iwahoriContractions
    (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O)
    (g : G) (hc : ∀ m ∈ M, m * g = g * m)
    (hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g)
    (hχ : ∀ m : M,
      (HaarModulus.closedInverseHalfCharacter U hU M hMU m : ℂ) *
        (HaarModulus.closedInverseHalfCharacter O hO M hMO m : ℂ) = 1) :
    let rU := normalizedJacquetFunctor.{uG, uV} U M hU hMU
    let rO := normalizedJacquetFunctor.{uG, uV} O M hO hMO
    ∃ E : ∀ (A : SmoothRep.{0, uG, uV} ℂ G), A.IsAdmissible →
        (rU.obj A.contragredient ≅ (rO.obj A).contragredient),
      ∀ (A B : SmoothRep.{0, uG, uV} ℂ G)
        (hA : A.IsAdmissible) (hB : B.IsAdmissible) (f : A ⟶ B),
        rU.map (SmoothRep.contragredientHom f) ≫ (E A hA).hom =
          (E B hB).hom ≫ SmoothRep.contragredientHom (rO.map f) := by
  let rU := normalizedJacquetFunctor.{uG, uV} U M hU hMU
  let rO := normalizedJacquetFunctor.{uG, uV} O M hO hMO
  let χU := HaarModulus.closedInverseHalfCharacter U hU M hMU
  let χO := HaarModulus.closedInverseHalfCharacter O hO M hMO
  have hχO : IsOpen (χO.ker : Set M) :=
    HaarModulus.isOpen_ker_closedInverseHalfCharacter O hO M hMO
  let D := Jacquet.stablePairingDataOfIwahoriContractions U M O hMU hMO g hc hBasis
  have hAdm (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible) :
      D.Admits A.representation A.isSmooth :=
    D.admits_of_iwahoriContractions A.representation hA
      (fun _ hK => hK.2.1) (fun _ hK => hK.2.2)
  let Q (A : SmoothRep.{0, uG, uV} ℂ G) : SmoothRep.{0, uG, uV} ℂ M :=
    SmoothRep.of (Jacquet.characterTwistedAction A.representation O M hMO χO)
      (Jacquet.isSmooth_characterTwistedAction A.representation O M hMO χO hχO A.isSmooth)
  let eO (A : SmoothRep.{0, uG, uV} ℂ G) : rO.obj A ≅ Q A :=
    SmoothRep.mkIso (twistEquiv χO (Jacquet.Localization.trivialEquiv A.representation O M hMO))
  have key : ∀ (A : SmoothRep.{0, uG, uV} ℂ G) (hA : A.IsAdmissible),
      ∃ b : Jacquet.Coinvariants (smoothContragredient A.representation) U →ₗ[ℂ]
          Jacquet.Coinvariants A.representation O →ₗ[ℂ] ℂ,
        D.IsStablePairing A.representation A.isSmooth b ∧
        ∃ E : rU.obj A.contragredient ≅ (rO.obj A).contragredient,
          ∀ x y, (SmoothRep.hom E.hom x).val y =
            b (Jacquet.Localization.trivialEquiv
              (smoothContragredient A.representation) U M hMU x)
              (Jacquet.Localization.trivialEquiv A.representation O M hMO y) := by
    intro A hA
    obtain ⟨b, hb⟩ := D.exists_isStablePairing (hAdm A hA)
    refine ⟨b, hb, ?_⟩
    obtain ⟨E, hE⟩ := hb.exists_equiv (hAdm A hA) (ContinuousMulEquiv.refl M)
      (fun m => (χU m : ℂ)) χO hχ hχO
      (rU.obj A.contragredient).representation
      (Jacquet.Localization.trivialEquiv
        (smoothContragredient A.representation) U M hMU).toLinearEquiv
      (fun m x => by
        obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
          (smoothContragredient A.representation) U 1 x
        change Jacquet.Localization.trivialEquiv
          (smoothContragredient A.representation) U M hMU
            ((χU m : ℂ) • Jacquet.Localization.mk
              (smoothContragredient A.representation) U 1
                (smoothContragredient A.representation m v)) = _
        rw [map_smul]
        rfl)
      (Q A).representation (fun _ _ => rfl)
    refine ⟨SmoothRep.mkIso E ≪≫ SmoothRep.contragredientIso (eO A), ?_⟩
    intro x y
    change (E x).val
      (Jacquet.Localization.trivialEquiv A.representation O M hMO y) = _
    exact hE x _
  choose b hb E hE using key
  refine ⟨E, ?_⟩
  intro A B hA hB f
  apply ObjectProperty.hom_ext
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply LinearMap.ext
  intro y
  change (SmoothRep.hom (E A hA).hom
      (SmoothRep.hom (rU.map (SmoothRep.contragredientHom f)) x)).val y =
    (SmoothRep.hom (E B hB).hom x).val (SmoothRep.hom (rO.map f) y)
  rw [hE, hE]
  obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
    (smoothContragredient B.representation) U 1 x
  obtain ⟨w, rfl⟩ := Jacquet.Localization.mk_surjective A.representation O 1 y
  exact (hb A hA).natural (hAdm A hA) (hb B hB) (SmoothRep.hom f)
    (Jacquet.mk (smoothContragredient B.representation) U v) (Jacquet.mk A.representation O w)

/-- Full reciprocity of the actual Haar characters implies the inverse-half
reciprocity required by coherent normalized Jacquet duality. -/
theorem exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus
    (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O)
    (g : G) (hc : ∀ m ∈ M, m * g = g * m)
    (hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g)
    (hδ : ∀ m : M,
      HaarModulus.closedRestrictCharacter U hU M hMU m *
        HaarModulus.closedRestrictCharacter O hO M hMO m = 1) :
    let rU := normalizedJacquetFunctor.{uG, uV} U M hU hMU
    let rO := normalizedJacquetFunctor.{uG, uV} O M hO hMO
    ∃ E : ∀ (A : SmoothRep.{0, uG, uV} ℂ G), A.IsAdmissible →
        (rU.obj A.contragredient ≅ (rO.obj A).contragredient),
      ∀ (A B : SmoothRep.{0, uG, uV} ℂ G)
        (hA : A.IsAdmissible) (hB : B.IsAdmissible) (f : A ⟶ B),
        rU.map (SmoothRep.contragredientHom f) ≫ (E A hA).hom =
          (E B hB).hom ≫ SmoothRep.contragredientHom (rO.map f) := by
  apply exists_naturalNormalizedJacquetDuality_of_iwahoriContractions
    U M O hU hO hMU hMO g hc hBasis
  intro m
  let F : ℝ≥0ˣ →* ℂˣ :=
    (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom).comp
      (Units.map NNReal.sqrtHom.toMonoidHom)
  change ((F (HaarModulus.closedRestrictCharacter U hU M hMU m))⁻¹ : ℂˣ).val *
    ((F (HaarModulus.closedRestrictCharacter O hO M hMO m))⁻¹ : ℂˣ).val = 1
  rw [← Units.val_mul, ← mul_inv, ← map_mul, hδ m, map_one, inv_one]
  rfl

/-- Choose the coherent duality family furnished by opposite Iwahori
contractions and full reciprocity of the actual Haar characters. -/
def naturalNormalizedJacquetDualityOfIwahoriContractionsOfReciprocalModulus
    (U M O : Subgroup G) (hU : IsClosed (U : Set G)) (hO : IsClosed (O : Set G))
    (hMU : M ≤ Subgroup.normalizer U) (hMO : M ≤ Subgroup.normalizer O)
    (g : G) (hc : ∀ m ∈ M, m * g = g * m)
    (hBasis : Jacquet.HasOppositeIwahoriContractionBasis U M O g)
    (hδ : ∀ m : M,
      HaarModulus.closedRestrictCharacter U hU M hMU m *
        HaarModulus.closedRestrictCharacter O hO M hMO m = 1) :
    NaturalNormalizedJacquetDuality.{uG, uV} U M O hU hO hMU hMO :=
  let h := exists_naturalNormalizedJacquetDuality_of_iwahoriContractions_of_reciprocalModulus
    U M O hU hO hMU hMO g hc hBasis hδ
  ⟨Classical.choose h, Classical.choose_spec h⟩

end Langlands.Aubert.General
