import Langlands.GroupScheme.Reductive.IsogenyTorusRigidityLocalReduction

/-! # Coordinate tori in the split affine rigidity reduction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G H : GroupScheme S} {T U : CommGroupScheme S}

/-- Replacing the supplied conjugating group by an isomorphic group preserves
the existence of fppf local all-test conjugators. -/
theorem fppfLocallyTorusConjugate_torusIso_iff
    (e : U.toGrp ≅ T.toGrp) (i : T.toGrp ⟶ H) (f F : G ⟶ H) :
    FppfLocallyTorusConjugate (T := U) (e.hom ≫ i) f F ↔
      FppfLocallyTorusConjugate i f F := by
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun k => ?_⟩
    obtain ⟨t, ht⟩ := h𝒰 k
    exact ⟨t ≫ e.hom.hom.hom, (torusConjugates_torusIso_iff e i f F t).mp ht⟩
  · rintro ⟨𝒰, h𝒰⟩
    refine ⟨𝒰, fun k => ?_⟩
    obtain ⟨t, ht⟩ := h𝒰 k
    refine ⟨t ≫ e.inv.hom.hom, (torusConjugates_torusIso_iff e i f F _).mpr ?_⟩
    have he : (t ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = t := by
      rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
        Grp.id_hom_hom, Category.comp_id]
    rw [he]
    exact ht

/-- Split affine local existence stated directly with the full coordinate
root data and free actual root-weight lines of the two coordinate tori. -/
def CoordinateSplitIsogenyTorusConjugacyStatement : Prop :=
  ∀ (R : Type u) [CommRing R]
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    (hG : IsReductive G) (hH : IsReductive H)
    (I I' : Type u) [Fintype I] [Fintype I']
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (j : splitTorus (Spec (CommRingCat.of R)) I' ⟶ H)
    (J J' : Type u)
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (Q : RootDatum J' (I' → ℤ) (I' → ℤ)),
    haveI := hG.isAffineHom
    haveI := hH.isAffineHom
    IsClosedSubgroup i →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
    IsFibrewiseRootDatumOf I G i P →
    (∀ α : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
        CommRingCat.of R)) →
    IsClosedSubgroup j →
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') j →
    IsFibrewiseRootDatumOf I' H j Q →
    (∀ α : J', Nonempty
      (splitTorus.exponentWeightSpace I' H j (Q.root α) ≃ₗ[CommRingCat.of R]
        CommRingCat.of R)) →
    ∀ f F : G ⟶ H, IsIsogeny f → IsIsogeny F →
      (∃ τ : splitTorus (Spec (CommRingCat.of R)) I ⟶
        splitTorus (Spec (CommRingCat.of R)) I', i ≫ f = τ ≫ j) →
      i ≫ f = i ≫ F →
      FppfLocallyTorusConjugate (T := splitTorus.commGroupScheme _ I') j f F

/-- Coordinate-torus local existence supplies the packaged split affine
existence assertion without any choice of compatible root data. -/
theorem splitAffineIsogenyTorusConjugacy_of_coordinateSplit
    (hlocal : CoordinateSplitIsogenyTorusConjugacyStatement.{u}) :
    SplitAffineIsogenyTorusConjugacyStatement.{u} := by
  intro R G H hG hH T U i j
  let := hG.isAffineHom
  let := hH.isAffineHom
  intro hT hU f F hf hF hτ heq
  obtain ⟨I, hI, eT, hic, him, J, P, hP, hlP⟩ := hT
  obtain ⟨I', hI', eU, hjc, hjm, J', Q, hQ, hlQ⟩ := hU
  let : Fintype I := hI
  let : Fintype I' := hI'
  apply (fppfLocallyTorusConjugate_torusIso_iff
    (U := splitTorus.commGroupScheme _ I') eU j f F).mp
  apply hlocal R G H hG hH I I' (eT.hom ≫ i) (eU.hom ≫ j)
    J J' P Q hic him hP hlP hjc hjm hQ hlQ f F hf hF
  · obtain ⟨τ, hτ⟩ := hτ
    refine ⟨eT.hom ≫ τ ≫ eU.inv, ?_⟩
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← hτ]
  · simpa only [Category.assoc] using congrArg (eT.hom ≫ ·) heq

/-- The coordinate-torus version is also a consequence of the packaged
split affine assertion, by taking identity coordinate isomorphisms. -/
theorem coordinateSplitIsogenyTorusConjugacy_of_splitAffine
    (hlocal : SplitAffineIsogenyTorusConjugacyStatement.{u}) :
    CoordinateSplitIsogenyTorusConjugacyStatement.{u} := by
  intro R _ G H hG hH I I' _ _ i j J J' P Q
  let := hG.isAffineHom
  let := hH.isAffineHom
  intro hic him hP hlP hjc hjm hQ hlQ f F hf hF hτ heq
  apply hlocal (CommRingCat.of R) G H hG hH
    (splitTorus.commGroupScheme _ I) (splitTorus.commGroupScheme _ I') i j
  · refine ⟨I, inferInstance, Iso.refl _, ?_⟩
    rw [Iso.refl_hom, Category.id_comp]
    exact ⟨hic, him, J, P, hP, hlP⟩
  · refine ⟨I', inferInstance, Iso.refl _, ?_⟩
    rw [Iso.refl_hom, Category.id_comp]
    exact ⟨hjc, hjm, J', Q, hQ, hlQ⟩
  · exact hf
  · exact hF
  · exact hτ
  · exact heq

/-- Passing from supplied split coordinates to actual coordinate tori
preserves precisely the same local existence obligation. -/
theorem splitAffineIsogenyTorusConjugacy_iff_coordinateSplit :
    SplitAffineIsogenyTorusConjugacyStatement.{u} ↔
      CoordinateSplitIsogenyTorusConjugacyStatement.{u} :=
  ⟨coordinateSplitIsogenyTorusConjugacy_of_splitAffine,
    splitAffineIsogenyTorusConjugacy_of_coordinateSplit⟩

/-- Coordinate-torus local existence suffices for the unchanged general-base
rigidity statement. -/
theorem reductiveIsogenyTorusRigidity_of_coordinateSplit
    (hlocal : CoordinateSplitIsogenyTorusConjugacyStatement.{u}) :
    ReductiveIsogenyTorusRigidityStatement.{u} :=
  reductiveIsogenyTorusRigidity_of_splitAffine
    (splitAffineIsogenyTorusConjugacy_of_coordinateSplit hlocal)

end Langlands.GroupScheme
