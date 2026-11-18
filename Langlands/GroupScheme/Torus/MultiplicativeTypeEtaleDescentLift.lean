import Langlands.GroupScheme.Descent.CechDatumLift
import Langlands.GroupScheme.Descent.EtaleAffineBaseEffectivity
import Langlands.GroupScheme.Torus.MultiplicativeTypeNilpotentHom
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeLocality

/-! # Lifting a multiplicative-type group from an étale local model -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.RelativeMultiplicativeType

open Descent

variable {B S C V : Scheme.{u}} {p : S ⟶ B} {t : V ⟶ C} {q : V ⟶ S} {b : C ⟶ B}
variable {G : GroupScheme S}

/-- Over a cartesian square with a surjective closed immersion on the base,
any datum on the reduction of a multiplicative-type group lifts. -/
theorem exists_datum_lift_of_multiplicativeType (h : IsPullback q t p b)
    [IsClosedImmersion b] [Surjective b] (hG : IsMultiplicativeType G)
    (D₀ : Datum t ((baseChange q).obj G)) :
    ∃ D : Datum p G, D.reindex t q b h.w = D₀ := by
  have : IsClosedImmersion q := MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    h.flip inferInstance
  have : Surjective q := MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  have h₂ := CechBaseChange.overlapMap_isPullback h
  have h₃ := CechBaseChange.tripleMap_isPullback h
  have : IsClosedImmersion (CechBaseChange.overlapMap h.w) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₂.flip inferInstance
  have : Surjective (CechBaseChange.overlapMap h.w) :=
    MorphismProperty.of_isPullback (P := @Surjective) h₂.flip inferInstance
  have : IsClosedImmersion (CechBaseChange.tripleMap h.w) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₃.flip inferInstance
  have : Surjective (CechBaseChange.tripleMap h.w) :=
    MorphismProperty.of_isPullback (P := @Surjective) h₃.flip inferInstance
  exact CechBaseChange.exists_datum_reindex_eq h.w D₀
    (fun f g => (hG.baseChange f).baseChange_hom_bijective_of_surjective_closedImmersion
      (hG.baseChange g) (CechBaseChange.overlapMap h.w))
    ((hG.baseChange (p1 p)).baseChange_hom_bijective_of_surjective_closedImmersion
      (hG.baseChange (p3 p)) (CechBaseChange.tripleMap h.w))

/-- An affine multiplicative-type group on an étale cover which agrees with the
special-fibre group descends to a lift over the original affine base. -/
theorem exists_lift_of_etale_model [IsAffine B] [Etale p] [Surjective p]
    [IsClosedImmersion b] [Surjective b] [IsAffineHom G.X.hom]
    (h : IsPullback q t p b) (hG : IsMultiplicativeType G) (H₀ : GroupScheme C)
    (e : (baseChange t).obj H₀ ≅ (baseChange q).obj G) :
    ∃ H : GroupScheme B, IsMultiplicativeType H ∧ Flat H.X.hom ∧
      Nonempty ((baseChange b).obj H ≅ H₀) := by
  let D₀ := (canonicalDatum t H₀).transport e
  obtain ⟨D, hD⟩ := exists_datum_lift_of_multiplicativeType h hG D₀
  let s := D.etaleAffineBaseSolution
  have hH : IsMultiplicativeType s.obj :=
    IsMultiplicativeType.of_fppfBaseChange p (IsMultiplicativeType.of_iso s.iso hG)
  have : Etale t := MorphismProperty.of_isPullback (P := @Etale) h inferInstance
  have : Surjective t := MorphismProperty.of_isPullback (P := @Surjective) h inferInstance
  let s₀ := s.reindex t q b h.w
  let t₀ : Solution (D.reindex t q b h.w) :=
    (canonicalSolution t H₀).mapIso e (by
      rw [hD]
      exact (canonicalDatum t H₀).compatible_transport e)
  exact ⟨s.obj, hH, hH.flat,
    ⟨s₀.descendIsoOfEtale t₀ (Iso.refl _) (compatible_id _)⟩⟩

end Langlands.GroupScheme.RelativeMultiplicativeType
