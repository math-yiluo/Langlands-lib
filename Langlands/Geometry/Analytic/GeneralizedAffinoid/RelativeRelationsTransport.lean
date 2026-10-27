import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeRelations
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Bounded coefficient transport through relative equation quotients -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRelations

open GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  {A B C : PresentedAffinoidAlgebra K} {m : ℕ}
  (s : PositivePolyradius (Fin m))

/-- The coefficientwise map sends each source equation into the target closed ideal. -/
def MapsRelations (φ : BoundedAlgHom K A B)
    (E : Set (GeneralizedTateAlgebra s A)) (F : Set (GeneralizedTateAlgebra s B)) : Prop :=
  ∀ f ∈ E, mapCoefficientsAlgHom s φ f ∈ ideal K B s F

variable {E : Set (GeneralizedTateAlgebra s A)}
  {F : Set (GeneralizedTateAlgebra s B)} {G : Set (GeneralizedTateAlgebra s C)}

/-- Sending generators into target generators suffices for closed-relation compatibility. -/
theorem mapsRelations_of_mapsTo (φ : BoundedAlgHom K A B)
    (hφ : Set.MapsTo (mapCoefficientsAlgHom s φ) E F) :
    MapsRelations K s φ E F :=
  fun _ hf => equation_mem K B s F (hφ hf)

/-- A compatible coefficient map preserves the entire closed generated ideal. -/
theorem mapsRelations_ideal (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) :
    ∀ f ∈ ideal K A s E, mapCoefficientsAlgHom s φ f ∈ ideal K B s F := by
  intro f hf
  apply (quotientMap_eq_zero_iff K B s F _).mp
  exact annihilates_ideal K A s E (QuotientAlgebra K B s F)
    ((quotientMap K B s F).comp (mapCoefficientsAlgHom s φ))
    (fun g hg => (quotientMap_eq_zero_iff K B s F _).mpr (hφ g hg)) f hf

/-- Identity coefficient maps preserve the supplied relations. -/
theorem mapsRelations_id (E : Set (GeneralizedTateAlgebra s A)) :
    MapsRelations K s (BoundedAlgHom.id K A) E E := by
  intro f hf
  simpa only [mapCoefficientsAlgHom_id, BoundedAlgHom.id_apply, ideal] using
    equation_mem K A s E hf

/-- Closed-relation compatibility composes. -/
theorem mapsRelations_comp (ψ : BoundedAlgHom K B C) (φ : BoundedAlgHom K A B)
    (hψ : MapsRelations K s ψ F G) (hφ : MapsRelations K s φ E F) :
    MapsRelations K s (ψ.comp φ) E G := by
  intro f hf
  simpa only [mapCoefficientsAlgHom_comp, BoundedAlgHom.comp_apply] using
    mapsRelations_ideal K s ψ hψ _ (hφ f hf)

/-- Descend the actual coefficientwise map to the two closed equation quotients. -/
def transport (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra s B))
    (φ : BoundedAlgHom K A B) (hφ : MapsRelations K s φ E F) :
    BoundedAlgHom K (QuotientAlgebra K A s E) (QuotientAlgebra K B s F) :=
  descend K A s E (QuotientAlgebra K B s F)
    ((quotientMap K B s F).comp (mapCoefficientsAlgHom s φ))
    (fun f hf => (quotientMap_eq_zero_iff K B s F _).mpr (hφ f hf))

/-- The descended map is computed coefficientwise on any series representative. -/
@[simp] theorem transport_quotientMap (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (f : GeneralizedTateAlgebra s A) :
    transport K s E F φ hφ (quotientMap K A s E f) =
      quotientMap K B s F (mapCoefficientsAlgHom s φ f) := rfl

theorem transport_comp_quotientMap (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) :
    (transport K s E F φ hφ).comp (quotientMap K A s E) =
      (quotientMap K B s F).comp (mapCoefficientsAlgHom s φ) :=
  BoundedAlgHom.ext fun _ => rfl

/-- Coefficients are transported by the given base map. -/
@[simp] theorem transport_baseMap (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (a : A) :
    transport K s E F φ hφ (baseMap K A s E a) = baseMap K B s F (φ a) := by
  change quotientMap K B s F
    (mapCoefficients s φ.toBoundedRingHom (algebraMap A (GeneralizedTateAlgebra s A) a)) =
      quotientMap K B s F (algebraMap B (GeneralizedTateAlgebra s B) (φ a))
  rw [mapCoefficients_algebraMap]
  rfl

/-- The new coordinate labels are unchanged. -/
@[simp] theorem transport_newCoordinate (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (j : Fin m) :
    transport K s E F φ hφ (newCoordinate K A s E j) =
      newCoordinate K B s F j := by
  change quotientMap K B s F (mapCoefficients s φ.toBoundedRingHom (X s A j)) =
    quotientMap K B s F (X s B j)
  rw [mapCoefficients_X]

/-- The representative formula determines the descended map uniquely. -/
theorem eq_transport (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F)
    (ψ : BoundedAlgHom K (QuotientAlgebra K A s E) (QuotientAlgebra K B s F))
    (hψ : ∀ f, ψ (quotientMap K A s E f) =
      quotientMap K B s F (mapCoefficientsAlgHom s φ f)) :
    ψ = transport K s E F φ hφ :=
  hom_ext K A s E (QuotientAlgebra K B s F) _ _ hψ

/-- The descended identity is the actual identity on the quotient. -/
@[simp] theorem transport_id (E : Set (GeneralizedTateAlgebra s A)) :
    transport K s E E (BoundedAlgHom.id K A) (mapsRelations_id K s E) =
      BoundedAlgHom.id K (QuotientAlgebra K A s E) := by
  apply hom_ext K A s E (QuotientAlgebra K A s E)
  intro f
  simp only [transport_quotientMap, mapCoefficientsAlgHom_id, BoundedAlgHom.id_apply]

/-- Descended coefficient transport respects composition on the actual quotients. -/
@[simp] theorem transport_comp (ψ : BoundedAlgHom K B C) (φ : BoundedAlgHom K A B)
    (hψ : MapsRelations K s ψ F G) (hφ : MapsRelations K s φ E F) :
    transport K s E G (ψ.comp φ) (mapsRelations_comp K s ψ φ hψ hφ) =
      (transport K s F G ψ hψ).comp (transport K s E F φ hφ) := by
  apply hom_ext K A s E (QuotientAlgebra K C s G)
  intro f
  simp only [BoundedAlgHom.comp_apply, transport_quotientMap, mapCoefficientsAlgHom_comp]

/-- Every supplied nonnegative coefficient bound descends with the same constant. -/
theorem norm_transport_le (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a, ‖φ a‖ ≤ c * ‖a‖) (a : QuotientAlgebra K A s E) :
    ‖transport K s E F φ hφ a‖ ≤ c * ‖a‖ := by
  by_cases hpos : 0 < c
  · apply norm_descend_le K A s E (QuotientAlgebra K B s F)
      ((quotientMap K B s F).comp (mapCoefficientsAlgHom s φ)) _ c hpos
    intro f
    exact (norm_quotientMap_le K B s F _).trans
      (norm_mapCoefficientsAlgHom_le s φ hc hbound f)
  · have hc0 : c = 0 := le_antisymm (le_of_not_gt hpos) hc
    obtain ⟨f, rfl⟩ := quotientMap_surjective K A s E a
    rw [transport_quotientMap]
    have h := (norm_quotientMap_le K B s F (mapCoefficientsAlgHom s φ f)).trans
      (norm_mapCoefficientsAlgHom_le s φ hc hbound f)
    simpa only [hc0, zero_mul] using h

/-- A contractive coefficient map induces a contractive quotient map. -/
theorem norm_transport_le_of_contractive (φ : BoundedAlgHom K A B)
    (hφ : MapsRelations K s φ E F) (hbound : ∀ a, ‖φ a‖ ≤ ‖a‖)
    (a : QuotientAlgebra K A s E) :
    ‖transport K s E F φ hφ a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using norm_transport_le K s φ hφ zero_le_one
    (fun a => (hbound a).trans_eq (one_mul _).symm) a

/-- A supplied bounded base equivalence preserving the relations in both directions
induces an actual bounded equivalence of the closed equation quotients. -/
def transportEquiv (E : Set (GeneralizedTateAlgebra s A))
    (F : Set (GeneralizedTateAlgebra s B)) (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) :
    BoundedAlgEquiv K (QuotientAlgebra K A s E) (QuotientAlgebra K B s F) :=
  BoundedAlgEquiv.ofHomInv
    (transport K s E F e.toBoundedAlgHom hAB)
    (transport K s F E e.symm.toBoundedAlgHom hBA)
    (fun a => by
      obtain ⟨f, rfl⟩ := quotientMap_surjective K A s E a
      simp only [transport_quotientMap]
      have h : e.symm.toBoundedAlgHom.comp e.toBoundedAlgHom = BoundedAlgHom.id K A := by
        apply BoundedAlgHom.ext
        exact e.symm_apply_apply
      have h' := congrArg
        (fun φ : BoundedAlgHom K A A => mapCoefficientsAlgHom s φ f) h
      simp only [mapCoefficientsAlgHom_comp, mapCoefficientsAlgHom_id,
        BoundedAlgHom.comp_apply, BoundedAlgHom.id_apply] at h'
      rw [h'])
    (fun b => by
      obtain ⟨f, rfl⟩ := quotientMap_surjective K B s F b
      simp only [transport_quotientMap]
      have h : e.toBoundedAlgHom.comp e.symm.toBoundedAlgHom = BoundedAlgHom.id K B := by
        apply BoundedAlgHom.ext
        exact e.apply_symm_apply
      have h' := congrArg
        (fun φ : BoundedAlgHom K B B => mapCoefficientsAlgHom s φ f) h
      simp only [mapCoefficientsAlgHom_comp, mapCoefficientsAlgHom_id,
        BoundedAlgHom.comp_apply, BoundedAlgHom.id_apply] at h'
      rw [h'])

@[simp] theorem transportEquiv_apply (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) (a : QuotientAlgebra K A s E) :
    transportEquiv K s E F e hAB hBA a = transport K s E F e.toBoundedAlgHom hAB a := rfl

@[simp] theorem transportEquiv_symm_apply (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) (b : QuotientAlgebra K B s F) :
    (transportEquiv K s E F e hAB hBA).symm b =
      transport K s F E e.symm.toBoundedAlgHom hBA b := rfl

/-- Every supplied nonnegative forward bound transfers to the quotient equivalence. -/
theorem norm_transportEquiv_le (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ a, ‖e a‖ ≤ c * ‖a‖) (a : QuotientAlgebra K A s E) :
    ‖transportEquiv K s E F e hAB hBA a‖ ≤ c * ‖a‖ :=
  norm_transport_le K s e.toBoundedAlgHom hAB hc he a

/-- Every supplied nonnegative inverse bound transfers as well. -/
theorem norm_transportEquiv_symm_le (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) {c : ℝ} (hc : 0 ≤ c)
    (he : ∀ b, ‖e.symm b‖ ≤ c * ‖b‖) (b : QuotientAlgebra K B s F) :
    ‖(transportEquiv K s E F e hAB hBA).symm b‖ ≤ c * ‖b‖ :=
  norm_transport_le K s e.symm.toBoundedAlgHom hBA hc he b

/-- A norm-preserving base equivalence preserves the actual quotient norms. -/
theorem norm_transportEquiv (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E)
    (he : ∀ a, ‖e a‖ = ‖a‖) (a : QuotientAlgebra K A s E) :
    ‖transportEquiv K s E F e hAB hBA a‖ = ‖a‖ := by
  apply le_antisymm
  · exact norm_transport_le_of_contractive K s e.toBoundedAlgHom hAB
      (fun a => (he a).le) a
  · have h := norm_transport_le_of_contractive K s e.symm.toBoundedAlgHom hBA
      (fun b => by
        have hb := he (e.symm b)
        rw [e.apply_symm_apply] at hb
        exact hb.symm.le) (transportEquiv K s E F e hAB hBA a)
    change ‖(transportEquiv K s E F e hAB hBA).symm
      (transportEquiv K s E F e hAB hBA a)‖ ≤ _ at h
    simpa only [BoundedAlgEquiv.symm_apply_apply] using h

theorem isometry_transportEquiv (e : BoundedAlgEquiv K A B)
    (hAB : MapsRelations K s e.toBoundedAlgHom E F)
    (hBA : MapsRelations K s e.symm.toBoundedAlgHom F E) (he : Isometry e) :
    Isometry (transportEquiv K s E F e hAB hBA) :=
  AddMonoidHomClass.isometry_of_norm (transportEquiv K s E F e hAB hBA).toAlgEquiv
    (norm_transportEquiv K s e hAB hBA
      (he.norm_map_of_map_zero (map_zero e.toAlgEquiv)))

end Langlands.Analytic.PresentedAffinoidAlgebra.RelativeRelations
