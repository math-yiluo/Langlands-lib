import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Comparison of actual central covers over isomorphic field groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {C C' G G' : GroupScheme (Spec (CommRingCat.of k))}
variable {π : C ⟶ G} {π' : C' ⟶ G'}

/-- The cover universal property transports along an isomorphism of its target. -/
theorem HasCentralCoverUniversalProperty.comp_iso
    (hπ : HasCentralCoverUniversalProperty π) (e : G ≅ G') :
    HasCentralCoverUniversalProperty (π ≫ e.hom) := by
  intro H q hH hq
  obtain ⟨a, ha, hu⟩ := hπ H (q ≫ e.inv) hH (hq.comp_iso e.symm)
  refine ⟨a, ?_, ?_⟩
  · apply (cancel_mono e.inv).mp
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using ha
  · intro b hb
    apply hu
    rw [← Category.assoc, hb, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The cover universal property transports along an isomorphism of its source. -/
theorem HasCentralCoverUniversalProperty.iso_comp
    (hπ : HasCentralCoverUniversalProperty π) (e : C' ≅ C) :
    HasCentralCoverUniversalProperty (e.hom ≫ π) := by
  intro H q hH hq
  obtain ⟨a, ha, hu⟩ := hπ H q hH hq
  refine ⟨e.hom ≫ a, ?_, ?_⟩
  · change (e.hom ≫ a) ≫ q = e.hom ≫ π
    rw [Category.assoc, ha]
  intro b hb
  have h : e.inv ≫ b = a := hu _ (by
    change (e.inv ≫ b) ≫ q = π
    rw [Category.assoc, hb, e.inv_hom_id_assoc])
  rw [← h, e.hom_inv_id_assoc]

namespace IsSimplyConnectedCover

/-- An actual central cover transports along an isomorphism of its target. -/
theorem comp_iso (hπ : IsSimplyConnectedCover π) (e : G ≅ G') :
    IsSimplyConnectedCover (π ≫ e.hom) :=
  ⟨hπ.isSemisimple.of_iso e.symm, hπ.isSimplyConnected,
    hπ.isCentralIsogeny.comp_iso e, hπ.universal.comp_iso e⟩

/-- An actual central cover transports along an isomorphism of its source. -/
theorem iso_comp (hπ : IsSimplyConnectedCover π) (e : C' ≅ C) :
    IsSimplyConnectedCover (e.hom ≫ π) :=
  ⟨hπ.isSemisimple, hπ.isSimplyConnected.of_iso e,
    hπ.isCentralIsogeny.iso_comp e, hπ.universal.iso_comp e⟩

/-- The canonical source comparison lifting a supplied target isomorphism. -/
def isoOver (hπ : IsSimplyConnectedCover π) (hπ' : IsSimplyConnectedCover π')
    (e : G ≅ G') : C ≅ C' :=
  hπ.iso (hπ'.comp_iso e.symm)

/-- The canonical comparison lifts exactly the supplied target isomorphism. -/
@[reassoc]
theorem isoOver_hom_comp (hπ : IsSimplyConnectedCover π)
    (hπ' : IsSimplyConnectedCover π') (e : G ≅ G') :
    (hπ.isoOver hπ' e).hom ≫ π' = π ≫ e.hom := by
  apply (cancel_mono e.inv).mp
  simpa only [isoOver, Iso.symm_hom, Category.assoc, e.hom_inv_id,
    Category.comp_id] using
    hπ.iso_hom_comp (hπ'.comp_iso e.symm)

/-- Any homomorphism lifting this target isomorphism is the canonical comparison. -/
theorem hom_eq_isoOver (hπ : IsSimplyConnectedCover π)
    (hπ' : IsSimplyConnectedCover π') (e : G ≅ G') (a : C ⟶ C')
    (ha : a ≫ π' = π ≫ e.hom) :
    a = (hπ.isoOver hπ' e).hom := by
  apply hπ.lift_unique hπ'.isSimplyConnected.isSemisimple
    (hπ'.isCentralIsogeny.comp_iso e.symm)
  rw [Iso.symm_hom, ← Category.assoc, ha, Category.assoc, e.hom_inv_id,
    Category.comp_id]

/-- The unique-lifting statement at these two supplied field covers. -/
theorem existsUnique_lift_iso (hπ : IsSimplyConnectedCover π)
    (hπ' : IsSimplyConnectedCover π') (e : G ≅ G') :
    ∃! a : C ⟶ C', a ≫ π' = π ≫ e.hom :=
  ⟨(hπ.isoOver hπ' e).hom, hπ.isoOver_hom_comp hπ' e,
    fun a ha => hπ.hom_eq_isoOver hπ' e a ha⟩

/-- Equality of lifts only needs the universal property of the first cover. -/
theorem hom_ext_over_iso (hπ : IsSimplyConnectedCover π)
    (hC' : IsSemisimple C') (hπ' : IsCentralIsogeny π') (e : G ≅ G')
    {a b : C ⟶ C'}
    (ha : a ≫ π' = π ≫ e.hom) (hb : b ≫ π' = π ≫ e.hom) :
    a = b := by
  apply hπ.hom_ext hC' (hπ'.comp_iso e.symm)
  · rw [Iso.symm_hom, ← Category.assoc, ha, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  · rw [Iso.symm_hom, ← Category.assoc, hb, Category.assoc, e.hom_inv_id,
      Category.comp_id]

end IsSimplyConnectedCover

end Langlands.GroupScheme
