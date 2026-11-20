import Langlands.AllField.LocalField.Foundation

/-!
# Transport of local integer rings under continuous field maps
-/

namespace Langlands.LocalFieldData

universe u v

/-- A continuous field homomorphism sends the actual valuation ring into the
valuation ring. The absolute values of the images of powers of an integer
are bounded by compactness. -/
theorem map_mem_integers_of_continuous {F : Type u} [Field F] {E : Type v} [Field E]
    (TF : LocalFieldData F) (TE : LocalFieldData E) (g : F →+* E)
    (hg : @Continuous F E TF.topology TE.topology g) {x : F} (hx : x ∈ TF.Integers) :
    g x ∈ TE.Integers := by
  let := TF.topology
  let := TE.topology
  apply (TE.normalizedAbs_le_one_iff_mem_integers _).mp
  by_contra! h
  obtain ⟨M, hM⟩ := TF.isCompact_integers.bddAbove_image
    (TE.continuous_normalizedAbs.comp hg).continuousOn
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h
  have hp (y : E) (m : ℕ) : TE.normalizedAbs (y ^ m) = TE.normalizedAbs y ^ m := by
    induction m with
    | zero => rw [pow_zero, pow_zero, TE.normalizedAbs_one]
    | succ m ih => rw [pow_succ, pow_succ, TE.normalizedAbs_mul, ih]
  have hbound : TE.normalizedAbs (g (x ^ n)) ≤ M :=
    hM ⟨x ^ n, pow_mem hx n, rfl⟩
  rw [map_pow, hp] at hbound
  exact hn.not_ge hbound

/-- A continuous field isomorphism with continuous inverse preserves and
reflects membership in the integer ring. -/
theorem mem_integers_iff_of_continuous_ringEquiv {F : Type u} [Field F] {E : Type v} [Field E]
    (TF : LocalFieldData F) (TE : LocalFieldData E) (e : F ≃+* E)
    (he : @Continuous F E TF.topology TE.topology e)
    (he' : @Continuous E F TE.topology TF.topology e.symm) (x : F) :
    x ∈ TF.Integers ↔ e x ∈ TE.Integers := by
  refine ⟨fun hx => TF.map_mem_integers_of_continuous TE e.toRingHom he hx, ?_⟩
  intro hx
  have h := TE.map_mem_integers_of_continuous TF e.symm.toRingHom he' hx
  change e.symm (e x) ∈ TF.Integers at h
  rwa [RingEquiv.symm_apply_apply] at h

end Langlands.LocalFieldData
