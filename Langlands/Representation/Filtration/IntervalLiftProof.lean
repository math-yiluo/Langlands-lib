import Langlands.Representation.Filtration.IntervalLiftStatement

/-! Pulling a quotient composition series back to its ambient interval. -/

namespace Langlands

universe uK uG uV

namespace IntervalLiftProof

open LengthCriterionProof

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- Membership in the pullback is membership of the quotient class. -/
theorem mem_pull_iff (S T : Subrepresentation ρ)
    (U : Subrepresentation (quotientRep S T)) (x : T.toSubmodule) :
    (x : V) ∈ pull S T U ↔ (lower S T).mkQ x ∈ U := by
  constructor
  · rintro ⟨y, hy, he⟩
    have hyx : y = x := Subtype.ext he
    change (lower S T).mkQ y ∈ U at hy
    rwa [hyx] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Every pullback lies in the original upper endpoint. -/
theorem pull_le (S T : Subrepresentation ρ)
    (U : Subrepresentation (quotientRep S T)) : pull S T U ≤ T := by
  rintro _ ⟨x, _, rfl⟩
  exact x.2

/-- Pullback preserves inclusions. -/
theorem pull_mono (S T : Subrepresentation ρ) : Monotone (pull S T) := by
  intro U U' h v hv
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨x, h hx, rfl⟩

/-- The preimage of zero is the lower endpoint. -/
theorem pull_bot {S T : Subrepresentation ρ} (hST : S ≤ T) :
    pull S T ⊥ = S := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (mkQ_mem_bot_iff x).mp hx
  · intro v hv
    exact (mem_pull_iff S T ⊥ ⟨v, hST hv⟩).mpr ((mkQ_mem_bot_iff _).mpr hv)

/-- The preimage of the full quotient is the upper endpoint. -/
theorem pull_top (S T : Subrepresentation ρ) : pull S T ⊤ = T := by
  apply le_antisymm (pull_le S T ⊤)
  intro v hv
  exact ⟨⟨v, hv⟩, Submodule.mem_top, rfl⟩

/-- Successive quotients of preimages are actually equivalent to the original
successive quotients, through the map induced by the quotient projection. -/
theorem nonempty_quotient_pull_equiv (S T : Subrepresentation ρ)
    (U U' : Subrepresentation (quotientRep S T)) :
    Nonempty ((quotientRep (pull S T U) (pull S T U')).Equiv (quotientRep U U')) := by
  let r : (pull S T U').toSubmodule →ₗ[k] U'.toSubmodule :=
    ((lower S T).mkQ.comp (Submodule.inclusion (pull_le S T U'))).codRestrict
      U'.toSubmodule (fun x =>
        (mem_pull_iff S T U' ⟨x, pull_le S T U' x.2⟩).mp x.2)
  have hr (x : (pull S T U').toSubmodule) :
      r x ∈ lower U U' ↔ x ∈ lower (pull S T U) (pull S T U') :=
    (mem_pull_iff S T U ⟨x, pull_le S T U' x.2⟩).symm
  have hsurj : Function.Surjective r := by
    intro y
    obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (lower S T) y.1
    have hxU : (x : V) ∈ pull S T U' :=
      (mem_pull_iff S T U' x).mpr (hx ▸ y.2)
    refine ⟨⟨x, hxU⟩, ?_⟩
    exact Subtype.ext hx
  let L := (lower U U').mkQ.comp r
  have hL : lower (pull S T U) (pull S T U') ≤ LinearMap.ker L := by
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((hr x).mpr hx)
  let Φ := (lower (pull S T U) (pull S T U')).liftQ L hL
  have hΦ (x : (pull S T U').toSubmodule) :
      Φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (r x) := rfl
  let Ψ : (quotientRep (pull S T U) (pull S T U')).IntertwiningMap
      (quotientRep U U') :=
    { toLinearMap := Φ
      isIntertwining' g := by
        apply LinearMap.ext
        intro q
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
        change Φ (Submodule.Quotient.mk ((pull S T U').toRepresentation g x)) =
          (quotientRep U U') g (Φ (Submodule.Quotient.mk x))
        rw [hΦ, hΦ]
        rfl }
  refine ⟨Ψ.ofBijective ⟨?_, ?_⟩⟩
  · intro x y hxy
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Φ (Submodule.Quotient.mk v) = Φ (Submodule.Quotient.mk w) at hxy
    rw [hΦ, hΦ, Submodule.Quotient.eq] at hxy
    rw [Submodule.Quotient.eq]
    apply (hr (v - w)).mp
    simpa only [map_sub] using hxy
  · intro y
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨v, rfl⟩ := hsurj w
    exact ⟨Submodule.Quotient.mk v, hΦ v⟩

end IntervalLiftProof

open LengthCriterionProof IntervalLiftProof in
/-- Lift every actual quotient composition series to its interval, with actual
factor equivalences and the identity matching of factor occurrences. -/
theorem actualQuotientSeriesLift : ActualQuotientSeriesLiftStatement.{uK, uG, uV} := by
  intro k _ G _ A S T hST n f hf
  have hstep (i : Fin n) :
      pull S T (f.subrepresentation i.castSucc) ⋖ pull S T (f.subrepresentation i.succ) := by
    have hle := pull_mono S T (f.monotone_subrepresentation
      (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le)
    apply (isIrreducible_quotientRep_iff hle).mp
    obtain ⟨e⟩ := nonempty_quotient_pull_equiv S T
      (f.subrepresentation i.castSucc) (f.subrepresentation i.succ)
    have hirr := hf i
    change Representation.IsIrreducible (quotientRep
      (f.subrepresentation i.castSucc) (f.subrepresentation i.succ)) at hirr
    rw [Representation.irreducible_iff_isSimpleModule_asModule] at hirr ⊢
    exact (LinearMap.isSimpleModule_iff_of_bijective
      (Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap)
      e.bijective).2 hirr
  let c : RelSeries {(X, Y) : Subrepresentation A.ρ × Subrepresentation A.ρ | X ⋖ Y} :=
    ⟨n, fun i => pull S T (f.subrepresentation i), hstep⟩
  refine ⟨c, ?_, ?_, Equiv.refl (Fin n), ?_⟩
  · change pull S T (f.subrepresentation 0) = S
    rw [f.subrepresentation_zero, pull_bot hST]
  · change pull S T (f.subrepresentation (Fin.last n)) = T
    rw [f.subrepresentation_last, pull_top]
  · intro i
    exact nonempty_quotient_pull_equiv S T
      (f.subrepresentation i.castSucc) (f.subrepresentation i.succ)

end Langlands
