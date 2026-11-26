import Langlands.LocalFactor.Ramification.Wintenberger.Absolute

/-!
# Closed right limits and wild inertia in any characteristic

Finite restriction sends the closed right limit of the absolute upper filtration
to the finite right limit. At index zero these finite images are the first lower
ramification groups, which determine the closed wild inertia subgroup.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe uK uΩ

section Restriction

variable (K : Type uK) (Ω : Type uΩ) [Field K] [Field Ω] [Algebra K Ω]

private theorem map_topologicalClosure_absoluteFiniteRestriction
    (L : FiniteGaloisIntermediateField K Ω) (H : Subgroup (Ω ≃ₐ[K] Ω)) :
    H.topologicalClosure.map (absoluteFiniteRestriction K Ω L).toMonoidHom =
      H.map (absoluteFiniteRestriction K Ω L).toMonoidHom := by
  apply le_antisymm _ (Subgroup.map_mono H.le_topologicalClosure)
  rw [Subgroup.map_le_iff_le_comap]
  have hclosed := (isClosed_discrete
    ((H.map (absoluteFiniteRestriction K Ω L).toMonoidHom : Subgroup _) : Set _)).preimage
      (absoluteFiniteRestriction K Ω L).continuous
  exact H.topologicalClosure_minimal (Subgroup.le_comap_map _ H) hclosed

private theorem iInf_comap_map_absoluteFiniteRestriction [IsGalois K Ω]
    (H : Subgroup (Ω ≃ₐ[K] Ω)) (hH : IsClosed (H : Set (Ω ≃ₐ[K] Ω))) :
    (⨅ L : FiniteGaloisIntermediateField K Ω,
      (H.map (absoluteFiniteRestriction K Ω L).toMonoidHom).comap
        (absoluteFiniteRestriction K Ω L).toMonoidHom) = H := by
  apply le_antisymm _ (le_iInf fun L => Subgroup.le_comap_map _ H)
  intro σ hσ
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨H, hH⟩ : ClosedSubgroup Gal(Ω/K))
  rw [← hfix]
  apply (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr
  intro x hx
  let L := FiniteGaloisIntermediateField.adjoin K ({x} : Set Ω)
  have hxL : x ∈ L.toIntermediateField :=
    FiniteGaloisIntermediateField.subset_adjoin K _ rfl
  obtain ⟨τ, hτ, he⟩ :=
    Subgroup.mem_map.mp (Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp hσ L))
  change AlgEquiv.restrictNormalHom L τ = AlgEquiv.restrictNormalHom L σ at he
  let y : L := ⟨x, hxL⟩
  have hsame := congrArg (fun f : Gal(L/K) => (f y : Ω)) he
  rw [AlgEquiv.restrictNormalHom_apply L.toIntermediateField τ y,
    AlgEquiv.restrictNormalHom_apply L.toIntermediateField σ y] at hsame
  exact hsame.symm.trans ((IntermediateField.mem_fixedField_iff _ _).mp hx τ hτ)

end Restriction

section LocalField

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/-- The closed right limit of the absolute filtration maps to the right limit
in every finite Galois quotient. -/
theorem absoluteUpperClosedRightImage : AbsoluteUpperClosedRightImage K Ω := by
  intro L v hv
  rw [map_topologicalClosure_absoluteFiniteRestriction, Subgroup.map_iSup]
  refine iSup_congr fun w => ?_
  rw [Subgroup.map_iSup]
  exact iSup_congr fun hw =>
    Wintenberger.localAbsoluteUpperFiniteImage K Ω L w (hv.trans hw.le)

private theorem iSup_localUpperRamificationGroup_pos
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] :
    (⨆ (w : ℝ) (_ : 0 < w), localUpperRamificationGroup K L w) =
      lowerRamificationGroup (localTopologicalData K L) K 1 := by
  let T := localTopologicalData K L
  change (⨆ (w : ℝ) (_ : 0 < w), upperRamificationGroup T K w) =
    lowerRamificationGroup T K 1
  have hone : lowerRamificationGroupReal T K 1 = lowerRamificationGroup T K 1 := by
    simpa only [Nat.cast_one] using lowerRamificationGroupReal_nat T K 1
  rw [← hone]
  apply le_antisymm
  · refine iSup₂_le fun w hw => ?_
    have hceil : (1 : ℤ) ≤ ⌈herbrandPsi T K w⌉ :=
      Order.one_le_iff_pos.mpr (Int.ceil_pos.mpr (herbrandPsi_pos T K hw))
    simpa only [upperRamificationGroup_eq_lower, lowerRamificationGroupReal, Int.ceil_one]
      using lowerRamificationGroupInt_antitone T K hceil
  · rw [← upperRamificationGroup_phi T K 1]
    exact le_iSup₂ (f := fun w (_ : 0 < w) => upperRamificationGroup T K w)
      (herbrandPhi T K 1) (herbrandPhi_pos T K one_pos)

/-- Wild inertia consists of the automorphisms that restrict into the first
lower ramification group at every finite Galois subextension. -/
theorem absoluteUpperWildInertia : AbsoluteUpperWildInertia K Ω := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  unfold AbsoluteUpperWildInertia
  rw [← iInf_comap_map_absoluteFiniteRestriction K Ω (localWildInertia K Ω)
    (Subgroup.isClosed_topologicalClosure _)]
  refine iInf_congr fun L => ?_
  have himage : (localWildInertia K Ω).map (absoluteFiniteRestriction K Ω L).toMonoidHom =
      lowerRamificationGroup (localTopologicalData K L) K 1 :=
    (absoluteUpperClosedRightImage K Ω L 0 (by norm_num)).trans
      (iSup_localUpperRamificationGroup_pos K L)
  rw [himage]

end LocalField
end Langlands.Ramification.Local
