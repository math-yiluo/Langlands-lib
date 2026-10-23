import Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement

namespace Langlands

universe uF uV uR uG

/-- An open subgroup has exactly the same smooth vectors as the ambient action. -/
theorem isSmoothVector_restrict_open_iff
    {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module R V]
    (ρ : Representation R G V) (H : OpenSubgroup G) (v : V) :
    IsSmoothVector (ρ.comp H.toSubgroup.subtype) v ↔ IsSmoothVector ρ v := by
  constructor
  · rintro ⟨K, hK⟩
    let L : OpenSubgroup G :=
      { toSubgroup := K.toSubgroup.map H.toSubgroup.subtype
        isOpen' := H.isOpen.isOpenMap_subtype_val _ K.isOpen }
    refine ⟨L, ?_⟩
    intro g
    obtain ⟨h, hh, hhg⟩ := g.property
    change ρ g.val v = v
    rw [← hhg]
    exact hK ⟨h, hh⟩
  · exact isSmoothVector_comp H.toSubgroup.subtype continuous_subtype_val

namespace CuspidalSupport

open GeneralLinear


/-- Smoothness is tested for the restricted dual itself. -/
theorem determinantUnitSmoothDual : DeterminantUnitSmoothDualStatement.{uF, uV} := by
  intro p hp F T n B
  let := T.topology
  intro V _ _ ρ ℓ
  change IsSmoothVector (ρ.dual.comp (determinantUnitOpenSubgroup T B).toSubgroup.subtype) ℓ ↔ _
  exact isSmoothVector_restrict_open_iff ρ.dual (determinantUnitOpenSubgroup T B) ℓ

/-- Every coefficient on the empty product Levi has compact support. -/
theorem leviHarishChandraRankZero : LeviHarishChandraRankZeroStatement.{uF, uV} := by
  intro p hp F T B
  let := T.topology
  intro A
  have hsize (i : Fin B.length) : B.size i ≤ 0 := by
    calc
      B.size i ≤ ∑ j, B.size j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = 0 := B.sum_eq
  let : IsEmpty (Fin B.length) := ⟨fun i => (Nat.not_lt_of_ge (hsize i)) (B.positive i)⟩
  have hq : IsLeviQuasicuspidal B A.representation := by
    intro S hS
    exact (hS (Subsingleton.elim _ _)).elim
  have hc : HasCompactSmoothDualCoefficients
      (determinantUnitRestriction T B A.representation) := by
    intro v ℓ _
    exact HasCompactSupport.of_compactSpace _
  exact ⟨fun _ => hc, fun _ => hq⟩

/-- The exact two-universe boundary target. -/
theorem harishChandraBoundary : HarishChandraBoundaryStatement.{uF, uV} :=
  ⟨determinantUnitSmoothDual, leviHarishChandraRankZero⟩

end CuspidalSupport
end Langlands
