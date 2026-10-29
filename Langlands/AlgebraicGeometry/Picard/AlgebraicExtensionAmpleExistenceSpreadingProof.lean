import Langlands.AlgebraicGeometry.Picard.AlgebraicExtensionAmpleExistenceSpreadingStatement
import Langlands.AlgebraicGeometry.Picard.LineBundleLimitSpreading
import Langlands.AlgebraicGeometry.Picard.IntermediateFieldBaseChangeLimit
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms

/-! # Spreading ample existence to a finite intermediate field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- A section of `M^{⊗ n}` gives a section of `M^{⊗ N}` with the same trivialization open,
for every positive multiple `N` of `n`. -/
theorem exists_trivializationOpen_eq_of_dvd {X : Scheme.{u}}
    (M : LineBundle X) {n N : ℕ} (hN : 0 < N) (hnN : n ∣ N)
    (s : GlobalSections (tensorPow M.obj n)) :
    ∃ t : GlobalSections (tensorPow M.obj N),
      trivializationOpen (tensorPow M.obj N) t = trivializationOpen (tensorPow M.obj n) s := by
  obtain ⟨k, rfl⟩ := hnN
  refine ⟨(tensorPowMulIso M.obj n k).hom.app ⊤ (sectionPow (tensorPow M.obj n) s k), ?_⟩
  rw [trivializationOpen_mapIso]
  exact trivializationOpen_sectionPow ⟨tensorPow M.obj n, tensorPow_isLocallyFreeRankOne X M n⟩ s
    (Nat.pos_of_mul_pos_left hN)

/-- Spreading of ample existence from `X_Ω` to `X_E` for a finite intermediate field `E`. -/
theorem algebraicExtensionAmpleExistenceSpreading :
    AlgebraicExtensionAmpleExistenceSpreadingStatement.{u} := by
  classical
  intro K Ω _ _ _ _ X p hp ⟨M, hM⟩
  have := hp
  have := hM.1
  choose n hn s hxs haff using hM.2
  have hcover : Set.univ ⊆ ⋃ x, SetLike.coe (M.sectionOpen (s x)) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hxs x⟩
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover _
    (fun x ↦ (M.sectionOpen (s x)).isOpen) hcover
  have hN : 0 < ∏ x ∈ T, n x := Finset.prod_pos fun x _ ↦ hn x
  have ht : ∀ x : T, ∃ t : GlobalSections (tensorPow M.obj (∏ x ∈ T, n x)),
      trivializationOpen _ t = trivializationOpen _ (s x) := fun x ↦
    exists_trivializationOpen_eq_of_dvd M hN (Finset.dvd_prod_of_mem n x.2) (s x)
  choose t ht using ht
  obtain ⟨E, L, s', hcov, haff'⟩ := exists_lineBundle_of_isLimit (baseChangeDiagram X p)
    (baseChangeCone X p) (isLimitBaseChangeCone X p) (baseChangeCone_π_app_app_injective X p)
    (baseChangeCone_π_app_surjective X p) (tensorPow M.obj (∏ x ∈ T, n x)) t
    (fun y ↦ by
      obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (hT (Set.mem_univ y))
      exact ⟨⟨x, hx⟩, (ht ⟨x, hx⟩).symm ▸ hy⟩)
    (fun j ↦ (ht j).symm ▸ haff j)
  refine ⟨E.unop.1, E.unop.2, L, inferInstance, fun x ↦ ?_⟩
  obtain ⟨j, hj⟩ := hcov x
  have h1 := trivializationOpen_sectionPow L (s' j) one_pos
  refine ⟨1, le_rfl, sectionPow L.obj (s' j) 1, ?_, ?_⟩
  · rw [← h1] at hj
    exact hj
  · have h2 := haff' j
    rw [← h1] at h2
    exact h2

end Langlands.AlgebraicGeometry.Picard
