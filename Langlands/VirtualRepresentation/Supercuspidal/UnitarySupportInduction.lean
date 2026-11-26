import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupport
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered
import Langlands.Representation.Exponents.CuspidalInductionJacquetConstituentReduction

/-! # Realizing a witnessed unitary supercuspidal support by induction -/

noncomputable section

universe uF

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- A positive-rank representation with a witnessed unitary supercuspidal support is
equivalent to the normalized induction of unitarizable supercuspidal blocks. -/
theorem exists_equiv_unitarizableSupercuspidalProduct {n : ℕ} (hn : 0 < n)
    {π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, uF} ℂ (GeneralLinear n F.Carrier)}
    {x : UnitaryLattice.{uF, uF} F} (hx : IsUnitaryLatticeSupport F π x) :
    letI := F.canonicalTopologicalData.topology
    ∃ (B : GeneralLinear.BlockShape n)
      (σ : ∀ i, GeneralLinear.SupercuspidalRep.{uF, uF} (F := F.Carrier) (n := B.size i)),
      (∀ i, IsUnitarizable (σ i).obj.representation) ∧
      Nonempty (π.representation.Equiv
        (F.canonicalTopologicalData.normalizedProductInduced B
          (fun i => (σ i).obj.representation))) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  obtain ⟨s, ⟨k, ρ, hρs, h, A, hA, hπ, hsub⟩, _⟩ := hx
  let B := T.cuspidalShape ρ h
  have hu (i : Fin k) : IsUnitarizable (A i).obj.representation := by
    have hmem : ρ i ∈ s.map Subtype.val := by
      rw [← hρs, Multiset.mem_coe, List.mem_ofFn]
      exact ⟨i, rfl⟩
    obtain ⟨d, _, hd⟩ := Multiset.mem_map.mp hmem
    have hunitary : (ρ i).IsUnitary := hd ▸ d.property
    change GeneralLinear.SupercuspidalClass.IsUnitarizable (ρ i).cls at hunitary
    rw [← hA i] at hunitary
    exact hunitary
  have hind := Classification.squareIntegrableBlockInduction.{uF, uF}
    F T n hn B (fun i => (A i).obj)
    (fun i => ⟨(A i).property.1,
      Classification.unitarizableSupercuspidal_isSquareIntegrable F
        (B.positive i) (A i) (hu i), hu i⟩)
  exact ⟨B, A, hu, CuspidalInductionConstituent.nonempty_equiv_of_isSubquotient
    hind.1 hπ (SmoothRep.isSubquotient_iff_representation.mp hsub)⟩

end Langlands.VirtualRepresentation.PadicSupercuspidal
