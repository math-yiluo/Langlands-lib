import Langlands.GroupScheme.SimplyConnected.UniversalPropertyStatement
import Langlands.GroupScheme.CentralIsogeny.CommonSemisimpleRefinement
import Langlands.GroupScheme.CentralIsogeny.Uniqueness

/-! # Proof of the universal property of a semisimple simply connected central cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A common semisimple central refinement of `π` and `q` yields a factorization of `π`
through `q`, because simple connectedness of `C` makes the refining isogeny `p : D ⟶ C`
invertible. -/
theorem centralCoverFactorization_of_refinement
    {k : Type u} [Field k]
    {C H G D : GroupScheme (Spec (CommRingCat.of k))}
    (π : C ⟶ G) (q : H ⟶ G) (p : D ⟶ C) (r : D ⟶ H)
    (hC : IsSimplyConnected C) (hD : IsSemisimple D)
    (hp : IsCentralIsogeny p) (hcomm : p ≫ π = r ≫ q) :
    ∃ a : C ⟶ H, a ≫ q = π := by
  have : IsIso p := hC.central_isogeny_isIso D p hD hp
  refine ⟨inv p ≫ r, ?_⟩
  calc
    (inv p ≫ r) ≫ q = inv p ≫ (r ≫ q) := Category.assoc _ _ _
    _ = inv p ≫ (p ≫ π) := by rw [hcomm]
    _ = π := by simp

/-- A central isogeny from a simply connected semisimple group factors uniquely through
every incoming central isogeny from a semisimple group. -/
theorem simplyConnectedCentralCoverUniversalProperty :
    SimplyConnectedCentralCoverUniversalProperty.{u} := by
  intro k _ C G π hC hG hπ H q hH hq
  obtain ⟨D, p, r, hD, hp, -, hcomm⟩ :=
    centralIsogenyCommonSemisimpleRefinement k C H G π q hC.isSemisimple hH hG hπ hq
  obtain ⟨a, ha⟩ := centralCoverFactorization_of_refinement π q p r hC hD hp hcomm
  refine ⟨a, ha, ?_⟩
  intro b hb
  exact IsCentralIsogeny.cancel_of_connectedReductive
    hC.isSemisimple.isConnectedReductive hq (hb.trans ha.symm)

end Langlands.GroupScheme
