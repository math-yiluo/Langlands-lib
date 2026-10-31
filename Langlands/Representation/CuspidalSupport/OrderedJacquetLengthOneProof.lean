import Langlands.Representation.CuspidalSupport.OrderedJacquetLengthOneStatement
import Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Langlands.Representation.Filtration.IrreducibleMultiplicityProof

/-! Actual equivalences from length one, evaluation and exact multiplicity. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uA uW uZ

/-- The actual ordered equivalences retain independent carrier universes. -/
theorem normalizedJacquetOrderedLengthOneCriterion :
    NormalizedJacquetOrderedLengthOneCriterion.{uF, uA, uW, uZ} := by
  intro p hp F T n B
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A W _ _ Z _ _ σ τ hσ hτ hστ S f hf hS hQ hA
  let X := ((T.normalizedJacquetFunctor B).obj
    (SmoothRep.subrepresentation A S)).representation
  let R := ((T.normalizedJacquetFunctor B).obj A).representation
  let Y := ((T.normalizedJacquetFunctor B).obj (SmoothRep.quotient A S)).representation
  have hX : X.IsIrreducible := repLength_eq_one_iff.mp hS
  have hY : Y.IsIrreducible := repLength_eq_one_iff.mp hQ
  let := hX
  let := hσ
  let g : X.IntertwiningMap σ := jacquetEvaluation T B f
  have hg : g ≠ 0 := jacquetEvaluation_ne_zero T B f hf
  let e : X.Equiv σ :=
    g.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero g).resolve_right hg)
  refine ⟨⟨e⟩, ?_⟩
  have hXτ : ¬ Nonempty (X.Equiv τ) := by
    rintro ⟨v⟩
    exact hστ ⟨e.symm.trans v⟩
  let i := SmoothRep.hom (SmoothRep.subtype A S)
  let q := SmoothRep.hom (SmoothRep.mkQ A S)
  have hi : Function.Injective i := SmoothRep.subtype_injective A S
  have hq : Function.Surjective q := SmoothRep.mkQ_surjective A S
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
    change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  obtain ⟨hiJ, hexJ, hqJ⟩ := T.normalizedJacquetMap_exact B i q A.isSmooth hi hq hex
  obtain ⟨mX, mY, hmX, hmY, hsum⟩ :=
    jordanHolderShortExactDecomposition ℂ (B.Levi F.Carrier)
      (Rep.of X) (Rep.of R) (Rep.of Y) (Rep.of τ)
      (T.normalizedJacquetMap B i) (T.normalizedJacquetMap B q)
      hiJ hqJ hexJ 1 hA
  have hmX0 : mX = 0 := by
    have h := (IrreducibleMultiplicityProof.multiplicity ℂ (B.Levi F.Carrier)
      (Rep.of X) (Rep.of τ) hX mX).mp hmX
    exact (h.resolve_left (fun h => hXτ h.1)).2
  have hmY1 : mY = 1 := by omega
  have h := (IrreducibleMultiplicityProof.multiplicity ℂ (B.Levi F.Carrier)
    (Rep.of Y) (Rep.of τ) hY mY).mp hmY
  exact (h.resolve_right (by omega)).1

end Langlands.CuspidalSupport
