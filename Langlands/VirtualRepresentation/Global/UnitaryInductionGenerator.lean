import Langlands.VirtualRepresentation.Global.UnitaryRestriction
import Langlands.VirtualRepresentation.Supercuspidal.UnitaryInductionSupport

/-!
# Relative generators from actual unitary induction factors

Combine the full canonical Weil expansion with the integral sum of supplied
unitary supercuspidal factors of the actual automorphic local component.
-/

noncomputable section

universe uF uW uP

namespace Langlands.VirtualRepresentation.RelativeGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic
open scoped Classical

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)
  [CompactSpace (AdeleQuotient F)]

namespace WitnessedGenerator

variable {r : ℕ}
  (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
  (hirr : S.IsIrreducible) (hu : S.IsUnitary)
  (T : CuspidalOperatorRealization F r)
  (P : CuspidalSpectralPresentation.{uF, uP} T)
  (hassoc : RelativeWeilGroup.IsWeaklyAssociated S P.spectralSystem)
  (w : FinitePlacesAbove E v)
  (rec : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
  (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
  (hι : RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 rec ι)
  (hlirr : (P.localComponent v).IsIrreducible)
  (hladm : (P.localComponent v).IsAdmissible)
  (B : GeneralLinear.BlockShape (r + 1))
  (σ : letI := (padicField v).canonicalTopologicalData.topology
    ∀ i, GeneralLinear.SupercuspidalRep.{uF, uF}
      (F := (padicField v).Carrier) (n := B.size i))
  (hσ : letI := (padicField v).canonicalTopologicalData.topology
    ∀ i, IsUnitarizable (σ i).obj.representation)
  (e : letI := (padicField v).canonicalTopologicalData.topology
    ((P.localComponent v).padicObject hlirr hladm).obj.representation.Equiv
      ((padicField v).canonicalTopologicalData.normalizedProductInduced B
        fun i => (σ i).obj.representation))

/-- Construct the existing relative generator from the actual induction
conclusion data, without a supplied lattice element or expansion witness. -/
def ofUnitaryInduction : WitnessedGenerator.{uF, uW, uP} F E c v :=
  ofUnitarySupport F E c v S hirr hu T P hassoc w rec ι hι hlirr hladm
    ((padicField v).canonicalTopologicalData.unitaryInductionSupport B σ hσ)
    ((padicField v).canonicalTopologicalData.isUnitaryLatticeSupport_of_normalizedProductEquiv
      B σ hσ ((P.localComponent v).padicObject hlirr hladm).obj hlirr e)

/-- The Weil entry is the canonical expansion of the whole local restriction. -/
@[simp]
theorem ofUnitaryInduction_weilElement :
    (ofUnitaryInduction F E c v S hirr hu T P hassoc w rec ι hι hlirr hladm B σ hσ e).weilElement =
        (localUnitaryExpansion F E c v S hassoc.1 hu ι).val := rfl

/-- The automorphic entry retains every actual induction factor. -/
@[simp]
theorem ofUnitaryInduction_automorphicElement :
    (ofUnitaryInduction F E c v S hirr hu T P hassoc w rec ι hι hlirr hladm B σ hσ e).automorphicElement =
        (padicField v).canonicalTopologicalData.unitaryInductionSupport B σ hσ := rfl

/-- Its coefficient at any unitary datum is the exact factor multiplicity. -/
theorem ofUnitaryInduction_automorphicElement_apply
    (d : PadicField.TopologicalData.UnitaryCuspidalDatum.{uF, uF}
      (padicField v).canonicalTopologicalData) :
    (ofUnitaryInduction F E c v S hirr hu T P hassoc w rec ι hι hlirr hladm B σ hσ e).automorphicElement
        ((padicField v).canonicalTopologicalData.unitaryCuspidalDatumBasisEquiv d) =
      ((List.ofFn ((padicField v).canonicalTopologicalData.blockUnitaryCuspidalDatum
        B σ hσ) : Multiset _).count d : ℤ) :=
  (padicField v).canonicalTopologicalData.unitaryInductionSupport_apply B σ hσ d

end WitnessedGenerator

open WitnessedGenerator in
/-- The full local pair from the supplied actual factors belongs to the
existing paired relative lattice. -/
theorem unitaryInduction_pair_mem
    {r : ℕ}
    (S : FiniteRepresentation.{0, uF, uW} ℂ (RelativeWeilGroup c F E))
    (hirr : S.IsIrreducible) (hu : S.IsUnitary)
    (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uP} T)
    (hassoc : RelativeWeilGroup.IsWeaklyAssociated S P.spectralSystem)
    (w : FinitePlacesAbove E v)
    (rec : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hι : RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 rec ι)
    (hlirr : (P.localComponent v).IsIrreducible)
    (hladm : (P.localComponent v).IsAdmissible)
    (B : GeneralLinear.BlockShape (r + 1))
    (σ : letI := (padicField v).canonicalTopologicalData.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uF}
        (F := (padicField v).Carrier) (n := B.size i))
    (hσ : letI := (padicField v).canonicalTopologicalData.topology
      ∀ i, IsUnitarizable (σ i).obj.representation)
    (e : letI := (padicField v).canonicalTopologicalData.topology
      ((P.localComponent v).padicObject hlirr hladm).obj.representation.Equiv
        ((padicField v).canonicalTopologicalData.normalizedProductInduced B
          fun i => (σ i).obj.representation)) :
    ((localUnitaryExpansion F E c v S hassoc.1 hu ι).val,
      (padicField v).canonicalTopologicalData.unitaryInductionSupport B σ hσ) ∈
        pairedLattice.{uF, uW, uP} F E c v :=
  witnessed_pair_mem
    (ofUnitaryInduction F E c v S hirr hu T P hassoc w rec ι hι hlirr hladm B σ hσ e)

end Langlands.VirtualRepresentation.RelativeGlobal
