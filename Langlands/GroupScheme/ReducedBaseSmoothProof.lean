import Langlands.GroupScheme.ReducedBaseSmoothStatement
import Langlands.GroupScheme.ReducedBaseSmooth.Translation
import Langlands.GroupScheme.ReducedBaseSmooth.DimensionBridge
import Langlands.GroupScheme.ReducedBaseSmooth.OmegaRank
import Langlands.GroupScheme.ReducedBaseSmooth.Chart

/-! # Group schemes with smooth connected fibres over a reduced base are smooth -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open ReducedBaseSmooth

/-- **Local criterion.** Let `q : Y ⟶ S` be locally of finite type over a reduced locally
Noetherian base, with a section `e`. If the residue fibres of `q` over an open `U` are all
smooth of relative dimension `n`, then `e s` lies in the smooth locus of `q` for `s ∈ U`. -/
theorem ReducedBaseSmooth.mem_smoothLocus_of_fibres {S Y : Scheme.{u}} [IsReduced S]
    [IsLocallyNoetherian S] (q : Y ⟶ S) [LocallyOfFiniteType q] (e : S ⟶ Y)
    (he : e ≫ q = 𝟙 S) (n : ℕ) (U : S.Opens)
    (hU : ∀ t ∈ U, SmoothOfRelativeDimension n (q.fiberToSpecResidueField t)) (s : S)
    (hs : s ∈ U) : e s ∈ q.smoothLocus :=
  mem_smoothLocus_of_fibres_of_finrank
    finrank_residueField_tensor_kaehler_eq q e he n U hU s hs

/-- SGA 3, Exposé VI_B, Corollaire 4.4, for a reduced locally Noetherian base and connected
fibres: a group scheme locally of finite type whose fibres are smooth and connected, of
locally constant dimension, is smooth. -/
theorem reducedBaseConnectedFibreSmooth : ReducedBaseConnectedFibreSmoothStatement.{u} := by
  intro S H hred hnoeth hlft hsm hconn hlc
  have := hred
  have := hnoeth
  have := hlft
  apply smooth_of_range_unit_subset_smoothLocus H hsm hconn
  rintro _ ⟨s, rfl⟩
  obtain ⟨U, n, hs, hU⟩ := exists_open_smoothOfRelativeDimension_fiber H.X.hom hsm hconn hlc s
  exact mem_smoothLocus_of_fibres H.X.hom η[H.X].left (Over.w η[H.X]) n U hU s hs

end Langlands.GroupScheme
