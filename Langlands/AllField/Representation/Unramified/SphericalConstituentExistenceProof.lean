import Langlands.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.AllField.Group.GL.BlockIwahoriBasis
import Langlands.AllField.Group.GL.BlockIwahoriDefinitionsSupplement
import Langlands.AllField.Group.GL.CompactOpenSupplement
import Langlands.AllField.Group.GL.UnramifiedCharacterSupplement
import Langlands.AllField.HarmonicAnalysis.ConductorSupplement
import Langlands.AllField.Representation.CuspidalSupport.NormalizedCuspidalInductionStatementSupplement
import Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.Jacquet.ParabolicSupplement
import Langlands.AllField.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.AllField.Representation.Parabolic.NormalizedInductionStatementSupplement
import Langlands.AllField.Representation.Parabolic.RefinementCompositionSupplement
/-! # Existence of spherical constituents of unramified principal series -/

noncomputable section

namespace Langlands.AllField.Unramified
open Langlands.Unramified
open Langlands.AllField.Unramified

open Langlands.Correspondence

universe uF uG uV uW

namespace SphericalExistence
open Langlands.Unramified.SphericalExistence hiding exists_compactOpenSubgroup_le sphericalExistenceGeneralLinearTopology
open Langlands.AllField.Unramified.SphericalExistence
open Langlands.Unramified
open Langlands.AllField.Unramified

section Generic


end Generic

section Specific

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance sphericalExistenceGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopology n

/-- Every open subgroup of `GL_(r+1)(F)` contains a compact open subgroup. -/
theorem exists_compactOpenSubgroup_le {r : ℕ}
    (H : OpenSubgroup (GeneralLinear (r + 1) F)) :
    ∃ K : OpenSubgroup (GeneralLinear (r + 1) F),
      IsCompact (K : Set (GeneralLinear (r + 1) F)) ∧ K ≤ H := by
  obtain ⟨K, hK, hKH, -⟩ :=
    Langlands.AllField.GeneralLinear.BlockShape.exists_compactOpenSubgroup_hasBlockIwahoriFactorization
      (borelShape r) (⟨⟩ : LocalFieldData F)
      (H.isOpen.mem_nhds H.one_mem)
  exact ⟨K, hK, hKH⟩

end Specific

end SphericalExistence

end Langlands.AllField.Unramified
