import Langlands.AbelianScheme.Lie
import Langlands.AlgebraicGeometry.SmoothDifferentialsFiniteLocalBasisRank
import Langlands.AlgebraicGeometry.PullbackFiniteLocalBasisRankProof
import Langlands.AlgebraicGeometry.ModuleDualFiniteLocalBasis

/-! # Finite local frames of the actual Lie sheaf of a smooth group scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S) (hG : Smooth G.X.hom)

include hG

/-- Pulling smooth differentials back to the identity gives finite local cotangent bases. -/
theorem cotangentAtIdentity_hasFiniteLocalBasis :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} G.cotangentAtIdentity,
      q.IsLocallyFreeData ∧ q.IsFiniteType := by
  have hΩ := Langlands.Scheme.smoothDifferentialsFiniteLocalBasisRank G.X.left S G.X.hom
  exact (Langlands.Scheme.Modules.pullbackFiniteLocalBasisRank
    S G.X.left G.identitySection (Langlands.Scheme.relativeDifferentials G.X.hom)).1
      (hΩ.1 hG)

/-- The actual internal Lie sheaf has finite local bases over an arbitrary base. -/
theorem lie_hasFiniteLocalBasis :
    ∃ q : SheafOfModules.LocalGeneratorsData.{u} G.Lie,
      q.IsLocallyFreeData ∧ q.IsFiniteType :=
  Langlands.Scheme.Modules.dual_hasFiniteLocalBasis
    (G.cotangentAtIdentity_hasFiniteLocalBasis hG)

/-- Choose cotangent frames only from their proved existence. -/
def cotangentFiniteLocalBasisData :
    SheafOfModules.LocalGeneratorsData.{u} G.cotangentAtIdentity :=
  (G.cotangentAtIdentity_hasFiniteLocalBasis hG).choose

instance cotangentFiniteLocalBasisData_isLocallyFreeData :
    (G.cotangentFiniteLocalBasisData hG).IsLocallyFreeData :=
  (G.cotangentAtIdentity_hasFiniteLocalBasis hG).choose_spec.1

instance cotangentFiniteLocalBasisData_isFiniteType :
    (G.cotangentFiniteLocalBasisData hG).IsFiniteType :=
  (G.cotangentAtIdentity_hasFiniteLocalBasis hG).choose_spec.2

instance cotangentFiniteLocalBasisIndex_fintype
    (i : (G.cotangentFiniteLocalBasisData hG).I) :
    Fintype ((G.cotangentFiniteLocalBasisData hG).generators i).I := by
  let := ((G.cotangentFiniteLocalBasisData_isFiniteType hG).isFiniteType i).finite
  exact Fintype.ofFinite _

/-- The cotangent sheaf is actually free on each chosen open. -/
def cotangentFiniteLocalBasisTrivialization
    (i : (G.cotangentFiniteLocalBasisData hG).I) :
    SheafOfModules.free
        (R := S.ringCatSheaf.over ((G.cotangentFiniteLocalBasisData hG).X i))
        ((G.cotangentFiniteLocalBasisData hG).generators i).I ≅
      G.cotangentAtIdentity.over ((G.cotangentFiniteLocalBasisData hG).X i) :=
  by
    letI := (G.cotangentFiniteLocalBasisData_isLocallyFreeData hG).isIso i
    exact asIso ((G.cotangentFiniteLocalBasisData hG).generators i).π

/-- Dual frames retain the cotangent cover and its finite basis index types. -/
def lieFiniteLocalBasisData :
    SheafOfModules.LocalGeneratorsData.{u} G.Lie :=
  Langlands.Scheme.Modules.dualLocalGeneratorsData (G.cotangentFiniteLocalBasisData hG)

instance lieFiniteLocalBasisData_isLocallyFreeData :
    (G.lieFiniteLocalBasisData hG).IsLocallyFreeData :=
  Langlands.Scheme.Modules.dualLocalGeneratorsData_isLocallyFreeData
    (G.cotangentFiniteLocalBasisData hG)

instance lieFiniteLocalBasisData_isFiniteType :
    (G.lieFiniteLocalBasisData hG).IsFiniteType :=
  Langlands.Scheme.Modules.dualLocalGeneratorsData_isFiniteType
    (G.cotangentFiniteLocalBasisData hG)

instance lieFiniteLocalBasisIndex_fintype (i : (G.lieFiniteLocalBasisData hG).I) :
    Fintype ((G.lieFiniteLocalBasisData hG).generators i).I := by
  let := ((G.lieFiniteLocalBasisData_isFiniteType hG).isFiniteType i).finite
  exact Fintype.ofFinite _

/-- The Lie sheaf is actually free on each open of the constructed cover. -/
def lieFiniteLocalBasisTrivialization (i : (G.lieFiniteLocalBasisData hG).I) :
    SheafOfModules.free
        (R := S.ringCatSheaf.over ((G.lieFiniteLocalBasisData hG).X i))
        ((G.lieFiniteLocalBasisData hG).generators i).I ≅
      G.Lie.over ((G.lieFiniteLocalBasisData hG).X i) :=
  by
    letI := (G.lieFiniteLocalBasisData_isLocallyFreeData hG).isIso i
    exact asIso ((G.lieFiniteLocalBasisData hG).generators i).π

end Langlands.GroupScheme
