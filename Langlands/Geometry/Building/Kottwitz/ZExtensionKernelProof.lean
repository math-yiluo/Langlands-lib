import Langlands.Geometry.Building.Kottwitz.ZExtensionRationalKernelReduction
import Langlands.Geometry.Building.Kottwitz.CentralTorusExactnessProof
import Langlands.Geometry.Building.Kottwitz.CentralTorusInertiaInjectivityProof
import Langlands.Geometry.Building.Kottwitz.InducedTorusRationalSurjectivityProof
import Langlands.Geometry.Building.Kottwitz.ReductiveFunctorialityProof
import Langlands.Geometry.Building.Kottwitz.ReductiveMapRemainingInputs
import Langlands.Geometry.Building.Kottwitz.ReductiveMapDescentReduction
import Langlands.Geometry.Building.Kottwitz.SimplyConnectedDerivedKottwitzProof
import Langlands.Geometry.Building.Kottwitz.TorusKottwitzEquivariance
import Langlands.Geometry.Building.Kottwitz.FundamentalInertiaMapProof
import Langlands.Geometry.Building.Kottwitz.TorusInertiaComparisonProof
import Langlands.GroupScheme.ZExtensionMorphismDominationProof
import Langlands.GroupScheme.Torus.ZExtensionPointSurjectivityProof

/-! # KP Proposition 11.5.3, kernel clause: proof -/

noncomputable section
universe u

open CategoryTheory
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.Kottwitz

/-- Existence of the reductive Kottwitz homomorphisms (KP Lemma 11.5.1 and the
definition after it), assembled from the conditional existence theorem
`reductiveKottwitzExistence_of_remaining_inputs` and proved inputs. The common
domination input is the case `f = 𝟙 G` of `zExtensionMorphismDomination`. -/
theorem reductiveKottwitzExistence_assembled : ReductiveKottwitzExistenceStatement.{u} := by
  have hcommon : ZExtensionCommonDominationStatement.{u} := by
    intro k _ G hG z t
    obtain ⟨w, r, s, hr, hs⟩ := zExtensionMorphismDomination k G G hG hG z t (𝟙 G)
    exact ⟨w, r, s, hr, by simpa using hs⟩
  exact reductiveKottwitzExistence_of_remaining_inputs fundamentalInertiaMapStatement
    zExtensionPointSurjectivity centralTorusInertiaExactness hcommon

/-- Galois descent of the reductive Kottwitz homomorphisms, assembled from the
conditional theorem `reductiveKottwitzDescent_of_inputs` and proved inputs. -/
theorem reductiveKottwitzDescent_assembled : ReductiveKottwitzDescentStatement.{u} :=
  reductiveKottwitzDescent_of_inputs simplyConnectedDerivedKottwitz_proof
    reductiveKottwitzExistence_assembled fundamentalInertiaMapStatement
    torusInertiaComparison_proof generalTorusKottwitzEquivariance

/-- **KP Proposition 11.5.3, kernel clause.** For every z-extension `1 → Z → H → G → 1`,
the projection maps the Kottwitz kernel of `H` onto the Kottwitz kernel of `G`, both for
points over the maximal unramified extension (first conjunct) and for rational points
(second conjunct). -/
theorem zExtensionKottwitzKernelSurjectivity :
    ZExtensionKottwitzKernelSurjectivityStatement.{u} :=
  zExtensionKottwitzKernelSurjectivityStatement_iff.2
    ⟨zExtensionUnramifiedKernelReduction reductiveKottwitzExistence_assembled
        reductiveKottwitzFunctoriality centralTorusInertiaExactness,
      zExtensionRationalKernelReduction reductiveKottwitzFunctoriality
        reductiveKottwitzDescent_assembled centralTorusInertiaExactness
        (fun F _ _ _ _ _ z => inducedCentralTorusInertiaInjectivity.zExtension F
          (UnramifiedClosure F) (SeparableClosure F) z)
        inducedTorusKottwitzRationalSurjectivity zExtensionPointSurjectivity⟩

end Langlands.Geometry.Building.Kottwitz
