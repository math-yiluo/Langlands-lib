import Langlands.Representation.CuspidalSupport.NormalHeckeLineStabilizer
import Langlands.Representation.CuspidalSupport.NormalHeckeHomDetection
import Langlands.Representation.CuspidalSupport.RationalNormKernelFiniteRestrictionProof
import Langlands.Representation.CuspidalSupport.RationalSummandStabilizerLemmaStatement

/-! Renard VI.4.4, Lemma: proof of `RationalSummandStabilizerLemmaStatement`, from the generic
`NormalHecke.lineStabilizer` applied to `H = ⁰G` with the valuation degree, the finite-length
clause of the published VI.3.2(ii) proof, and the published `NormalHeckeHomDetection`. -/

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

open Aubert.General Aubert.General.RationalPointFamily GroupScheme

/-- **Renard VI.4.4, Lemma.** -/
theorem rationalSummandStabilizerLemma : RationalSummandStabilizerLemmaStatement.{uF, uV} := by
  intro F _ _ _ _ G hG S i hi _ _ _ ν hν hStandard hRoots hU h π hπ hcusp ρ hρ hex Res T
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let _ : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) := rationalPoint_isTopologicalGroup F G
  have hlen := (rationalNormKernelFiniteRestriction F G hG π hπ).2.1
  classical
  have : ρ.representation.IsIrreducible := hρ
  have := finiteDimensional_rationalSummandHom hρ hlen
  obtain ⟨j₀, hj₀⟩ := hex
  have := nontrivial_rationalSummandHom hρ j₀ hj₀
  exact NormalHecke.lineStabilizer ρ (isOpen_rationalCommonNormKernel G)
    (isDegree_rationalValuation G) (rank_le_aleph0_of_rationalCommonNormKernel G ρ hρ) π
    (rationalSummand_cyclic_of_isIrreducible hπ hρ)
    (rationalSummand_twistIso_of_isIrreducible hπ hρ) (fun g => mem_rationalTwistGroup_iff g)
    ⟨j₀, hj₀⟩

end Langlands.CuspidalSupport
