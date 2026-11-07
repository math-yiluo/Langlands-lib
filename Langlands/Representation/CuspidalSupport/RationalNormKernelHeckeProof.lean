import Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeStatement
import Langlands.Representation.CuspidalSupport.NormalSubgroupHecke
import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! Renard VI.4.2: `End (ind_{⁰G}^G ρ)` is the Hecke space `H(G,ρ)`, with composition
corresponding to convolution. The proof specializes the generic development of
`NormalSubgroupHecke` to the open normal subgroup `⁰G`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard VI.4.2, Proposition. -/
theorem rationalNormKernelHecke_equiv : RationalNormKernelHeckeStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  intro ρ hρ I f
  have : ρ.representation.IsIrreducible := hρ
  have hH := isOpen_rationalCommonNormKernel G
  refine ⟨NormalHecke.heckeEquiv (rationalCommonNormKernel G) ρ hH, ?_, ?_, ?_⟩
  · intro α g w
    exact NormalHecke.heckeEquiv_apply (rationalCommonNormKernel G) ρ hH α g w
  · intro φ v x
    exact NormalHecke.eval_endOfHecke (rationalCommonNormKernel G) ρ hH φ v x
  · intro α β
    exact NormalHecke.heckeEquiv_mul (rationalCommonNormKernel G) ρ hH α β

end Langlands.CuspidalSupport
