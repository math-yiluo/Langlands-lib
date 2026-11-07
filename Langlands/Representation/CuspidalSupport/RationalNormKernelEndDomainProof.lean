import Langlands.Representation.CuspidalSupport.RationalNormKernelEndDomainStatement
import Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeDomain
import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Plancherel.RationalCharacterValuation

/-! Renard VI.4.3, Corollary (i): `End (ind_{⁰G}^G ρ)` is a domain. The quotient `G ⧸ ⁰G`
embeds, through the rational-character valuation, in the group
`Multiplicative (X*(G) → ℤ)` of all integer-valued functions on the rational characters.
That group has unique products, because `ℤ` has unique sums and unique sums pass to
function types (no freeness of the full function group is used), so `G ⧸ ⁰G` has unique
products; the generic result of `NormalSubgroupHeckeDomain` then applies to the open normal
subgroup `⁰G`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))

/-- `G ⧸ ⁰G` has unique products: the valuation `g ↦ (χ ↦ ord χ(g))` identifies it with a
subgroup of `Multiplicative (X*(G) → ℤ)`. -/
theorem rationalNormKernelQuotient_uniqueProds :
    UniqueProds (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) := by
  let f : (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) →*
      Multiplicative (GroupScheme.rationalCharacters G → ℤ) :=
    (AddMonoidHom.toMultiplicative (AddMonoidHom.coeFn (GroupScheme.rationalCharacters G) ℤ)).comp
      ((rationalCharacterValuationImage G).subtype.comp
        (rationalNormKernelQuotientEquiv G).toMonoidHom)
  have hf : Function.Injective f := by
    intro a b h
    apply (rationalNormKernelQuotientEquiv G).injective
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact DFunLike.coe_injective (congrArg Multiplicative.toAdd h)
  exact UniqueProds.of_injective_mulHom f.toMulHom hf inferInstance

end

/-- Renard VI.4.3, Corollary (i). -/
theorem rationalNormKernelEnd_isDomain : RationalNormKernelEndDomainStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  intro ρ hρ
  have : ρ.representation.IsIrreducible := hρ
  have := rationalNormKernelQuotient_uniqueProds G
  exact NormalHecke.isDomain (rationalCommonNormKernel G) ρ (isOpen_rationalCommonNormKernel G)

end Langlands.CuspidalSupport
