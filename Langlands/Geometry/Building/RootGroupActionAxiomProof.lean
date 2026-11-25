import Langlands.Geometry.Building.RootGroupActionAxiomStatement
import Langlands.Geometry.Building.ZeroFixerNormalizerReduction
import Langlands.Geometry.Building.IwahoriWeylExactSequenceReduction
import Langlands.Geometry.Building.RootGroupZeroFixer
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylProof

/-! # Axiom 4.1.8 (2) and (3) for the building of a valuation of the root datum: proof -/

universe u

open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

/-- **KP Axiom 4.1.8 (2), (3)** for the building of supplied data over a nonarchimedean local
field, under V 7 and AS 2–AS 5: for every non-empty bounded `Ω ⊆ A(S)`, `G(F)^0_Ω` is generated
by `Z(F)^0` and the `U_ψ` with `ψ ∈ Ψ` non-negative on `Ω`, and
`U_a(F) ∩ G(F)^0_Ω = U_{a,Ω,0}` for every relative root `a`. -/
theorem rootGroupActionAxiom : RootGroupActionAxiomStatement.{u} :=
  fun _ _ _ _ _ _ _ P hP => ⟨P.hasZeroFixerGenerators_of_hasNormalizerParahoricFixers hP
    (P.hasNormalizerParahoricFixers_of_mem_affineWeylGroup hP fun n hn =>
      P.normalizerAffineEquiv_mem_affineWeylGroup hP simplyConnectedNormalizerAffineWeyl
        ⟨n, Subgroup.mem_subgroupOf.2 hn⟩), P.hasRootZeroFixers hP⟩

end Langlands.Geometry.Building
