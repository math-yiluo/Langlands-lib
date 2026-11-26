import Langlands.BushnellKutzko.BetaExtensionTwist.DomainProduct
import Langlands.BushnellKutzko.BetaExtensionTwist.Intertwining
import Langlands.BushnellKutzko.BetaExtensionTwist.Multiplicity
import Langlands.BushnellKutzko.BetaExtensionTwistStatement
import Langlands.BushnellKutzko.HeisenbergRepresentationStatement
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesStatement
import Langlands.Weil.Representation.IsomorphismInvarianceProof

/-! # The beta-extension twist from the Heisenberg and simple-stratum properties -/

noncomputable section
open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uW uW₁ uW₂

section Irreducibility

variable {F : Type uF} [Field F] [ValuativeRel F] {V : Type uV} [AddCommGroup V] [Module F V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {W₁ : Type uW₁} [AddCommGroup W₁] [Module ℂ W₁]
  {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂] [FiniteDimensional ℂ W₂]

/-- The irreducibility clause of the beta-extension twist. -/
theorem isIrreducible_betaExtension_tprod (L : LatticeChain 𝒪[F] F V) (n : ℤ)
    (β : Module.End F V) (tail : List (Module.End F V))
    (θ : simpleHGroup L n β tail 1 →* ℂˣ)
    (η : Representation ℂ (simpleJGroup L n β tail 1) W)
    (hη : IsHeisenbergRepresentation L n β tail θ η)
    (κ : Representation ℂ (simpleJ L n β tail) W₁) (hκ : IsBetaExtension L n β tail η κ)
    (ξ : Representation ℂ (simpleJ L n β tail) W₂) (hξ : ξ.IsIrreducible)
    (ht : ∀ j : simpleJ L n β tail,
      (j : (Module.End F V)ˣ) ∈ simpleJGroup L n β tail 1 → ξ j = 1) :
    (κ.tprod ξ).IsIrreducible := by
  have := hκ.1
  obtain ⟨e⟩ := hκ.2.2.1
  exact isIrreducible_tensor_of_irreducible_restriction
    (Subgroup.inclusion (simpleJGroup_one_le_simpleJ L n β tail)) κ ξ
    ((Langlands.Weil.IsomorphismInvariance.irreducible_iff e).mpr hη.2.2.1)
    hξ (fun k => ht _ k.property)

end Irreducibility

/-- The beta-extension twist as a consequence of Heisenberg theory and the
simple-stratum lattice and subgroup properties. -/
def BetaExtensionTwistReductionStatement : Prop :=
  HeisenbergRepresentationStatement.{uF, uV, uW, uW₁, uW₂} →
    SimpleStratumLatticePropertiesStatement.{uF, uV} →
    SimpleStratumGroupPropertiesStatement.{uF, uV} →
    BetaExtensionTwistStatement.{uF, uV, uW, uW₁, uW₂}

/-- The Heisenberg representation theorem and the simple-stratum lattice and
subgroup properties imply the beta-extension twist. -/
theorem betaExtensionTwist_of : BetaExtensionTwistReductionStatement.{uF, uV, uW, uW₁, uW₂} := by
  intro hV₁ hlattices hgroups F _ _ _ _ V _ _ ψF hψ S hr hs q θ hθ W _ _ η hη W₁ _ _ κ hκ W₂ _ _ _ ξ hξ ht
  let J := simpleJ S.chain S.n S.b q.tail
  let K := simpleJGroup S.chain S.n S.b q.tail 1
  let U := relativeUnitFiltration S.chain S.b 0
  let B := centralizerUnitGroup S.b
  let hK : K ≤ J := simpleJGroup_one_le_simpleJ S.chain S.n S.b q.tail
  let hU : U ≤ J := relativeUnitFiltration_le_simpleJ S.chain S.n S.b q.tail
  let κK : Representation ℂ K W₁ := κ.comp (Subgroup.inclusion hK)
  have := hκ.1
  obtain ⟨e⟩ := hκ.2.2.1
  have hηSupp : representationSelfIntertwining η = ((K : Set (Module.End F V)ˣ) * B) * K :=
    ((hV₁ F V ψF hψ S hr hs q θ hθ).2.2 W η hη).2.2
  have hsupport : representationSelfIntertwining κK ⊆ ((K : Set (Module.End F V)ˣ) * B) * K := by
    intro y hy
    obtain ⟨f, hf⟩ := hy
    rw [← hηSupp]
    let E := intertwiningSpaceCongr e y
    exact ⟨E f, fun h => hf (E.map_eq_zero_iff.mp h)⟩
  have hline' (y : (Module.End F V)ˣ) (hy : y ∈ B) :
      Module.finrank ℂ (intertwiningSpace κK κK y) ≤ 1 := by
    rw [(intertwiningSpaceCongr e y).finrank_eq]
    have hy' : y ∈ representationSelfIntertwining η := by
      rw [hηSupp]
      simpa only [one_mul, mul_one] using
        (Set.mul_mem_mul (Set.mul_mem_mul K.one_mem hy) K.one_mem :
          1 * y * 1 ∈ ((K : Set (Module.End F V)ˣ) * B) * K)
    exact (heisenberg_intertwining_finrank_eq_one hV₁ hlattices hgroups
      ψF hψ S hr hs q θ hθ η hη y hy').le
  have hcarrier : (J : Set (Module.End F V)ˣ) = simpleJCarrier S.chain S.n S.b q.tail 0 :=
    ((hgroups F V S hr hs q).1 0).2
  obtain ⟨hsupp, hdim⟩ := tprod_intertwining_of_restriction hK κ ξ ht hU (B : Set (Module.End F V)ˣ)
    hsupport hκ.2.2.2 hline' (fun y hy => simpleJ_intertwiningDomain_product S hr hs q hcarrier y hy)
  exact ⟨hsupp, hdim, isIrreducible_betaExtension_tprod S.chain S.n S.b q.tail θ η hη κ hκ ξ hξ ht⟩

end Langlands.BushnellKutzko
