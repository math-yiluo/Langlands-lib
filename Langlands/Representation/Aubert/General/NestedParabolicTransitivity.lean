import Langlands.Representation.Aubert.General.NestedParabolicModulus
import Langlands.Representation.Aubert.General.NestedInductionStages
import Langlands.Representation.Aubert.General.JacquetStages

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

universe uG uV
open CategoryTheory Topology
open scoped Pointwise

namespace Langlands.Aubert.General.NestedParabolic

section Algebra

variable {G : Type uG} [Group G] {L U N : Subgroup G}

/-- The actual radical product also identifies the join used by coinvariants. -/
theorem unipotent_sup_inter
    (hprod : (N : Set G) = (L ⊓ N : Subgroup G) * (U : Set G)) :
    U ⊔ (L ⊓ N) = N := by
  apply le_antisymm
  · exact sup_le (unipotent_le hprod) inf_le_right
  · intro n hn
    change n ∈ (N : Set G) at hn
    rw [hprod] at hn
    obtain ⟨w, hw, u, hu, rfl⟩ := Set.mem_mul.mp hn
    exact (U ⊔ (L ⊓ N)).mul_mem
      (Subgroup.mem_sup_right hw) (Subgroup.mem_sup_left hu)

end Algebra

section Modulus

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
    [NonarchimedeanGroup G] [SecondCountableTopology G]
    {P M N Q L U : Subgroup G}
    (hP : IsSemidirectDecomposition P M N)
    (hQ : IsSemidirectDecomposition Q L U)
    (hL : IsClosed (L : Set G)) (hN : IsClosed (N : Set G))
    (hU : IsClosed (U : Set G))
    (hPQ : P ≤ Q)
    (hprod : (N : Set G) = (L ⊓ N : Subgroup G) * (U : Set G))
    (hp : Continuous hQ.projection)

include hP hQ hPQ hprod hp

/-- The positive product with the literal inner radical and acting-group copy. -/
theorem modulus_product {S : Subgroup G} (hSL : S ≤ L)
    (hSN : S ≤ Subgroup.normalizer (N : Set G)) (s : S) :
    let := hL.locallyCompactSpace
    HaarModulus.closedRestrictCharacter N hN S hSN s =
      HaarModulus.closedRestrictCharacter U hU L hQ.levi_le_normalizer
        ⟨s, hSL s.property⟩ *
      HaarModulus.closedRestrictCharacter (N.subgroupOf L)
        (hN.preimage continuous_subtype_val) (S.subgroupOf L)
        (normalizes_subgroupOf hSN) ((subgroupOfContinuousEquiv hSL).symm s) := by
  let := hL.locallyCompactSpace
  dsimp only
  rw [inner_modulus_eq hN hL hSL hSN s]
  exact (ambient_modulus_product hQ (hP.unipotent_le.trans hPQ) hprod hp
    hN hU hL hSL hSN s).trans (mul_comm _ _)

/-- Multiplicativity of the canonical positive square root gives exactly the
normalization premise used by normalized induction in stages. -/
theorem halfCharacterProduct
    (hInner : IsSemidirectDecomposition
      (P.subgroupOf L) (M.subgroupOf L) (N.subgroupOf L)) :
    NestedInduction.HalfCharacterProduct hP hQ hL hInner hN hU := by
  let := hL.locallyCompactSpace
  intro p
  let s : (L ⊓ P : Subgroup G) := ⟨p.val.val, p.val.property, p.property⟩
  have hδ := modulus_product hP hQ hL hN hU hPQ hprod hp
    (S := L ⊓ P) inf_le_left (inf_le_right.trans hP.le_normalizer) s
  change HaarModulus.closedRestrictCharacter N hN P hP.le_normalizer
      ⟨p.val.val, p.property⟩ =
    HaarModulus.closedRestrictCharacter U hU L hQ.levi_le_normalizer p.val *
      HaarModulus.closedRestrictCharacter (N.subgroupOf L)
        (hN.preimage continuous_subtype_val) (P.subgroupOf L)
        hInner.le_normalizer p at hδ
  let κ : NNRealˣ →* ℂˣ :=
    (Units.map (Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom).comp
      (Units.map NNReal.sqrtHom.toMonoidHom)
  change κ (HaarModulus.closedRestrictCharacter N hN P hP.le_normalizer
      ⟨p.val.val, p.property⟩) =
    κ (HaarModulus.closedRestrictCharacter U hU L hQ.levi_le_normalizer p.val) *
      κ (HaarModulus.closedRestrictCharacter (N.subgroupOf L)
        (hN.preimage continuous_subtype_val) (P.subgroupOf L) hInner.le_normalizer p)
  rw [hδ, map_mul]

/-- Normalized Jacquet restriction in stages for the actual fine and coarse
radicals, with the positive modulus product derived from their actual product. -/
def jacquetIso (hML : M ≤ L)
    (hInner : IsSemidirectDecomposition
      (P.subgroupOf L) (M.subgroupOf L) (N.subgroupOf L))
    (hWc : Jacquet.Localization.IsLimitOfCompactSubgroups (N.subgroupOf L)) :
    jacquetFunctor.{uG, uV} hP hN ≅
      jacquetFunctor.{uG, uV} hQ hU ⋙
        leviNormalizedJacquetFunctor.{uG, uV} hL hML hInner hN := by
  have hjoin := unipotent_sup_inter hprod
  have hMN := normalizes_inter hML hP.levi_le_normalizer
  have hW : IsClosed (((L ⊓ N).subgroupOf L) : Set L) := by
    simpa only [Subgroup.inf_subgroupOf_left, Subgroup.coe_subgroupOf,
      Subgroup.coe_subtype] using
      hN.preimage (continuous_subtype_val (p := (· ∈ L)))
  have hV : IsClosed ((U ⊔ (L ⊓ N) : Subgroup G) : Set G) := by
    rw [hjoin]
    exact hN
  have hWc' : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((L ⊓ N).subgroupOf L) := by
    simpa only [Subgroup.inf_subgroupOf_left] using hWc
  letI := hL.locallyCompactSpace
  have hδ0 :
      (HaarModulus.closedRestrictCharacter U hU L hQ.levi_le_normalizer).comp
          (Subgroup.inclusion hML) *
        (HaarModulus.closedRestrictCharacter (N.subgroupOf L)
          (hN.preimage continuous_subtype_val) (M.subgroupOf L)
          hInner.levi_le_normalizer).comp
            (subgroupOfContinuousEquiv hML).symm.toMonoidHom =
      HaarModulus.closedRestrictCharacter N hN M hP.levi_le_normalizer := by
    apply MonoidHom.ext
    intro m
    exact (modulus_product hP hQ hL hN hU hPQ hprod hp
      hML hP.levi_le_normalizer m).symm
  have hδ :
      (HaarModulus.closedRestrictCharacter U hU L hQ.levi_le_normalizer).comp
          (Subgroup.inclusion hML) *
        innerJacquetModulus U L (L ⊓ N) M inf_le_left hML
          hQ.levi_le_normalizer hMN hL hW =
      HaarModulus.closedRestrictCharacter (U ⊔ (L ⊓ N)) hV M
        (jacquetTowerDatum U L (L ⊓ N) M inf_le_left hML
          hQ.levi_le_normalizer hMN).H_le_normalizer_sup := by
    simpa only [innerJacquetModulus, jacquetTowerDatum,
      Subgroup.inf_subgroupOf_left, hjoin] using hδ0
  symm
  simpa only [iteratedNormalizedJacquetFunctor, jacquetFunctor,
    leviNormalizedJacquetFunctor, jacquetTowerDatum,
    Subgroup.inf_subgroupOf_left, hjoin, Functor.assoc] using
    (normalizedJacquetStagesIso.{uG, uV} U L (L ⊓ N) M inf_le_left hML
      hQ.levi_le_normalizer hMN hU hL hW hV hWc' hδ)

end Modulus

end Langlands.Aubert.General.NestedParabolic
