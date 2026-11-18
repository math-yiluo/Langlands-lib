import Langlands.Representation.Jacquet.StandardInducedRayThreshold

/-! # Common thresholds for fixed Levi translates of the actual induced ray -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

/-- A shared bi-invariance level refines to a shared bi-invariance level
after left translation by a specified actual group point. -/
theorem biInvariant_mul_left_of_le_conj
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {U L : OpenSubgroup H} {f : H → ℂ}
    (hinv : ∀ (k l : U) g, f ((k : H) * g * (l : H)) = f g)
    (m : H) (hLU : L ≤ U) (hLc : L ≤ Jacquet.conjOpenSubgroup m⁻¹ U) :
    ∀ (k l : L) g, f (m * ((k : H) * g * (l : H))) = f (m * g) := by
  intro k l g
  have hk : m * (k : H) * m⁻¹ ∈ U := by
    simpa only [inv_inv] using (Jacquet.mem_conjOpenSubgroup m⁻¹ U k).mp (hLc k.property)
  calc
    f (m * ((k : H) * g * (l : H))) =
        f ((m * (k : H) * m⁻¹) * (m * g) * (l : H)) := by
      congr 1
      group
    _ = f (m * g) := hinv ⟨_, hk⟩ ⟨l, hLU l.property⟩ (m * g)

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace rationalInducedSecondCountable
  rationalInducedT2 rationalInducedNonarchimedean

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
  (I J : Finset (RationalPointFamily.SimpleRoot i ν))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K.toSubgroup)
  {q : A.toGrp ⟶ S.toGrp}
  (hA : IsCompatibleStandardSplitComponent i ν (RationalPointFamily.rootSet i ν J) A q)
  {ζ : cocharacterLattice S}
  (hζ : IsStandardCocharacter i ν (RationalPointFamily.rootSet i ν J) ζ)
  {K0 : Subgroup (rationalPoints G)} {B : Set (Subgroup (rationalPoints G))}
  (hB : CompactOpenNormalBasis K0 B)
  (hmem : ∀ L ∈ B, StandardParabolicBasisMember i ν (RationalPointFamily.rootSet i ν J) q L)

/-- At the given Levi point the ambient coefficient agrees with its chosen
normalized constant term multiplied by the standard radical half-modulus. -/
abbrev HasStandardConstantTermEqualityAt {J' : Set (characterLattice S)}
    (hA' : IsCompatibleStandardSplitComponent i ν J' A q)
    (f : rationalPoints G → ℂ) (m : standardLeviPoints i ν J') : Prop :=
  f (m : rationalPoints G) =
    standardHalfModulus i ν J' m * standardConstantTerm hA' f m

include hKc hPK hmem in
set_option maxHeartbeats 1200000 in
/-- The actual chosen constant-term ray formula remains uniform after a
fixed Levi translation. The common threshold is the original untwisted
induced dimension at a level fixing the translated original function. -/
theorem standardUnramifiedConstantTerm_mul_ray_threshold
    (τ : SmoothRep.{0, u, uV} ℂ (standardLeviPoints i ν (RationalPointFamily.rootSet i ν I)))
    (hτ : τ.IsAdmissible) {L : Subgroup (rationalPoints G)} (hLB : L ∈ B)
    (ψ : unramifiedCharacters (RationalPointFamily.leviRationalNormCharacters i ν I))
    (t : CoefficientTensor (standardUnramifiedInducedObject hG hi hν I τ ψ))
    (m : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))
    (hinv : ∀ (k l : basisOpenSubgroup hB hLB) (g : rationalPoints G),
      coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ ψ) t
        ((m : rationalPoints G) * ((k : rationalPoints G) * g * (l : rationalPoints G))) =
      coefficientTensorMap (standardUnramifiedInducedObject hG hi hν I τ ψ) t
        ((m : rationalPoints G) * g))
    {r : ℕ} (hr : standardInducedFixedOrder hG hi hν I τ (basisOpenSubgroup hB hLB) ≤ r) :
    let Vψ := standardUnramifiedInducedObject hG hi hν I τ ψ
    let a := (hA.centralStrictElement i ν hi hζ :
      standardLeviPoints i ν (RationalPointFamily.rootSet i ν J))
    HasStandardConstantTermEqualityAt hA (fun g => coefficientTensorMap Vψ t g) (m * a ^ r) := by
  intro Vψ a
  change coefficientTensorMap Vψ t (m * a ^ r : standardLeviPoints i ν _) = _
  let t' := coefficientTensorAction Vψ (1, (m : rationalPoints G)⁻¹) t
  have ht' : (fun g => coefficientTensorMap Vψ t' g) =
      fun g => coefficientTensorMap Vψ t ((m : rationalPoints G) * g) := by
    funext g
    simp only [t', coefficientTensorMap_action, inv_inv, mul_one]
  have hinv' : ∀ (k l : basisOpenSubgroup hB hLB) (g : rationalPoints G),
      coefficientTensorMap Vψ t' ((k : rationalPoints G) * g * (l : rationalPoints G)) =
        coefficientTensorMap Vψ t' g := by
    intro k l g
    simpa only [t', coefficientTensorMap_action, inv_inv, mul_one] using hinv k l g
  have h := standardUnramifiedConstantTerm_ray_threshold hG hi hν I hKc hPK
    hζ hB hA hmem τ hτ hLB ψ t' hinv' hr
  obtain ⟨hadm, _⟩ := standardUnramifiedInduced_admissible_finrank
    hG hi hν I hKc hPK τ hτ (basisOpenSubgroup hB hLB) (hB.1 L hLB).2.2.2 ψ
  let E := standardCasselmanPairingData hG hi hν hζ hB hA hmem
  have hAd : E.Admits Vψ.representation Vψ.isSmooth :=
    standardCasselmanPairingData_admits hG hi hν hζ hB hA hmem Vψ.representation hadm
  obtain ⟨b, hb⟩ := E.exists_isStablePairing hAd
  have hCT : HasStandardConstantTerm hA (fun g => coefficientTensorMap Vψ t g) :=
    ⟨_, coefficientTensorConstantTerm_spec hG hi hν hζ hB hA hmem Vψ hadm hb t⟩
  have hleft := standardConstantTerm_mul_left hi hζ hA hCT m
  change coefficientTensorMap Vψ t' (a ^ r) = _ at h
  change (fun g => coefficientTensorMap Vψ t' g) _ = _ at h
  rw [ht', hleft] at h
  have h' : coefficientTensorMap Vψ t
      ((m * a ^ r : standardLeviPoints i ν (RationalPointFamily.rootSet i ν J)) :
        rationalPoints G) =
      standardHalfModulus i ν (RationalPointFamily.rootSet i ν J) (a ^ r) *
        (standardHalfModulus i ν (RationalPointFamily.rootSet i ν J) m *
          standardConstantTerm hA (fun g => coefficientTensorMap Vψ t g) (m * a ^ r)) := by
    exact h
  rw [h', standardHalfModulus_mul]
  ring

end Langlands.HarishChandraSchwartz
