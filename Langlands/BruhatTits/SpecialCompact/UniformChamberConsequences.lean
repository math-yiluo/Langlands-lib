import Langlands.BruhatTits.SpecialCompact.ComponentUniformContraction
import Langlands.GroupScheme.Rational.RelativeRootNegationProof
import Langlands.Representation.Aubert.General.RationalOppositeChamber
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction

/-! # Opposite chambers and the two exact uniform basis clauses -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology Filter Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.BruhatTits.SpecialCompact

section Groups

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- Uniform contraction into open ambient subgroups gives uniform compact
containment in the actual expanding conjugates. -/
theorem uniform_compact_expanding_containment
    (K U : Subgroup H) (CAeps : ℝ → Set H) (σ : H → H)
    (hKo : IsOpen (K : Set H))
    (hnorm : ∀ ε m, m ∈ CAeps ε → ∀ x ∈ U,
      σ m * x * (σ m)⁻¹ ∈ U)
    (hcontract : ∀ C : Set H, IsCompact C → C ⊆ U →
      ∀ W ∈ 𝓝 (1 : H), ∃ ε : ℝ, 0 < ε ∧
        ∀ m ∈ CAeps ε, ∀ x ∈ C, σ m * x * (σ m)⁻¹ ∈ W)
    (Γ : Set U) (hΓ : IsCompact Γ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ CAeps ε,
      U.subtype '' Γ ⊆ ambientConjugate (σ m)⁻¹
        ((K ⊓ U : Subgroup H) : Set H) := by
  have hc : IsCompact (U.subtype '' Γ) := hΓ.image continuous_subtype_val
  have hCU : U.subtype '' Γ ⊆ (U : Set H) := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  obtain ⟨ε, hε, h⟩ := hcontract _ hc hCU K (hKo.mem_nhds K.one_mem)
  refine ⟨ε, hε, ?_⟩
  intro m hm x hx
  refine ⟨σ m * x * (σ m)⁻¹, ⟨h m hm x hx, hnorm ε m hm x (hCU hx)⟩, ?_⟩
  simp only [inv_inv]
  group

/-- Compact-uniform contraction of the literal compact intersection gives
uniform cofinality in every intrinsic open subgroup. -/
theorem uniform_compact_open_cofinality
    (K U : Subgroup H) (CAeps : ℝ → Set H) (σ : H → H)
    (hKc : IsCompact (K : Set H)) (hUc : IsClosed (U : Set H))
    (hnorm : ∀ ε m, m ∈ CAeps ε → ∀ x ∈ U,
      σ m * x * (σ m)⁻¹ ∈ U)
    (hcontract : ∀ C : Set H, IsCompact C → C ⊆ U →
      ∀ W ∈ 𝓝 (1 : H), ∃ ε : ℝ, 0 < ε ∧
        ∀ m ∈ CAeps ε, ∀ x ∈ C, σ m * x * (σ m)⁻¹ ∈ W)
    (Γ : OpenSubgroup U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ m ∈ CAeps ε,
      ambientConjugate (σ m) ((K ⊓ U : Subgroup H) : Set H) ⊆
        U.subtype '' (Γ : Set U) := by
  have hΓ : (Γ : Set U) ∈ 𝓝 (1 : U) := Γ.isOpen.mem_nhds Γ.one_mem
  rw [nhds_subtype_eq_comap] at hΓ
  obtain ⟨V, hV, hVΓ⟩ := mem_comap.mp hΓ
  have hc : IsCompact ((K : Set H) ∩ U) := hKc.inter_right hUc
  obtain ⟨ε, hε, h⟩ := hcontract _ hc inter_subset_right V hV
  refine ⟨ε, hε, ?_⟩
  intro m hm x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨⟨σ m * y * (σ m)⁻¹, hnorm ε m hm y hy.2⟩, ?_, rfl⟩
  exact hVΓ (h m hm y hy)

end Groups

variable {F : Type u} [Field F]
    {S A : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {J : Set (characterLattice S)} {q : A.toGrp ⟶ S.toGrp}

/-- Simultaneous reversal negates the original restricted outside-face
simple characters. -/
theorem standardParabolicComponentCharacters_reversed
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) :
    standardParabolicComponentCharacters i (-ν) (Neg.neg '' J) q =
      Neg.neg '' standardParabolicComponentCharacters i ν J q := by
  ext β
  constructor
  · rintro ⟨α, ⟨hα, hαJ⟩, rfl⟩
    refine ⟨componentCharacterRestriction q (-α), ?_, ?_⟩
    · refine ⟨-α, ⟨?_, ?_⟩, rfl⟩
      · simpa only [neg_neg] using neg_mem_simpleRelativeRoots i (-ν) hneg hα
      · intro h
        exact hαJ ⟨-α, h, neg_neg α⟩
    · simp only [map_neg, neg_neg]
  · rintro ⟨_, ⟨α, ⟨hα, hαJ⟩, rfl⟩, rfl⟩
    refine ⟨-α, ⟨neg_mem_simpleRelativeRoots i ν hneg hα, ?_⟩, ?_⟩
    · rintro ⟨b, hb, heq⟩
      exact hαJ (neg_injective heq ▸ hb)
    · exact map_neg (componentCharacterRestriction q) α

/-- The same actual split component represents the same Levi after chamber
and face reversal. -/
theorem IsCompatibleStandardSplitComponent.reversed
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν) :
    IsCompatibleStandardSplitComponent i (-ν) (Neg.neg '' J) A q := by
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG S i hi ν hν J hJ).1
  have hrev := standardSubgroups_reversedChamber i ν standardCocharacter hG hi hν
    (relativeRootNegation F G hG S i hi) hζ
  obtain ⟨hq, M, j, a, hj, hjc, hM, ha, hcomp⟩ := hA
  exact ⟨hq, M, j, a, hrev.2.1 ▸ hj, hjc, hM, ha, hcomp⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- Negating the character and inverting the actual point cancel in its
normalized character norm. -/
theorem componentCharacterNorm_neg_inv (α : characterLattice A)
    (t : rationalPoints A.toGrp) :
    CocharacterUniformizer.characterNorm F A (-α) t⁻¹ =
      CocharacterUniformizer.characterNorm F A α t := by
  simp [CocharacterUniformizer.characterNorm, map_neg]

/-- Inversion sends the original epsilon chamber into the reversed one,
with exactly the same epsilon. -/
theorem inv_mem_standardComponentCAepsilon_reversed
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    {ε : ℝ} {m : rationalPoints G}
    (hm : m ∈ standardComponentCAepsilon i ν J q ε) :
    m⁻¹ ∈ standardComponentCAepsilon i (-ν) (Neg.neg '' J) q ε := by
  obtain ⟨t, ht, rfl⟩ := hm
  refine ⟨t⁻¹, ⟨(CocharacterUniformizer.CA F A).inv_mem ht.1, ?_⟩, ?_⟩
  · intro β hβ
    rw [standardParabolicComponentCharacters_reversed i ν hneg] at hβ
    obtain ⟨α, hα, rfl⟩ := hβ
    rw [componentCharacterNorm_neg_inv]
    exact ht.2 α hα
  · exact map_inv (rationalPoints.map (q ≫ i)) t

/-- The actual inverse-point map between the original epsilon chamber and
its reversed chamber. -/
def oppositeEpsilonChamberMap
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i) (ε : ℝ) :
    {m : rationalPoints G // m ∈ standardComponentCAepsilon i ν J q ε} →
      {m : rationalPoints G //
        m ∈ standardComponentCAepsilon i (-ν) (Neg.neg '' J) q ε} :=
  fun m => ⟨m.1⁻¹, inv_mem_standardComponentCAepsilon_reversed i ν hneg m.2⟩

local instance uniformChamberConsequencesAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance uniformChamberConsequencesTopology :
    TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X

/-- All epsilon-chamber points normalize the entire literal radical. -/
theorem IsCompatibleStandardSplitComponent.epsilon_conj_mem
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (ε : ℝ) {m : rationalPoints G}
    (hm : m ∈ standardComponentCAepsilon i ν J q ε)
    {x : rationalPoints G} (hx : x ∈ standardUnipotentPoints i ν J) :
    m * x * m⁻¹ ∈ standardUnipotentPoints i ν J := by
  obtain ⟨t, _, rfl⟩ := hm
  exact StandardLeviIntersection.conj_mem_standardUnipotent i ν
    (standardLevi_le_standardParabolic i ν J _
      (hA.map_mem_standardLeviPoints i ν t)) hx

/-- The same epsilon chamber contracts compact subsets of the original
opposite radical by inverse conjugation. -/
theorem IsCompatibleStandardSplitComponent.uniform_opposite_contraction
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (C : Set (rationalPoints G)) (hC : IsCompact C)
    (hCU : C ⊆ standardOppositeUnipotentPoints i ν J)
    (W : Set (rationalPoints G)) (hW : W ∈ 𝓝 (1 : rationalPoints G)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ m ∈ standardComponentCAepsilon i ν J q ε,
        ∀ x ∈ C, m⁻¹ * x * m ∈ W := by
  have hneg := relativeRootNegation F G hG S i hi
  have hAr := hA.reversed i ν hG hi hν hJ
  have hJr : Neg.neg '' J ⊆ simpleRelativeRoots i (-ν) := by
    rintro _ ⟨α, hα, rfl⟩
    exact neg_mem_simpleRelativeRoots i ν hneg (hJ hα)
  obtain ⟨ε, hε, h⟩ := hAr.uniform_contraction i (-ν) hG hi (hν.neg i ν)
    hJr C hC hCU W hW
  refine ⟨ε, hε, fun m hm x hx => ?_⟩
  simpa only [inv_inv] using h m⁻¹
    (inv_mem_standardComponentCAepsilon_reversed i ν hneg hm) x hx

/-- Both precise uniform clauses hold at every compact open subgroup, with
the original component and the two original literal radicals. -/
theorem IsCompatibleStandardSplitComponent.uniform_containment_and_cofinality
    (hA : IsCompatibleStandardSplitComponent i ν J A q)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hJ : J ⊆ simpleRelativeRoots i ν)
    (K : Subgroup (rationalPoints G))
    (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G))) :
    UniformCompactContainment K (standardUnipotentPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) (standardComponentCAepsilon i ν J q) ∧
    UniformCompactOpenCofinality K (standardUnipotentPoints i ν J)
      (standardOppositeUnipotentPoints i ν J) (standardComponentCAepsilon i ν J q) := by
  let : T2Space F := Langlands.BruhatTits.localField_t2Space F
  have hneg := relativeRootNegation F G hG S i hi
  have hAr := hA.reversed i ν hG hi hν hJ
  have hn : ∀ ε m, m ∈ standardComponentCAepsilon i ν J q ε →
      ∀ x ∈ standardUnipotentPoints i ν J,
        m * x * m⁻¹ ∈ standardUnipotentPoints i ν J :=
    fun ε _ hm _ hx => hA.epsilon_conj_mem i ν ε hm hx
  have ho : ∀ ε m, m ∈ standardComponentCAepsilon i ν J q ε →
      ∀ x ∈ standardOppositeUnipotentPoints i ν J,
        m⁻¹ * x * m ∈ standardOppositeUnipotentPoints i ν J := by
    intro ε m hm x hx
    simpa only [inv_inv] using hAr.epsilon_conj_mem i (-ν) ε
      (inv_mem_standardComponentCAepsilon_reversed i ν hneg hm) hx
  have hnc : IsClosed (standardUnipotentPoints i ν J : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F _ (Standard.unipotentHom i ν J)
      (Standard.isRepresentedBy_unipotentHom i ν J)
      (Standard.isClosedSubgroup_unipotentHom i ν J)
  have hoc : IsClosed (standardOppositeUnipotentPoints i ν J : Set (rationalPoints G)) :=
    isClosed_rationalPoint_subgroup F _ (Standard.unipotentHom i (-ν) (Neg.neg '' J))
      (Standard.isRepresentedBy_unipotentHom i (-ν) (Neg.neg '' J))
      (Standard.isClosedSubgroup_unipotentHom i (-ν) (Neg.neg '' J))
  have hcN := hA.uniform_contraction i ν hG hi hν hJ
  have hcO := hA.uniform_opposite_contraction i ν hG hi hν hJ
  constructor
  · constructor
    · exact uniform_compact_expanding_containment K (standardUnipotentPoints i ν J)
        (standardComponentCAepsilon i ν J q) id hKo hn hcN
    · simpa only [inv_inv] using
        uniform_compact_expanding_containment K (standardOppositeUnipotentPoints i ν J)
          (standardComponentCAepsilon i ν J q) Inv.inv hKo
          (by simpa only [inv_inv] using ho) (by simpa only [inv_inv] using hcO)
  · constructor
    · intro Γ _
      exact uniform_compact_open_cofinality K (standardUnipotentPoints i ν J)
        (standardComponentCAepsilon i ν J q) id hKc hnc hn hcN Γ
    · intro Γ _
      exact uniform_compact_open_cofinality K (standardOppositeUnipotentPoints i ν J)
        (standardComponentCAepsilon i ν J q) Inv.inv hKc hoc
        (by simpa only [inv_inv] using ho) (by simpa only [inv_inv] using hcO) Γ

end Langlands.BruhatTits.SpecialCompact
