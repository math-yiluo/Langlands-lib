import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviScheme
import Langlands.GroupScheme.Rational.MinimalParabolicDistanceLengthProof
import Langlands.GroupScheme.Rational.MinimalStandardDynamicComparison

/-! # Changing the minimal parabolic while keeping the Iwasawa compact -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

open Langlands.GroupScheme.MinimalParabolicDistanceLength

namespace Langlands.HarishChandraSchwartz

section Generic

variable {H : Type*} [Group H] {P Q K : Subgroup H}

/-- An Iwasawa compact contains a conjugator for every conjugate of its
parabolic. This is an algebraic consequence of `H = P K = K P`. -/
theorem IsIwasawaPair.exists_mem_conjugator (hPK : IsIwasawaPair P K)
    (hPQ : ∃ n : H, ∀ x : H, x ∈ P ↔ n * x * n⁻¹ ∈ Q) :
    ∃ k ∈ K, ∀ x : H, x ∈ P ↔ k * x * k⁻¹ ∈ Q := by
  obtain ⟨n, hn⟩ := hPQ
  obtain ⟨p, hp, k, hk, hnpk⟩ := hPK n⁻¹
  have hnp : n = k⁻¹ * p⁻¹ := by
    calc n = (n⁻¹)⁻¹ := (inv_inv n).symm
      _ = (p * k)⁻¹ := congrArg Inv.inv hnpk
      _ = k⁻¹ * p⁻¹ := by group
  refine ⟨k⁻¹, K.inv_mem hk, fun x => ?_⟩
  have hx : k⁻¹ * x * (k⁻¹)⁻¹ = n * (p * x * p⁻¹) * n⁻¹ := by
    rw [hnp]
    group
  rw [hx, ← hn]
  constructor
  · intro hxP
    exact P.mul_mem (P.mul_mem hp hxP) (P.inv_mem hp)
  · intro hxP
    have heq : x = p⁻¹ * (p * x * p⁻¹) * p := by group
    rw [heq]
    exact P.mul_mem (P.mul_mem (P.inv_mem hp) hxP) hp

/-- Conjugating the parabolic by an element of the compact factor retains
that exact compact factor in the Iwasawa decomposition. -/
theorem IsIwasawaPair.of_mem_conjugator (hPK : IsIwasawaPair P K)
    {k : H} (hk : k ∈ K) (hPQ : ∀ x : H, x ∈ P ↔ k * x * k⁻¹ ∈ Q) :
    IsIwasawaPair Q K := by
  intro g
  obtain ⟨p, hp, l, hl, hg⟩ := hPK (k⁻¹ * g * k)
  refine ⟨k * p * k⁻¹, (hPQ p).mp hp, k * l * k⁻¹,
    K.mul_mem (K.mul_mem hk hl) (K.inv_mem hk), ?_⟩
  calc g = k * (k⁻¹ * g * k) * k⁻¹ := by group
    _ = k * (p * l) * k⁻¹ := by rw [hg]
    _ = (k * p * k⁻¹) * (k * l * k⁻¹) := by group

variable [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace P] [LocallyCompactSpace Q] [CompactSpace K]

/-- With the modular character as inducing character, conjugate parabolics
with the same compact Iwasawa factor have exactly the same spherical function. -/
theorem xi_eq_of_mem_conjugator {hPK : IsIwasawaPair P K} {hQK : IsIwasawaPair Q K}
    {δP : P →* ℝ≥0ˣ} {δQ : Q →* ℝ≥0ˣ}
    (hδP : ∀ p : P, (δP p : ℝ≥0) = Measure.modularCharacter p)
    (hδQ : ∀ q : Q, (δQ q : ℝ≥0) = Measure.modularCharacter q)
    (hδK : ∀ q : Q, (q : H) ∈ K → δQ q = 1)
    {k : H} (hk : k ∈ K) (hPQ : ∀ x : H, x ∈ P ↔ k * x * k⁻¹ ∈ Q)
    (g : H) : xi hQK δQ g = xi hPK δP g := by
  let e : H ≃ₜ* H :=
    { toMulEquiv := MulAut.conj k
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
      continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }
  have hK : ∀ x : H, x ∈ K ↔ e x ∈ K := by
    intro x
    change x ∈ K ↔ k * x * k⁻¹ ∈ K
    constructor
    · exact fun hx => K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
    · intro hx
      have heq : x = k⁻¹ * (k * x * k⁻¹) * k := by group
      rw [heq]
      exact K.mul_mem (K.mul_mem (K.inv_mem hk) hx) hk
  have hP : ∀ x : H, x ∈ P ↔ e x ∈ Q := hPQ
  let eP := subgroupContinuousMulEquiv e hP
  have hchar : ∀ p : P, δQ ⟨e p, (hP p).mp p.2⟩ = δP p := by
    intro p
    apply Units.ext
    calc (δQ ⟨e p, (hP p).mp p.2⟩ : ℝ≥0)
        = Measure.modularCharacter (eP p) := hδQ _
      _ = Measure.modularCharacter p :=
        Aubert.General.modularCharacter_continuousMulEquiv eP p
      _ = (δP p : ℝ≥0) := (hδP p).symm
  have hmap := xi_map (hPK := hPK) (hPK' := hQK) e hδK (fun x hx => (hP x).mp hx) hK hchar g
  change xi hQK δQ (k * g * k⁻¹) = xi hPK δP g at hmap
  rwa [xi_mul_mul hδK hk (K.inv_mem hk)] at hmap

end Generic

section Actual

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν ξ : cocharacterLattice S}

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- Any two minimal standard parabolics of the same maximal split torus
are conjugate by an element of any supplied Iwasawa compact. -/
theorem exists_mem_iwasawaCompact_conjugating_minimal (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hξ : IsGenericCocharacter i ξ) {K : Subgroup (rationalPoints G)}
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) :
    ∃ k ∈ K, ∀ x : rationalPoints G, x ∈ standardParabolicPoints i ν ∅ ↔
      k * x * k⁻¹ ∈ standardParabolicPoints i ξ ∅ := by
  have := hi.isSplitSubtorus.mono
  apply hPK.exists_mem_conjugator
  obtain ⟨n, hn, -⟩ := MinimalParabolicDistanceLength.exists_map_conj_eq i hG hi hν hξ
  have hP : standardParabolicPoints i ν ∅ = parabolicPoints i ν := by
    unfold standardParabolicPoints parabolicPoints
    rw [standardParabolic_empty_eq_dynamic_of_generic i ν hG hi hν]
  have hQ : standardParabolicPoints i ξ ∅ = parabolicPoints i ξ := by
    unfold standardParabolicPoints parabolicPoints
    rw [standardParabolic_empty_eq_dynamic_of_generic i ξ hG hi hξ]
  refine ⟨(n : rationalPoints G), fun x => ?_⟩
  rw [hP, hQ, ← hn, MinimalParabolicDistanceLength.mem_map_conj]
  simp [mul_assoc]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The exact Iwasawa compact works for every generic chamber of the same
torus; no structural basis or covering is needed for this change. -/
theorem IsIwasawaPair.rationalChangeMinimal (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hξ : IsGenericCocharacter i ξ) {K : Subgroup (rationalPoints G)}
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K) :
    IsIwasawaPair (standardParabolicPoints i ξ ∅) K := by
  obtain ⟨k, hk, hconj⟩ := exists_mem_iwasawaCompact_conjugating_minimal hG hi hν hξ hPK
  exact hPK.of_mem_conjugator hk hconj

/-- The actual spherical function is independent of the chosen generic
minimal parabolic for a fixed compact Iwasawa factor. -/
theorem rationalXi_changeMinimal (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hξ : IsGenericCocharacter i ξ) {K : Subgroup (rationalPoints G)}
    (hKo : IsOpen (K : Set (rationalPoints G)))
    (hKc : IsCompact (K : Set (rationalPoints G)))
    (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K)
    (hQK : IsIwasawaPair (standardParabolicPoints i ξ ∅) K) (g : rationalPoints G) :
    rationalXi hKc hQK g = rationalXi hKc hPK g := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have : LocallyCompactSpace (standardParabolicPoints i ν ∅) :=
    (isClosed_standardParabolicPoints_empty hG hi hν).locallyCompactSpace
  have : LocallyCompactSpace (standardParabolicPoints i ξ ∅) :=
    (isClosed_standardParabolicPoints_empty hG hi hξ).locallyCompactSpace
  obtain ⟨k, hk, hconj⟩ := exists_mem_iwasawaCompact_conjugating_minimal hG hi hν hξ hPK
  exact xi_eq_of_mem_conjugator
    (rationalMinimalModulus_eq_modularCharacter hG hi hν)
    (rationalMinimalModulus_eq_modularCharacter hG hi hξ)
    (fun p hp => rationalMinimalModulus_eq_one i ξ hKo hKc p hp) hk hconj g

end Actual

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- A fixed compact Iwasawa factor defines the same actual spherical function
for every generic minimal chamber of the given maximal split torus. -/
def RationalXiChangeMinimalStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ (ν ξ : cocharacterLattice S), IsGenericCocharacter i ν → IsGenericCocharacter i ξ →
    ∀ K : Subgroup (rationalPoints G), IsOpen (K : Set (rationalPoints G)) →
    ∀ (hKc : IsCompact (K : Set (rationalPoints G)))
      (hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K),
    ∃ hQK : IsIwasawaPair (standardParabolicPoints i ξ ∅) K,
      ∀ g : rationalPoints G, rationalXi hKc hQK g = rationalXi hKc hPK g

/-- Exact change of minimal parabolic for the actual spherical function. -/
theorem rationalXiChangeMinimal : RationalXiChangeMinimalStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν ξ hν hξ K hKo hKc hPK
  refine ⟨IsIwasawaPair.rationalChangeMinimal hG hi hν hξ hPK, ?_⟩
  exact rationalXi_changeMinimal hG hi hν hξ hKo hKc hPK _

end Langlands.HarishChandraSchwartz
