import Langlands.Representation.Exponents.GeneralizedJacquetRemarksStatements
import Langlands.Representation.Exponents.SplitComponentOppositeContractionStatement
import Langlands.Representation.Exponents.LeviJacquetOppositePairingStructure
import Langlands.Representation.Jacquet.DominatedIwahoriContraction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof

/-! # Renard VI.9.1, Remark 3, from uniform stabilization and two-sided contraction

Renard 2026, VI.9.1, Remarque 3 and its proof (printed p.198 / PDF p.204). The published
`GeneralizedJacquetContractingRangeStatement` follows from the Proposition of VI.9.1
(`UniformCompressionStabilizationStatement`) and the two-sided contraction of compact
subsets of `N(F)` and `N̄(F)` by `A^+(ε)` (`SplitComponentOppositeContractionStatement`,
Renard V.5.2 (iii)). Neither antecedent is asserted here.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.9.1, Remark 3, as an implication: the uniform stabilization Proposition of
VI.9.1 and the two-sided contraction of compact subsets of `N(F)` and `N̄(F)` by
`A^+(ε)` (Renard V.5.2 (iii)) imply `GeneralizedJacquetContractingRangeStatement`. This
proposition records the internal reduction; neither antecedent is asserted. -/
def GeneralizedJacquetContractingRangeReductionStatement : Prop :=
  RationalPointFamily.UniformCompressionStabilizationStatement.{u, v} →
    SplitComponentOppositeContractionStatement.{u} →
      GeneralizedJacquetContractingRangeStatement.{u, v}

/-- `GeneralizedJacquetContractingRangeStatement` (Renard VI.9.1, Remark 3) follows from the
uniform stabilization Proposition of VI.9.1 and the two-sided contraction statement
`SplitComponentOppositeContractionStatement` (Renard V.5.2 (iii)). -/
theorem generalizedJacquetContractingRange_of_uniformStabilization :
    GeneralizedJacquetContractingRangeReductionStatement.{u, v} := by
  intro hstab hGeo k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar hmbar hnbar hmulbar hP hPP
    K hK t₀ hcent₀ ht₀ A a pres Δ incG
  -- The cocharacter of `P` and the dynamic descriptions of `N`, `M` and `N̄`.
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hp hm
  have hN := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ hp hPχ hn
  have hM : pointImage (m ≫ p) = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hMχ]
  have hNbar := pointImage_opposite_radical_eq_dynamic parabolicDynamic
    oppositeDynamicParabolicUniqueness hG χ m hPχ hMχ hpbar hmbar hnbar hP hPP
  have hMN := pointImage_le_normalizer p m n hn
  have hMNbar : pointImage (m ≫ p) ≤
      Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G)) := by
    rw [← hP]
    exact pointImage_le_normalizer pbar mbar nbar hnbar
  have hNc := isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup
  have hNbarc := isClosed_pointImage_comp pbar nbar hpbar.isClosedSubgroup hnbar.1.isClosedSubgroup
  -- The Proposition of VI.9.1 in the actual parabolic.
  have hstab' : ∀ g : rationalPoints G, (∀ x ∈ pointImage (m ≫ p), x * g = g * x) →
      Jacquet.IsIwahoriContraction K (pointImage (n ≫ p)) (pointImage (m ≫ p))
        (pointImage (nbar ≫ pbar)) g →
      ∃ b : ℕ, ∀ (V : Type v) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ (rationalPoints G) V) (hρ : IsSmooth ρ),
        (∀ s : ℕ, b ≤ s →
          Jacquet.stableImage ρ hρ K hK g =
              LinearMap.range (Jacquet.compressedAction ρ hρ K hK g ^ s) ∧
            Jacquet.powerKernelSup ρ hρ K hK g =
              LinearMap.ker (Jacquet.compressedAction ρ hρ K hK g ^ s)) ∧
          Jacquet.CompactCompressionSplits ρ hρ K hK g := by
    intro g hg hgc
    rw [hM] at hg
    rw [hN, hM, hNbar] at hgc
    exact hstab k G hG χ K hK g hg hgc
  obtain ⟨b₀, hb₀⟩ := hstab' t₀ hcent₀ ht₀
  set b : ℕ := max b₀ 1 with hbdef
  have hb : 1 ≤ b := le_max_right _ _
  -- The compact sets `t₀^{-b} (K ∩ N) t₀^b ⊆ N(F)` and `t₀^b (K ∩ N̄) t₀^{-b} ⊆ N̄(F)`.
  have ht₀M : t₀ ^ b ∈ pointImage (m ≫ p) := Subgroup.pow_mem _ ht₀.mem_levi b
  let C : Set (rationalPoints G) :=
    (fun x => (t₀ ^ b)⁻¹ * x * t₀ ^ b) '' ((K : Set (rationalPoints G)) ∩ pointImage (n ≫ p))
  let Cbar : Set (rationalPoints G) :=
    (fun x => t₀ ^ b * x * (t₀ ^ b)⁻¹) ''
      ((K : Set (rationalPoints G)) ∩ pointImage (nbar ≫ pbar))
  have hC : IsCompact C :=
    (hK.inter_right hNc).image ((continuous_const.mul continuous_id).mul continuous_const)
  have hCbar : IsCompact Cbar :=
    (hK.inter_right hNbarc).image ((continuous_const.mul continuous_id).mul continuous_const)
  have hCN : C ⊆ pointImage (n ≫ p) := by
    rintro _ ⟨x, hx, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hMN (Subgroup.inv_mem _ ht₀M)) x).mp hx.2
    simpa using this
  have hCbarN : Cbar ⊆ pointImage (nbar ≫ pbar) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMNbar ht₀M) x).mp hx.2
  obtain ⟨ε, hε, hεC⟩ := hGeo k G hG P Pbar M N Nbar p m n hp hm hn hmul pbar mbar nbar hpbar
    hmbar hnbar hmulbar hP hPP A a pres C hC hCN Cbar hCbar hCbarN
    (K : Set (rationalPoints G)) (K.isOpen.mem_nhds K.one_mem)
  refine ⟨ε, hε, fun t ht V _ _ ρ hρ => ?_⟩
  obtain ⟨hupC, hlowC⟩ := hεC t ht
  -- `g = t` lies in `M(F)` and is central there.
  have hincG : incG t = rationalPoints.map (m ≫ p) (rationalPoints.map a t) := by
    simp only [incG, rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have hg : incG t ∈ pointImage (m ≫ p) := ⟨rationalPoints.map a t, hincG.symm⟩
  have hcent : ∀ x ∈ pointImage (m ≫ p), x * incG t = incG t * x := by
    intro x hx
    rw [hincG]
    exact (splitComponent_point_comm pres t x hx).symm
  have hup : ∀ u ∈ K.toSubgroup ⊓ pointImage (n ≫ p),
      incG t * ((t₀ ^ b)⁻¹ * u * t₀ ^ b) * (incG t)⁻¹ ∈ K :=
    fun u hu => hupC _ ⟨u, ⟨hu.1, hu.2⟩, rfl⟩
  have hlow : ∀ l ∈ K.toSubgroup ⊓ pointImage (nbar ≫ pbar),
      (incG t)⁻¹ * (t₀ ^ b * l * (t₀ ^ b)⁻¹) * incG t ∈ K :=
    fun l hl => hlowC _ ⟨l, ⟨hl.1, hl.2⟩, rfl⟩
  -- `g` is an `M`-central Iwahori contraction, so the Proposition applies to it too.
  have hgc := ht₀.of_dominates hMN hMNbar hb hg hcent hup hlow
  obtain ⟨b₁, hb₁⟩ := hstab' (incG t) hcent hgc
  obtain ⟨hst₀, hsplit₀⟩ := hb₀ V ρ hρ
  obtain ⟨hrange, hker⟩ := hst₀ b (le_max_left _ _)
  exact Jacquet.ker_range_compressedAction_of_dominates ρ hρ hK ht₀ hcent₀ hMN hMNbar hb hg
    hcent hup hlow hker hrange hsplit₀ (hb₁ V ρ hρ).2

end Langlands.Aubert.General.RepresentedParabolic
