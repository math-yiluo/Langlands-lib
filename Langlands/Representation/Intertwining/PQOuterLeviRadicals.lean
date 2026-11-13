import Langlands.Representation.Exponents.LeviJacquetContragredientStructure
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Dynamic.CommutingRefinements
import Langlands.GroupScheme.Dynamic.NormalizedLimits
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.NestedParabolicPointDecompositionProof

/-! # Radicals of parabolics through an intermediate Levi (Renard VII.3.5 (iii))

For represented parabolics `P₁ = MN₁ ⊂ Q₁ = LU₁`, `P₂ = MN₂ ⊂ Q₂ = LU₂` with a common
parabolic `P' = P₁ ∩ L = P₂ ∩ L` of `L`, and opposites `P̄₁ = MN̄₁`, `Q̄₁ = LŪ₁`, the
rational points satisfy `N̄₁(F) ∩ N₂(F) = Ū₁(F) ∩ U₂(F)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Radicals

variable {k : Type u} [Field k]

/-- The range of a composite lies in the range of its second factor. -/
private theorem range_comp_le' {S : Scheme.{u}} {H K G : GroupScheme S} (f : H ⟶ K) (g : K ⟶ G) :
    SubgroupFunctor.range (f ≫ g) ≤ SubgroupFunctor.range g := by
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, by simp⟩

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]

/-- Renard VII.3.5 (iii), first step: `N̄₁(F) ∩ N₂(F) = Ū₁(F) ∩ U₂(F)`. -/
theorem outerRadical_inf_eq
    {G M P₁ P₂ N₂ Pb₁ Nb₁ L Q₁ Q₂ U₂ Qb₁ Ub₁ P' N' : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    {p₁ : P₁ ⟶ G} {l₁ : M ⟶ P₁} (hp₁ : IsParabolicSubgroup p₁)
    (hl₁ : IsRationalLeviSubgroup l₁)
    {p₂ : P₂ ⟶ G} {l₂ : M ⟶ P₂} {r₂ : N₂ ⟶ P₂} (hp₂ : IsParabolicSubgroup p₂)
    (hl₂ : IsRationalLeviSubgroup l₂) (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
    (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
    {pb₁ : Pb₁ ⟶ G} {lb₁ : M ⟶ Pb₁} {rb₁ : Nb₁ ⟶ Pb₁} (hpb₁ : IsParabolicSubgroup pb₁)
    (hlb₁ : IsRationalLeviSubgroup lb₁) (hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
    {q₁ : Q₁ ⟶ G} {lQ₁ : L ⟶ Q₁} (hq₁ : IsParabolicSubgroup q₁)
    (hlQ₁ : IsRationalLeviSubgroup lQ₁)
    {q₂ : Q₂ ⟶ G} {lQ₂ : L ⟶ Q₂} {rQ₂ : U₂ ⟶ Q₂} (hq₂ : IsParabolicSubgroup q₂)
    (hlQ₂ : IsRationalLeviSubgroup lQ₂) (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
    (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂))
    {qb₁ : Qb₁ ⟶ G} {lqb₁ : L ⟶ Qb₁} {rqb₁ : Ub₁ ⟶ Qb₁} (hqb₁ : IsParabolicSubgroup qb₁)
    (hlqb₁ : IsRationalLeviSubgroup lqb₁) (hrqb₁ : LeviSubgroup.IsGeometricUnipotentRadical rqb₁)
    {p' : P' ⟶ L} {l' : M ⟶ P'} {r' : N' ⟶ P'} (hp' : IsParabolicSubgroup p')
    (hl' : IsRationalLeviSubgroup l') (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
    (hmul' : IsIso (subgroupMultiplication l' r'))
    (hlev₂ : l₂ ≫ p₂ = l₁ ≫ p₁) (hlevb : lb₁ ≫ pb₁ = l₁ ≫ p₁)
    (hopp : pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁))
    (hlevQ₂ : lQ₂ ≫ q₂ = lQ₁ ≫ q₁) (hlevQb : lqb₁ ≫ qb₁ = lQ₁ ≫ q₁)
    (hoppQ : pointImage q₁ ⊓ pointImage qb₁ = pointImage (lQ₁ ≫ q₁))
    (hPQ₁ : pointImage p₁ ≤ pointImage q₁) (hPQ₂ : pointImage p₂ ≤ pointImage q₂)
    (hM : l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁)
    (hP'₁ : pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₁ ⊓ pointImage (lQ₁ ≫ q₁))
    (hP'₂ : pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₂ ⊓ pointImage (lQ₁ ≫ q₁)) :
    pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₂ ≫ p₂) =
      pointImage (rqb₁ ≫ qb₁) ⊓ pointImage (rQ₂ ≫ q₂) := by
  have := hG.isAffineHom
  have := hG.smooth
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  -- cocharacters realizing `P₁ ⊃ M`, `Q₁ ⊃ L` and `Q₂ ⊃ L`
  obtain ⟨χ, hPχ, hMχ⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
    dynamicGeometricUnipotentRadical hG hp₁ hl₁
  obtain ⟨ξ, hPξ, hLξ⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
    dynamicGeometricUnipotentRadical hG hq₁ hlQ₁
  obtain ⟨ψ, hPψ, hLψ⟩ := DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
    dynamicGeometricUnipotentRadical hG hq₂ hlQ₂
  have hNb := pointImage_opposite_radical_eq_dynamic parabolicDynamic
    oppositeDynamicParabolicUniqueness hG χ l₁ hPχ hMχ hpb₁ hlb₁ hrb₁ hlevb hopp
  have hUb := pointImage_opposite_radical_eq_dynamic parabolicDynamic
    oppositeDynamicParabolicUniqueness hG ξ lQ₁ hPξ hLξ hqb₁ hlqb₁ hrqb₁ hlevQb hoppQ
  have hU₂ := pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG ψ hq₂ hPψ hrQ₂
  -- the centralizers
  have hLψξ : Dynamic.centralizer ψ = Dynamic.centralizer ξ := by
    rw [← hLψ, ← hLξ, hlevQ₂]
  have hMle : Dynamic.centralizer χ ≤ Dynamic.centralizer ξ := by
    rw [← hMχ, ← hLξ, ← hM]
    have h := range_comp_le' (l' ≫ p') (lQ₁ ≫ q₁)
    rwa [Category.assoc] at h
  -- `U₂(F) ⊂ N₂(F)` from the nested decomposition of `P₂ ⊂ Q₂`
  have hU₂N₂ : pointImage (rQ₂ ≫ q₂) ≤ pointImage (r₂ ≫ p₂) := by
    have hnest := nestedParabolicPointDecomposition k G hG P₂ M N₂ Q₂ L U₂ P' N'
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ p' l' r' hp' hl' hr' hmul'
      hPQ₂ (by rw [hlevQ₂, hM, hlev₂]) (by rw [hlevQ₂]; exact hP'₂.trans (inf_comm _ _))
    intro x hx
    have hx' : x ∈ ((pointImage (r₂ ≫ p₂) : Set (rationalPoints G))) := by
      rw [hnest.2.1]
      exact ⟨1, (Subgroup.one_mem _), x, hx, one_mul x⟩
    exact hx'
  -- notation for the identity test
  set pt : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k))) with hpt
  have hP₁pt : pointImage p₁ = (Dynamic.parabolic χ).carrier pt := by
    rw [pointImage_eq_range_carrier, hPχ]
  have hQ₁pt : pointImage q₁ = (Dynamic.parabolic ξ).carrier pt := by
    rw [pointImage_eq_range_carrier, hPξ]
  have hQ₂pt : pointImage q₂ = (Dynamic.parabolic ψ).carrier pt := by
    rw [pointImage_eq_range_carrier, hPψ]
  have hLpt : pointImage (lQ₁ ≫ q₁) = (Dynamic.centralizer ξ).carrier pt := by
    rw [pointImage_eq_range_carrier, hLξ]
  -- the opposite cocharacters
  set χb := Dynamic.oppositeCocharacter χ with hχb
  set ξb := Dynamic.oppositeCocharacter ξ with hξb
  have hinvχ : Dynamic.inverseCocharacter χ = χb := rfl
  have hinvξ : Dynamic.inverseCocharacter ξ = ξb := rfl
  rw [hinvχ] at hNb
  rw [hinvξ] at hUb
  have hZχb : Dynamic.centralizer χb = Dynamic.centralizer χ :=
    Dynamic.centralizer_oppositeCocharacter χ
  have hZξb : Dynamic.centralizer ξb = Dynamic.centralizer ξ :=
    Dynamic.centralizer_oppositeCocharacter ξ
  have hτ : SubgroupFunctor.range χb ≤ Dynamic.centralizer ξb := by
    rw [hZξb]
    exact (Dynamic.range_le_centralizer χb).trans (hZχb.le.trans hMle)
  have : LocallyOfFiniteType G.X.hom := inferInstance
  have : IsSeparated G.X.hom := inferInstance
  obtain ⟨θ, hθP, hθZ, hθU, hθUmul, hθPmul⟩ := Dynamic.exists_commuting_refinement ξb χb hτ
  have hZθ : Dynamic.centralizer θ = Dynamic.centralizer χ := by
    rw [hθZ, hZξb, hZχb]
    apply le_antisymm
    · intro X g hg
      exact hg.2
    · intro X g hg
      exact ⟨hMle X hg, hg⟩
  have hrat : (Dynamic.parabolic χ).carrier pt ⊓ (Dynamic.parabolic θ).carrier pt =
      (Dynamic.centralizer χ).carrier pt := by
    apply le_antisymm
    · rintro g ⟨hgχ, hgθ⟩
      have hgθ' : g ∈ ((↑((Dynamic.parabolic θ).carrier pt) : Set (pt ⟶ G.X))) := hgθ
      rw [hθPmul pt] at hgθ'
      obtain ⟨a, ⟨haZ, haP⟩, b, hb, rfl⟩ := hgθ'
      have haξ : a ∈ (Dynamic.parabolic ξ).carrier pt := by
        apply Dynamic.centralizer_le_parabolic ξ pt
        rw [← hZξb]
        exact haZ
      have hgξ : a * b ∈ (Dynamic.parabolic ξ).carrier pt := by
        have h1 : a * b ∈ pointImage p₁ := by rw [hP₁pt]; exact hgχ
        have h2 := hPQ₁ h1
        rw [hQ₁pt] at h2
        exact h2
      have hbξ : b ∈ (Dynamic.parabolic ξ).carrier pt := by
        have := mul_mem (inv_mem haξ) hgξ
        rwa [inv_mul_cancel_left] at this
      have hb1 : b = 1 := Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic ξ hb hbξ
      subst hb1
      have hgχ' : a ∈ (Dynamic.parabolic χ).carrier pt := by simpa using hgχ
      show a * 1 ∈ _
      rw [mul_one, ← Dynamic.parabolic_inf_opposite_eq_centralizer χ]
      exact ⟨hgχ', haP⟩
    · intro g hg
      refine ⟨Dynamic.centralizer_le_parabolic χ pt hg, ?_⟩
      apply Dynamic.centralizer_le_parabolic θ pt
      rw [hZθ]
      exact hg
  obtain ⟨-, hUθ⟩ := oppositeDynamicParabolicUniqueness k G hG χ θ hZθ hrat
  have hLψpt : pointImage (lQ₁ ≫ q₁) = (Dynamic.centralizer ψ).carrier pt := by
    rw [hLpt, hLψξ]
  have hU₂ψ : Dynamic.unipotent ξb ⊓ Dynamic.parabolic ψ =
      Dynamic.unipotent ξb ⊓ Dynamic.unipotent ψ :=
    Dynamic.unipotent_inf_parabolic_eq_unipotent_inf_unipotent ξb ψ (by rw [hLψξ, hZξb])
  rw [hNb, hUb, hU₂]
  apply le_antisymm
  · rintro x ⟨hxV, hxN₂⟩
    have hxθ : x ∈ ((↑((Dynamic.unipotent θ).carrier pt) : Set (pt ⟶ G.X))) := by
      rw [hUθ]; exact hxV
    rw [hθUmul pt] at hxθ
    obtain ⟨y, ⟨hyZ, hyU⟩, u, hu, rfl⟩ := hxθ
    have hyψ : y ∈ (Dynamic.parabolic ψ).carrier pt := by
      apply Dynamic.centralizer_le_parabolic ψ pt
      rw [hLψξ, ← hZξb]
      exact hyZ
    have hxψ : y * u ∈ (Dynamic.parabolic ψ).carrier pt := by
      have h1 : y * u ∈ pointImage p₂ := pointImage_comp_le p₂ r₂ hxN₂
      have h2 := hPQ₂ h1
      rw [hQ₂pt] at h2
      exact h2
    have huψ : u ∈ (Dynamic.parabolic ψ).carrier pt := by
      have := mul_mem (inv_mem hyψ) hxψ
      rwa [inv_mul_cancel_left] at this
    have huU₂ : u ∈ (Dynamic.unipotent ψ).carrier pt := by
      have h : u ∈ (Dynamic.unipotent ξb ⊓ Dynamic.parabolic ψ).carrier pt := ⟨hu, huψ⟩
      rw [hU₂ψ] at h
      exact h.2
    have huN₂ : u ∈ pointImage (r₂ ≫ p₂) := by
      apply hU₂N₂
      rw [hU₂]
      exact huU₂
    have hyN₂ : y ∈ pointImage (r₂ ≫ p₂) := by
      have := (pointImage (r₂ ≫ p₂)).mul_mem hxN₂ ((pointImage (r₂ ≫ p₂)).inv_mem huN₂)
      rwa [mul_inv_cancel_right] at this
    have hyP₁ : y ∈ (Dynamic.parabolic χ).carrier pt := by
      have hyL : y ∈ pointImage (lQ₁ ≫ q₁) := by
        rw [hLpt, ← hZξb]; exact hyZ
      have hyP₂ : y ∈ pointImage p₂ := pointImage_comp_le p₂ r₂ hyN₂
      have h : y ∈ pointImage (p' ≫ lQ₁ ≫ q₁) := by
        rw [hP'₂]; exact ⟨hyP₂, hyL⟩
      rw [hP'₁] at h
      rw [← hP₁pt]
      exact h.1
    have hy1 : y = 1 := Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hyU hyP₁
    subst hy1
    show 1 * u ∈ _
    rw [one_mul]
    exact ⟨hu, huU₂⟩
  · rintro x ⟨hxU, hxU₂⟩
    refine ⟨?_, ?_⟩
    · rw [← hUθ]
      exact hθU pt hxU
    · apply hU₂N₂
      rw [hU₂]
      exact hxU₂

end Radicals

end Langlands.Aubert.General.RepresentedParabolic
