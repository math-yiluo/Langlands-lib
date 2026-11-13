import Langlands.Representation.Exponents.LeviJacquetContragredientStructure
import Langlands.GroupScheme.Rational.NestedParabolicPointDecompositionProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Dynamic.StableIntersection
import Langlands.GroupScheme.Dynamic.CommutingRefinements
import Langlands.GroupScheme.Reductive.SteinbergBigCellGeometry
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Absolute.MaximalRankRadicalTorusIntersectionOfComplement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Reductive.NormalUnipotentRadicalIntersectionReduction

/-! # The integration domain of Renard VII.3.5 (ii) lies in the Levi

For represented parabolics `P₁ = MN₁`, `P₂ = MN₂` of `G` contained (on rational points) in a
represented parabolic `Q = LU`, an opposite `P̄₁ = MN̄₁` of `P₁`, and the corresponding
parabolics `P₁' = MN₁'`, `P₂' = MN₂'`, `P̄₁' = MN̄₁'` of `L`, the subgroup
`V = N̄₁(F) ∩ N₂(F)` of `G(F)` is the image of `V' = N̄₁'(F) ∩ N₂'(F)` under `L(F) → G(F)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.Dynamic

/-- The dynamic unipotent subgroup `U(χ)` is stable under conjugation by a cocharacter `τ`
whose image commutes with `χ` (lies in the centralizer `Z(χ)`). -/
theorem unipotent_isStable_conjugation_of_range_le_centralizer {S : Scheme.{u}}
    {G : GroupScheme S} (χ τ : (Gm S).toGrp ⟶ G)
    (h : SubgroupFunctor.range τ ≤ centralizer χ) :
    (AutomorphicAction.conjugation τ).IsStable (unipotent χ) := by
  intro T t g hg
  rw [AutomorphicAction.conjugation_act]
  have hz : t ≫ τ.hom.hom ∈ (centralizer χ).carrier T :=
    h T (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
  exact (centralizer_le_normalizer_unipotent χ T hz g).1 hg

end Langlands.GroupScheme.Dynamic

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k]

/-- The image of a point of `pointImage f` under `g` lies in `pointImage (f ≫ g)`. -/
theorem map_mem_pointImage_comp {H K G : GroupScheme (Spec (CommRingCat.of k))}
    {f : H ⟶ K} (g : K ⟶ G) {x : rationalPoints K} (hx : x ∈ pointImage f) :
    rationalPoints.map g x ∈ pointImage (f ≫ g) := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨y, by simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]⟩

/-- Along a monomorphism `j`, a point whose image lies in `pointImage (f ≫ j)` lies in
`pointImage f`. -/
theorem mem_pointImage_of_map_mem_comp {H K G : GroupScheme (Spec (CommRingCat.of k))}
    {f : H ⟶ K} {j : K ⟶ G} [Mono j.hom.hom] {x : rationalPoints K}
    (hx : rationalPoints.map j x ∈ pointImage (f ≫ j)) : x ∈ pointImage f := by
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  simp only [rationalPoints.map_apply, Grp.comp_hom_hom, ← Category.assoc] at hy
  exact (cancel_mono j.hom.hom).1 hy

/-- `P ∩ P̄ = M` on rational points identifies the radical of `P̄` with the opposite dynamic
unipotent subgroup, when the parabolic `P` agrees with `P(χ)` only on rational points and the
Levi `M` is `Z(χ)`. This is `pointImage_opposite_radical_eq_dynamic` with a pointwise
hypothesis on `P`. -/
theorem pointImage_opposite_radical_eq_dynamic_of_points
    {G P Pbar M Nbar : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} (m : M ⟶ P)
    (hPχ : pointImage p = (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)))
    (hMχ : SubgroupFunctor.range (m ≫ p) = Dynamic.centralizer χ)
    {pbar : Pbar ⟶ G} (hpbar : IsParabolicSubgroup pbar)
    {mbar : M ⟶ Pbar} (hmbar : IsRationalLeviSubgroup mbar)
    {nbar : Nbar ⟶ Pbar} (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hP : mbar ≫ pbar = m ≫ p)
    (hPP : pointImage p ⊓ pointImage pbar = pointImage (m ≫ p)) :
    pointImage (nbar ≫ pbar) =
      (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier (Over.mk (𝟙 _)) := by
  obtain ⟨χ', hPχ', hMχ'⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hpbar hmbar
  have hZ : Dynamic.centralizer χ' = Dynamic.centralizer χ := by
    rw [← hMχ', ← hMχ, hP]
  have hrat : (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊓
        (Dynamic.parabolic χ').carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [← hPχ, ← hPχ', ← hMχ, ← pointImage_eq_range_carrier, ← pointImage_eq_range_carrier]
    exact hPP
  obtain ⟨-, hU⟩ := oppositeDynamicParabolicUniqueness k G hG χ χ' hZ hrat
  rw [pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG χ' hpbar hPχ' hnbar,
    hU]


section LocalField

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]

/-- Renard VII.3.5 (ii), first structural step: the rational points of the opposite radical
`N̄₁` lying in `Q` lie in the Levi `L` of `Q`, when `P₁ ⊆ Q` on rational points and `M ⊆ L`.
-/
theorem oppositeRadical_inf_le_levi
    {G M P₁ N₁ Pb₁ Nb₁ Q L U P₁' N₁' : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
    (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
    (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
    (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
    {pb₁ : Pb₁ ⟶ G} {lb₁ : M ⟶ Pb₁} {rb₁ : Nb₁ ⟶ Pb₁}
    (hpb₁ : IsParabolicSubgroup pb₁) (hlb₁ : IsRationalLeviSubgroup lb₁)
    (hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (p₁' : P₁' ⟶ L) (l₁' : M ⟶ P₁') (r₁' : N₁' ⟶ P₁')
    (hp₁' : IsParabolicSubgroup p₁') (hl₁' : IsRationalLeviSubgroup l₁')
    (hr₁' : LeviSubgroup.IsGeometricUnipotentRadical r₁')
    (hmul₁' : IsIso (subgroupMultiplication l₁' r₁'))
    (hb : lb₁ ≫ pb₁ = l₁ ≫ p₁)
    (hPP : pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁))
    (hPQ : pointImage p₁ ≤ pointImage q)
    (hM : l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁)
    (hPL : pointImage (p₁' ≫ lQ ≫ q) = pointImage p₁ ⊓ pointImage (lQ ≫ q)) :
    pointImage (rb₁ ≫ pb₁) ⊓ pointImage q ≤ pointImage (lQ ≫ q) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsSeparated G.X.hom := hG.isSeparated
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hp₁ hl₁
  obtain ⟨τ, hPτ, hLτ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hq hlQ
  have hNb : pointImage (rb₁ ≫ pb₁) =
      (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier (Over.mk (𝟙 _)) :=
    pointImage_opposite_radical_eq_dynamic parabolicDynamic oppositeDynamicParabolicUniqueness
      hG χ l₁ hPχ hMχ hpb₁ hlb₁ hrb₁ hb hPP
  have hU : pointImage (rQ ≫ q) = (Dynamic.unipotent τ).carrier (Over.mk (𝟙 _)) :=
    pointImage_radical_eq_dynamic dynamicGeometricUnipotentRadical hG τ hq hPτ hrQ
  have hQ : pointImage q = (Dynamic.parabolic τ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hPτ]
  have hL : pointImage (lQ ≫ q) = (Dynamic.centralizer τ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hLτ]
  have hP₁ : pointImage p₁ = (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := by
    rw [pointImage_eq_range_carrier, hPχ]
  -- `χ` commutes with `τ`: its image lies in `M ⊆ L = Z(τ)`.
  have hχτ : SubgroupFunctor.range χ ≤ Dynamic.centralizer τ := by
    refine (Dynamic.range_le_centralizer χ).trans ?_
    rw [← hMχ, ← hLτ, ← hM]
    simpa only [Category.assoc] using SubgroupFunctor.range_comp_le (l₁' ≫ p₁') (lQ ≫ q)
  have hτχ : SubgroupFunctor.range τ ≤
      Dynamic.centralizer (Dynamic.oppositeCocharacter χ) := by
    rw [Dynamic.centralizer_oppositeCocharacter]
    exact Dynamic.range_le_centralizer_symm τ χ hχτ
  have hstab := Dynamic.unipotent_isStable_conjugation_of_range_le_centralizer
    (Dynamic.oppositeCocharacter χ) τ hτχ
  have hdec := Dynamic.inf_parabolic_eq_mul_of_isStable τ
    (Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter χ))
    (Dynamic.Affine.isClosedSubgroup_unipotentHom (Dynamic.oppositeCocharacter χ)) hstab
    (Over.mk (𝟙 _))
  -- The radical `U(F)` of `Q` lies in `P₁(F)`.
  have hUP : pointImage (rQ ≫ q) ≤ pointImage p₁ := by
    obtain ⟨-, -, h⟩ := nestedParabolicPointDecomposition k G hG P₁ M N₁ Q L U P₁' N₁'
      p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁'
      hPQ hM (by rw [inf_comm]; exact hPL)
    intro u hu
    have : u ∈ ((pointImage (p₁' ≫ lQ ≫ q) : Set (rationalPoints G)) *
        (pointImage (rQ ≫ q) : Set (rationalPoints G))) := ⟨1, one_mem _, u, hu, one_mul u⟩
    rw [← h] at this
    exact this
  rintro x ⟨hxN, hxQ⟩
  rw [hNb] at hxN
  rw [hQ] at hxQ
  have hx : x ∈ (↑((Dynamic.unipotent (Dynamic.oppositeCocharacter χ) ⊓
      Dynamic.parabolic τ).carrier (Over.mk (𝟙 _))) : Set _) := ⟨hxN, hxQ⟩
  rw [hdec] at hx
  obtain ⟨a, ⟨-, haZ⟩, n, ⟨hnN, hnU⟩, rfl⟩ := hx
  have hnP : n ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := by
    rw [← hP₁]
    exact hUP (by rw [hU]; exact hnU)
  have hn1 : n = 1 := Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hnN hnP
  subst hn1
  show a * 1 ∈ pointImage (lQ ≫ q)
  rw [mul_one, hL]
  exact haZ

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k] in
/-- Renard VII.3.5 (ii), second structural step: a rational point `x` of `L` lies in the
opposite radical `N̄₁'(F)` of `P₁' = P₁ ∩ L` in `L` exactly when its image lies in the opposite
radical `N̄₁(F)` of `P₁` in `G`. -/
theorem mem_innerOppositeRadical_iff
    {G M P₁ Pb₁ Nb₁ Q L P₁' Pb₁' Nb₁' : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁)
    (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
    {pb₁ : Pb₁ ⟶ G} {lb₁ : M ⟶ Pb₁} {rb₁ : Nb₁ ⟶ Pb₁}
    (hpb₁ : IsParabolicSubgroup pb₁) (hlb₁ : IsRationalLeviSubgroup lb₁)
    (hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
    (q : Q ⟶ G) (lQ : L ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (p₁' : P₁' ⟶ L) (l₁' : M ⟶ P₁')
    {pb₁' : Pb₁' ⟶ L} {lb₁' : M ⟶ Pb₁'} {rb₁' : Nb₁' ⟶ Pb₁'}
    (hpb₁' : IsParabolicSubgroup pb₁') (hlb₁' : IsRationalLeviSubgroup lb₁')
    (hrb₁' : LeviSubgroup.IsGeometricUnipotentRadical rb₁')
    (hb : lb₁ ≫ pb₁ = l₁ ≫ p₁)
    (hPP : pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁))
    (hM : l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁)
    (hb' : lb₁' ≫ pb₁' = l₁' ≫ p₁')
    (hPP' : pointImage p₁' ⊓ pointImage pb₁' = pointImage (l₁' ≫ p₁'))
    (hPL : pointImage (p₁' ≫ lQ ≫ q) = pointImage p₁ ⊓ pointImage (lQ ≫ q))
    (x : rationalPoints L) :
    x ∈ pointImage (rb₁' ≫ pb₁') ↔
      rationalPoints.map (lQ ≫ q) x ∈ pointImage (rb₁ ≫ pb₁) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsSeparated G.X.hom := hG.isSeparated
  have hL : IsConnectedReductive L := hlQ.isConnectedReductive
  have hjc : IsClosedSubgroup (lQ ≫ q) := hlQ.isClosedSubgroup.comp hq.isClosedSubgroup
  have : IsClosedImmersion (lQ ≫ q).hom.hom.left := hjc
  have : Mono (lQ ≫ q).hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hPχ, hMχ⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi parabolicDynamic
      dynamicGeometricUnipotentRadical hG hp₁ hl₁
  have hle : SubgroupFunctor.range χ ≤ SubgroupFunctor.range (lQ ≫ q) := by
    refine (Dynamic.range_le_centralizer χ).trans ?_
    rw [← hMχ, ← hM]
    simpa only [Category.assoc] using SubgroupFunctor.range_comp_le (l₁' ≫ p₁') (lQ ≫ q)
  obtain ⟨χL, hχL⟩ : ∃ χL : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L, χL ≫ (lQ ≫ q) = χ :=
    ⟨_, SubgroupFunctor.IsRepresentedBy.factorHom_comp hjc.isRepresentedBy_range χ hle⟩
  have hPχL : pointImage p₁' = (Dynamic.parabolic χL).carrier (Over.mk (𝟙 _)) := by
    ext y
    have hcomap : y ∈ (Dynamic.parabolic χL).carrier (Over.mk (𝟙 _)) ↔
        rationalPoints.map (lQ ≫ q) y ∈ pointImage p₁ := by
      rw [Dynamic.parabolic_eq_comap_of_isClosedSubgroup χL (lQ ≫ q) hjc, hχL,
        SubgroupFunctor.mem_comap, pointImage_eq_range_carrier, hPχ, rationalPoints.map_apply]
    rw [hcomap]
    constructor
    · intro hy
      have h := map_mem_pointImage_comp (lQ ≫ q) hy
      rw [hPL] at h
      exact h.1
    · intro hy
      have h : rationalPoints.map (lQ ≫ q) y ∈ pointImage p₁ ⊓ pointImage (lQ ≫ q) :=
        ⟨hy, MonoidHom.mem_range.mpr ⟨y, rfl⟩⟩
      rw [← hPL] at h
      exact mem_pointImage_of_map_mem_comp h
  have hMχL : SubgroupFunctor.range (l₁' ≫ p₁') = Dynamic.centralizer χL := by
    rw [Dynamic.centralizer_eq_comap_of_isClosedSubgroup χL (lQ ≫ q) hjc, hχL, ← hMχ, ← hM]
    simpa only [Category.assoc] using (range_comp_comap_of_mono (l₁' ≫ p₁') (lQ ≫ q)).symm
  have hNbL := pointImage_opposite_radical_eq_dynamic_of_points hL χL l₁' hPχL hMχL hpb₁'
    hlb₁' hrb₁' hb' hPP'
  have hNb : pointImage (rb₁ ≫ pb₁) =
      (Dynamic.unipotent (Dynamic.oppositeCocharacter χ)).carrier (Over.mk (𝟙 _)) :=
    pointImage_opposite_radical_eq_dynamic parabolicDynamic oppositeDynamicParabolicUniqueness
      hG χ l₁ hPχ hMχ hpb₁ hlb₁ hrb₁ hb hPP
  have hopp : Dynamic.oppositeCocharacter χL ≫ (lQ ≫ q) = Dynamic.oppositeCocharacter χ := by
    simp only [Dynamic.oppositeCocharacter, Category.assoc, hχL]
  rw [hNbL, hNb, Dynamic.unipotent_eq_comap_of_isClosedSubgroup
    (Dynamic.oppositeCocharacter χL) (lQ ≫ q) hjc, hopp, rationalPoints.map_apply]
  exact SubgroupFunctor.mem_comap

/-- Renard VII.3.5 (ii): the integration domain `V = N̄₁(F) ∩ N₂(F)` is the image of
`V' = N̄₁'(F) ∩ N₂'(F)` under the embedding `L(F) → G(F)`. -/
theorem innerIntegrationDomain_eq_map
    {G M P₁ N₁ P₂ N₂ Pb₁ Nb₁ Q L U P₁' N₁' P₂' N₂' Pb₁' Nb₁' :
      GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
    (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
    (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
    (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
    (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
    (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
    (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
    (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
    {pb₁ : Pb₁ ⟶ G} {lb₁ : M ⟶ Pb₁} {rb₁ : Nb₁ ⟶ Pb₁}
    (hpb₁ : IsParabolicSubgroup pb₁) (hlb₁ : IsRationalLeviSubgroup lb₁)
    (hrb₁ : LeviSubgroup.IsGeometricUnipotentRadical rb₁)
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
    (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
    (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (h₂₁ : l₂ ≫ p₂ = l₁ ≫ p₁) (hb : lb₁ ≫ pb₁ = l₁ ≫ p₁)
    (hPP : pointImage p₁ ⊓ pointImage pb₁ = pointImage (l₁ ≫ p₁))
    (hPQ₁ : pointImage p₁ ≤ pointImage q) (hPQ₂ : pointImage p₂ ≤ pointImage q)
    (p₁' : P₁' ⟶ L) (l₁' : M ⟶ P₁') (r₁' : N₁' ⟶ P₁')
    (hp₁' : IsParabolicSubgroup p₁') (hl₁' : IsRationalLeviSubgroup l₁')
    (hr₁' : LeviSubgroup.IsGeometricUnipotentRadical r₁')
    (hmul₁' : IsIso (subgroupMultiplication l₁' r₁'))
    (p₂' : P₂' ⟶ L) (l₂' : M ⟶ P₂') (r₂' : N₂' ⟶ P₂')
    (hp₂' : IsParabolicSubgroup p₂') (hl₂' : IsRationalLeviSubgroup l₂')
    (hr₂' : LeviSubgroup.IsGeometricUnipotentRadical r₂')
    (hmul₂' : IsIso (subgroupMultiplication l₂' r₂'))
    {pb₁' : Pb₁' ⟶ L} {lb₁' : M ⟶ Pb₁'} {rb₁' : Nb₁' ⟶ Pb₁'}
    (hpb₁' : IsParabolicSubgroup pb₁') (hlb₁' : IsRationalLeviSubgroup lb₁')
    (hrb₁' : LeviSubgroup.IsGeometricUnipotentRadical rb₁')
    (hM : l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁) (h₂₁' : l₂' ≫ p₂' = l₁' ≫ p₁')
    (hb' : lb₁' ≫ pb₁' = l₁' ≫ p₁')
    (hPP' : pointImage p₁' ⊓ pointImage pb₁' = pointImage (l₁' ≫ p₁'))
    (hPL₁ : pointImage (p₁' ≫ lQ ≫ q) = pointImage p₁ ⊓ pointImage (lQ ≫ q))
    (hPL₂ : pointImage (p₂' ≫ lQ ≫ q) = pointImage p₂ ⊓ pointImage (lQ ≫ q)) :
    pointImage (rb₁ ≫ pb₁) ⊓ pointImage (r₂ ≫ p₂) =
      (pointImage (rb₁' ≫ pb₁') ⊓ pointImage (r₂' ≫ p₂')).map
        (rationalPoints.map (lQ ≫ q)) := by
  have hjc : IsClosedSubgroup (lQ ≫ q) := hlQ.isClosedSubgroup.comp hq.isClosedSubgroup
  have : IsClosedImmersion (lQ ≫ q).hom.hom.left := hjc
  have : Mono (lQ ≫ q).hom.hom := Over.mono_of_mono_left _
  have hM₂ : l₂' ≫ p₂' ≫ lQ ≫ q = l₂ ≫ p₂ := by
    rw [h₂₁, ← hM, ← Category.assoc, h₂₁', Category.assoc]
  obtain ⟨hNL₂, -, -⟩ := nestedParabolicPointDecomposition k G hG P₂ M N₂ Q L U P₂' N₂'
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂'
    hPQ₂ hM₂ (by rw [inf_comm]; exact hPL₂)
  have hN₂ : pointImage ((r₂' ≫ p₂') ≫ lQ ≫ q) =
      pointImage (lQ ≫ q) ⊓ pointImage (r₂ ≫ p₂) := by
    rw [Category.assoc]
    exact hNL₂
  have hiff := mem_innerOppositeRadical_iff hG p₁ l₁ hp₁ hl₁ hpb₁ hlb₁ hrb₁ q lQ hq hlQ p₁' l₁'
    hpb₁' hlb₁' hrb₁' hb hPP hM hb' hPP' hPL₁
  ext y
  constructor
  · rintro ⟨hy₁, hy₂⟩
    have hyQ : y ∈ pointImage q := hPQ₂ (pointImage_comp_le p₂ r₂ hy₂)
    obtain ⟨x, rfl⟩ := oppositeRadical_inf_le_levi hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ hpb₁ hlb₁ hrb₁
      q lQ rQ hq hlQ hrQ hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hb hPP hPQ₁ hM hPL₁ ⟨hy₁, hyQ⟩
    refine ⟨x, ⟨(hiff x).2 hy₁, ?_⟩, rfl⟩
    apply mem_pointImage_of_map_mem_comp (j := lQ ≫ q)
    rw [hN₂]
    exact ⟨⟨x, rfl⟩, hy₂⟩
  · rintro ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    refine ⟨(hiff x).1 hx₁, ?_⟩
    have h := map_mem_pointImage_comp (lQ ≫ q) hx₂
    rw [hN₂] at h
    exact h.2

end LocalField

/-- A homomorphism that is a topological embedding restricts to a topological group
isomorphism from a subgroup onto any subgroup equal to its image. -/
theorem exists_continuousMulEquiv_of_isEmbedding {A B : Type*} [Group A] [Group B]
    [TopologicalSpace A] [TopologicalSpace B] (f : A →* B) (hf : Topology.IsEmbedding f)
    (H : Subgroup A) (K : Subgroup B) (hK : K = H.map f) :
    ∃ e : H ≃ₜ* K, ∀ x : H, (e x : B) = f x := by
  subst hK
  let e₀ : H ≃* H.map f := H.equivMapOfInjective f hf.injective
  have he₀ : ∀ x : H, (e₀ x : B) = f x := fun x =>
    Subgroup.coe_equivMapOfInjective_apply H f hf.injective x
  have h₁ : Continuous e₀ := by
    apply continuous_induced_rng.2
    have : (Subtype.val ∘ e₀ : H → B) = f ∘ Subtype.val := funext he₀
    rw [this]
    exact hf.continuous.comp continuous_subtype_val
  have h₂ : Continuous e₀.symm := by
    apply continuous_induced_rng.2
    rw [hf.isInducing.continuous_iff]
    have : (f ∘ (Subtype.val ∘ e₀.symm) : H.map f → B) = Subtype.val := by
      funext y
      simp only [Function.comp_apply]
      rw [← he₀, MulEquiv.apply_symm_apply]
    rw [this]
    exact continuous_subtype_val
  exact ⟨{ toMulEquiv := e₀, continuous_toFun := h₁, continuous_invFun := h₂ }, he₀⟩

section Embedding

variable [TopologicalSpace k] {G Q L : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance innerAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- The point map `L(F) → G(F)` of a Levi `L` of a parabolic `Q` of `G` is a topological
embedding (for the canonical topologies). -/
theorem isEmbedding_leviPoints (q : Q ⟶ G) (lQ : L ⟶ Q) (hq : IsParabolicSubgroup q)
    (hlQ : IsRationalLeviSubgroup lQ) :
    letI := leviPointTopology lQ hlQ
    Topology.IsEmbedding (rationalPoints.map (lQ ≫ q)) := by
  let _ := leviPointTopology lQ hlQ
  have h : (rationalPoints.map (lQ ≫ q) : rationalPoints L → rationalPoints G) =
      Subtype.val ∘ leviPointsEquiv q lQ hq hlQ := by
    funext x
    rfl
  rw [h]
  exact Topology.IsEmbedding.subtypeVal.comp
    (leviPointsEquiv q lQ hq hlQ).toHomeomorph.isEmbedding

/-- A subgroup `V'` of `L(F)` is isomorphic, as a topological group, to its image `V` in
`G(F)`, by an isomorphism given by the point map. -/
theorem exists_leviSubgroupEquiv (q : Q ⟶ G) (lQ : L ⟶ Q) (hq : IsParabolicSubgroup q)
    (hlQ : IsRationalLeviSubgroup lQ) (V : Subgroup (rationalPoints G))
    (V' : Subgroup (rationalPoints L)) (hV : V = V'.map (rationalPoints.map (lQ ≫ q))) :
    letI := leviPointTopology lQ hlQ
    ∃ e : V' ≃ₜ* V, ∀ x : V', (e x : rationalPoints G) = rationalPoints.map (lQ ≫ q) x := by
  let _ := leviPointTopology lQ hlQ
  exact exists_continuousMulEquiv_of_isEmbedding _ (isEmbedding_leviPoints q lQ hq hlQ) V' V hV

end Embedding

end Langlands.Aubert.General.RepresentedParabolic
