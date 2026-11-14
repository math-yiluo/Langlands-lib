import Langlands.Geometry.Building.ApartmentFacetClosureFixing

/-! # A common normalizer for two apartment coordinates over any field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

/-- An orbit of the unipotent radical of a generic cocharacter meets the original apartment
in at most one point. This uses the original quotient relation and sharp-fixer exchange. -/
theorem eq_of_unipotent_smul_apartmentMap_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {g : rationalPoints G}
    (hgU : g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    {x y : D.Apartment} (hxy : g • D.apartmentMap x = D.apartmentMap y) :
    x = y := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro a ha
    simpa only [map_neg] using neg_ne_zero.mpr (hν a ha)
  have heq : ApartmentQuotient.mk D.sharpFixerFamily (1, y) =
      ApartmentQuotient.mk D.sharpFixerFamily (g, x) := by
    change ApartmentQuotient.mk D.sharpFixerFamily (g * 1, x) =
      ApartmentQuotient.mk D.sharpFixerFamily (1, y) at hxy
    simpa only [mul_one] using hxy.symm
  obtain ⟨m, hmy, hs⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff D.sharpFixerFamily 1 g y x).mp heq
  simp only [inv_one, one_mul] at hs
  have hsharp := D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi y (-ν) hνneg
  rw [neg_neg] at hsharp
  obtain ⟨vw, ⟨v, hv, w, hw, rfl⟩, q, hq, hvwq⟩ := hsharp hs
  change v * w * q = g * (m : rationalPoints G) at hvwq
  obtain ⟨-, hqN, hqy⟩ := KPApartmentData.mem_sharpNormalizerStabilizer.mp hq
  let n : normalizerPoints i := ⟨q, hqN⟩ * m⁻¹
  have hvU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints y ν hv).1
  have hwU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints y (-ν) hw).1
  have hpos : v⁻¹ * g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hvU) hgU
  have hopp : w⁻¹ ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom ν ≫ i))).carrier (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter i ν]
    exact Subgroup.inv_mem _ hwU
  have hn : (n : rationalPoints G) = w⁻¹ * (v⁻¹ * g) := by
    change q * (m : rationalPoints G)⁻¹ = _
    have hg : g = v * w * q * (m : rationalPoints G)⁻¹ := by
      rw [hvwq]
      group
    rw [hg]
    group
  have hn1 : n = 1 :=
    normalizer_eq_one_of_unipotent_product i ν n ⟨_, hopp⟩ ⟨_, hpos⟩ hn
  have hqm : (⟨q, hqN⟩ : normalizerPoints i) = m := mul_inv_eq_one.mp hn1
  have hmfix : m • y = y := by rw [← hqm]; exact hqy
  exact hmy.symm.trans hmfix

/-- If one rational element takes two original apartment points to two original apartment
points, one element of the actual normalizer has the same values at both points. No metric,
common-apartment existence theorem, or Tits-system comparison is assumed. -/
theorem exists_normalizer_eq_of_two_apartmentMap_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (g : rationalPoints G) (a b x y : D.Apartment)
    (ha : g • D.apartmentMap a = D.apartmentMap x)
    (hb : g • D.apartmentMap b = D.apartmentMap y) :
    ∃ n : normalizerPoints i, n • a = x ∧ n • b = y := by
  obtain ⟨w, hw⟩ := exists_mk_vadd_eq x y
  obtain ⟨ν, hν, hadapt⟩ :=
    exists_genericCocharacter_eval_nonneg_of_isMaximalSplitTorus hG hi w
  have hνneg : IsGenericCocharacter i (-ν) := by
    intro c hc
    simpa only [map_neg] using neg_ne_zero.mpr (hν c hc)
  have heq : ApartmentQuotient.mk D.sharpFixerFamily (1, x) =
      ApartmentQuotient.mk D.sharpFixerFamily (g, a) := by
    change ApartmentQuotient.mk D.sharpFixerFamily (g * 1, a) =
      ApartmentQuotient.mk D.sharpFixerFamily (1, x) at ha
    simpa only [mul_one] using ha.symm
  obtain ⟨m, hmx, hs⟩ :=
    (ApartmentQuotient.mk_eq_mk_iff D.sharpFixerFamily 1 g x a).mp heq
  simp only [inv_one, one_mul] at hs
  have hsharp := D.sharpFixer_subset_mul_sharpNormalizerStabilizer hG hi x (-ν) hνneg
  rw [neg_neg] at hsharp
  obtain ⟨uv, ⟨u, hu, v, hv, rfl⟩, q, hq, huvq⟩ := hsharp hs
  change u * v * q = g * (m : rationalPoints G) at huvq
  obtain ⟨-, hqN, hqx⟩ := KPApartmentData.mem_sharpNormalizerStabilizer.mp hq
  let n : normalizerPoints i := ⟨q, hqN⟩ * m⁻¹
  have hna : n • a = x := by
    change (⟨q, hqN⟩ * m⁻¹) • a = x
    rw [mul_smul, ← hmx, inv_smul_smul, hqx]
  have huy : u • D.apartmentMap y = D.apartmentMap y := by
    rw [hw]
    exact D.mem_reducedFixer.1 (D.sharpFixer_le_reducedFixer _
      (D.positiveChamberRootGroups_le_sharpFixer_vadd x ν hadapt hu))
  have hg : g = u * (v * (n : rationalPoints G)) := by
    change g = u * (v * (q * (m : rationalPoints G)⁻¹))
    rw [← mul_assoc, ← mul_assoc, huvq]
    group
  have hvnb : v • D.apartmentMap (n • b) = D.apartmentMap y := by
    rw [D.apartmentMap_smul]
    apply (MulAction.injective u)
    change u • (v • ((n : rationalPoints G) • D.apartmentMap b)) =
      u • D.apartmentMap y
    calc
      _ = g • D.apartmentMap b := by rw [hg, mul_smul, mul_smul]
      _ = _ := hb.trans huy.symm
  have hvU := (D.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hv).1
  exact ⟨n, hna, D.eq_of_unipotent_smul_apartmentMap_eq hG hi (-ν) hνneg hvU hvnb⟩

/-- A choice of actual normalizer agreeing with a rational element at two supplied
apartment points whose images stay in the original apartment. -/
def pairNormalizer
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (g : rationalPoints G) (a b x y : D.Apartment)
    (ha : g • D.apartmentMap a = D.apartmentMap x)
    (hb : g • D.apartmentMap b = D.apartmentMap y) : normalizerPoints i :=
  Classical.choose (D.exists_normalizer_eq_of_two_apartmentMap_eq hG hi g a b x y ha hb)

theorem pairNormalizer_spec
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (g : rationalPoints G) (a b x y : D.Apartment)
    (ha : g • D.apartmentMap a = D.apartmentMap x)
    (hb : g • D.apartmentMap b = D.apartmentMap y) :
    D.pairNormalizer hG hi g a b x y ha hb • a = x ∧
      D.pairNormalizer hG hi g a b x y ha hb • b = y :=
  Classical.choose_spec
    (D.exists_normalizer_eq_of_two_apartmentMap_eq hG hi g a b x y ha hb)

variable [Fintype (relativeRoots i)]

local instance : NormedAddCommGroup (TranslationSpace i) :=
  RootTranslationMetric.normedAddCommGroup i

/-- The canonical root norm of the displacement is independent of two apartment
coordinate pairs related by the same rational group element. -/
theorem norm_vsub_eq_of_two_apartmentMap_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (g : rationalPoints G) (a b x y : D.Apartment)
    (ha : g • D.apartmentMap a = D.apartmentMap x)
    (hb : g • D.apartmentMap b = D.apartmentMap y) :
    ‖(x -ᵥ y : TranslationSpace i)‖ = ‖(a -ᵥ b : TranslationSpace i)‖ := by
  obtain ⟨n, hna, hnb⟩ :=
    D.exists_normalizer_eq_of_two_apartmentMap_eq hG hi g a b x y ha hb
  rw [← hna, ← hnb]
  change ‖(D.normalizerAffineEquiv n).toAffineMap a -ᵥ
    (D.normalizerAffineEquiv n).toAffineMap b‖ = _
  rw [← (D.normalizerAffineEquiv n).toAffineMap.linearMap_vsub]
  exact RootTranslationMetric.norm_translationAction i n (a -ᵥ b)

end Langlands.Geometry.Building.KPApartmentData
