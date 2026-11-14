import Langlands.GroupScheme.Rational.TorusConjugatorGaloisCocycle
import Langlands.GroupScheme.Reductive.TitsIndexCentralizerConjugacy
import Langlands.Geometry.Building.KPBuilding

/-! # Centralizing a common apartment attached to a descended torus -/

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "T'_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T'
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b)

/-- A chart of a descended maximal split torus can be represented by a conjugator
centralizing any common split subtorus, with normalizer-valued Galois differences.
The set of covered building points is retained. -/
theorem exists_centralizing_conj_covering_of_descended_torus
    (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ G)
    [Mono (i_K i).hom.hom.left] [IsAffineHom (G_K).X.hom]
    {ω : Kˣ → ℝ} (D : KPApartmentData (S := T_K) (i_K i) ω)
    (hG : IsConnectedReductive G_K)
    {A : CommGroupScheme (Spec (CommRingCat.of K))}
    (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ G_K)
    (hi : IsMaximalSplitTorus (T := T_K) (i_K i))
    (hj : IsMaximalSplitTorus (T := T'_K) (i_K j))
    (f : A ⟶ T_K) (f' : A ⟶ T'_K)
    (hf : CommGroupScheme.groupHom f ≫ i_K i = a)
    (hf' : CommGroupScheme.groupHom f' ≫ i_K j = a)
    (g₀ : rationalPoints G_K) (e₀ : T_K ≅ T'_K)
    (hg₀ : i_K i ≫ ((G_K).innerIso g₀).hom =
      CommGroupScheme.groupHom e₀.hom ≫ i_K j) :
    ∃ g : rationalPoints G_K,
      g ∈ centralizerPoints a ∧
      (∀ σ : K ≃ₐ[k] K,
        g⁻¹ * rationalConjugate k K G σ g ∈ normalizerPoints (T := T_K) (i_K i)) ∧
      ∀ y : D.ReducedBuilding,
        (∃ x : D.Apartment, g₀ • D.apartmentMap x = y) ↔
          ∃ x : D.Apartment, g • D.apartmentMap x = y := by
  obtain ⟨g, e, hg, ha⟩ := exists_centralizing_conj_of_isMaximalSplitTorus
    hG hA a hi hj f f' hf hf'
  refine ⟨g, (mem_centralizerPoints a).mpr ha, ?_, ?_⟩
  · intro σ
    exact inv_mul_rationalConjugate_mem_normalizerPoints_of_transporters k K i j σ hg
  · intro y
    constructor
    · rintro ⟨x, hx⟩
      let n : normalizerPoints (T := T_K) (i_K i) :=
        ⟨g⁻¹ * g₀, inv_mul_mem_normalizerPoints_of_transporters hg₀ hg⟩
      refine ⟨n • x, ?_⟩
      rw [apartmentMap_smul, smul_smul]
      change (g * (g⁻¹ * g₀)) • D.apartmentMap x = y
      simpa only [mul_inv_cancel_left] using hx
    · rintro ⟨x, hx⟩
      let n : normalizerPoints (T := T_K) (i_K i) :=
        ⟨g₀⁻¹ * g, inv_mul_mem_normalizerPoints_of_transporters hg hg₀⟩
      refine ⟨n • x, ?_⟩
      rw [apartmentMap_smul, smul_smul]
      change (g₀ * (g₀⁻¹ * g)) • D.apartmentMap x = y
      simpa only [mul_inv_cancel_left] using hx

section Choice

variable (i : T.toGrp ⟶ G) (j : T'.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left] [IsAffineHom (((GroupScheme.baseChange (algebraBaseMap k K)).obj G)).X.hom]
  {ω : Kˣ → ℝ} (D : KPApartmentData (S := ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ω)
  (hG : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  {A : CommGroupScheme (Spec (CommRingCat.of K))}
  (hA : IsSplitTorus A.toGrp) (a : A.toGrp ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
  (hi : IsMaximalSplitTorus (T := ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (hj : IsMaximalSplitTorus (T := ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T')) ((GroupScheme.baseChange (algebraBaseMap k K)).map j))
  (f : A ⟶ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) (f' : A ⟶ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T'))
  (hf : CommGroupScheme.groupHom f ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map i = a)
  (hf' : CommGroupScheme.groupHom f' ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map j = a)
  (g₀ : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) (e₀ : ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T'))
  (hg₀ : (GroupScheme.baseChange (algebraBaseMap k K)).map i ≫ ((((GroupScheme.baseChange (algebraBaseMap k K)).obj G)).innerIso g₀).hom =
    CommGroupScheme.groupHom e₀.hom ≫ (GroupScheme.baseChange (algebraBaseMap k K)).map j)

/-- Choose a centralizing representative of the supplied descended apartment,
retaining its covered points and the normalizer-valued Galois differences. -/
def centralizingConjCoveringOfDescendedTorus :
    {g : rationalPoints G_K //
      g ∈ centralizerPoints a ∧
      (∀ σ : K ≃ₐ[k] K,
        g⁻¹ * rationalConjugate k K G σ g ∈ normalizerPoints (T := T_K) (i_K i)) ∧
      ∀ y : D.ReducedBuilding,
        (∃ x : D.Apartment, g₀ • D.apartmentMap x = y) ↔
          ∃ x : D.Apartment, g • D.apartmentMap x = y} :=
  ⟨Classical.choose
      (exists_centralizing_conj_covering_of_descended_torus k K i j D hG hA a
        hi hj f f' hf hf' g₀ e₀ hg₀),
    Classical.choose_spec
      (exists_centralizing_conj_covering_of_descended_torus k K i j D hG hA a
        hi hj f f' hf hf' g₀ e₀ hg₀)⟩

local notation "chosen" =>
  centralizingConjCoveringOfDescendedTorus k K i j D hG hA a
    hi hj f f' hf hf' g₀ e₀ hg₀

/-- The selected representative centralizes the common split subtorus. -/
theorem centralizingConjCoveringOfDescendedTorus_mem_centralizerPoints :
    (chosen).val ∈ centralizerPoints a :=
  (chosen).property.1

/-- Every coefficient difference of the selected representative normalizes the
original descended torus. -/
theorem centralizingConjCoveringOfDescendedTorus_galoisDifference
    (σ : K ≃ₐ[k] K) :
    (chosen).val⁻¹ * rationalConjugate k K G σ (chosen).val ∈
      normalizerPoints (T := T_K) (i_K i) :=
  (chosen).property.2.1 σ

/-- The selected representative covers exactly the original chart's points. -/
theorem centralizingConjCoveringOfDescendedTorus_covering_iff
    (y : D.ReducedBuilding) :
    (∃ x : D.Apartment, g₀ • D.apartmentMap x = y) ↔
      ∃ x : D.Apartment, (chosen).val • D.apartmentMap x = y :=
  (chosen).property.2.2 y

end Choice

end Langlands.Geometry.Building.KPApartmentData
