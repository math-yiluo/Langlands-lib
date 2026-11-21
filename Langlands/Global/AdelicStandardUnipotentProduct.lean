import Langlands.GroupScheme.Rational.StandardRestrictedConjugation
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction
import Langlands.GroupScheme.Rational.StandardParabolicOrderProof
import Langlands.GroupScheme.Rational.StandardParabolicOrderReduction
import Langlands.GroupScheme.Rational.StandardCocharacterProof

/-! # Products of standard unipotent radicals

For standard index sets `J, K ⊆ Δ₀`, the standard unipotent radical of `J ∩ K` is the product
`U_J · U_K` on every test scheme. -/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Global.StandardConstantTerm

open Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- The sum of standard cocharacters for `J` and `K` is standard for `J ∩ K`. -/
theorem isStandardCocharacter_add_inter {J K : Set (characterLattice T)}
    {ζ ξ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν J ζ)
    (hξ : IsStandardCocharacter i ν K ξ) : IsStandardCocharacter i ν (J ∩ K) (ζ + ξ) := by
  refine ⟨fun α hα => hζ.1 hα.1, ?_, ?_⟩
  · intro α hα
    simp only [map_add, hζ.2.1 α hα.1, hξ.2.1 α hα.2, add_zero]
  · intro α hα hαJK
    simp only [map_add]
    by_cases hαJ : α ∈ J
    · have hαK : α ∉ K := fun h => hαJK ⟨hαJ, h⟩
      exact add_pos_of_nonneg_of_pos (hζ.nonneg i ν hα) (hξ.2.2 α hα hαK)
    · exact add_pos_of_pos_of_nonneg (hζ.2.2 α hα hαJ) (hξ.nonneg i ν hα)

/-- Inside the standard Levi `L_K`, the standard unipotent radical of `J ∩ K` lies in `U_J`,
provided `K` has a standard cocharacter. -/
theorem standardLevi_inf_standardUnipotent_inter_le {J K : Set (characterLattice T)}
    {ξ : cocharacterLattice T} (hξ : IsStandardCocharacter i ν K ξ) :
    standardLevi i ν K ⊓ standardUnipotent i ν (J ∩ K) ≤ standardUnipotent i ν J := by
  intro S g hg
  obtain ⟨hgL, hgU⟩ := hg
  change g ∈ (standardUnipotent i ν J).carrier S
  refine (mem_standardUnipotent i ν).mpr fun ζ hζ => ?_
  have h1 := (mem_standardUnipotent i ν).mp hgU (ζ + ξ) (isStandardCocharacter_add_inter i ν hζ hξ)
  have hc := (mem_standardLevi i ν).mp hgL ξ hξ
  exact (Dynamic.mem_unipotent_add_iff_of_mem_centralizer i ζ ξ g hc).mp h1

/-- **Product decomposition.** For `J, K ⊆ Δ₀`, on every test scheme every point of `U_{J ∩ K}`
is a point of `U_J` times a point of `U_K`. -/
theorem standardUnipotent_inter_subset_mul (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν) {J K : Set (characterLattice T)}
    (hJ : J ⊆ simpleRelativeRoots i ν) (hK : K ⊆ simpleRelativeRoots i ν)
    (S : Over (Spec (CommRingCat.of k))) :
    (↑((standardUnipotent i ν (J ∩ K)).carrier S) : Set (S ⟶ G.X)) ⊆
      (↑((standardUnipotent i ν J).carrier S) : Set (S ⟶ G.X)) *
        (↑((standardUnipotent i ν K).carrier S) : Set (S ⟶ G.X)) := by
  obtain ⟨⟨ξ, hξ⟩, heq⟩ := standardCocharacter k G hG T i hi ν hν K hK
  have hreal : StandardLeviIntersection.IsRealizingStandardCocharacter i ν K ξ :=
    ⟨hξ, (heq ξ hξ).2.1 ▸ le_rfl, (heq ξ hξ).2.2 ▸ le_rfl⟩
  have hord := (standardParabolicOrder k G hG T i hi ν hν).1 (J ∩ K) K
    (Set.inter_subset_left.trans hJ) hK
  have hPar := hord.1.mp Set.inter_subset_right
  have hUni := (hord.2 Set.inter_subset_right).2
  rw [StandardLeviIntersection.standardUnipotent_eq_leviInter_mul i ν hreal hPar hUni S]
  refine Set.mul_subset_mul_right fun g hg => ?_
  exact standardLevi_inf_standardUnipotent_inter_le i ν hξ S hg

/-- **Statement form.** For connected reductive `G` over a field, a maximal split torus `i`, a
generic cocharacter `ν` and `J, K ⊆ Δ₀`, on every test scheme each point of `U_{J ∩ K}` is the
product of a point of `U_J` and a point of `U_K`. -/
def StandardUnipotentProductStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T),
    IsConnectedReductive G → IsMaximalSplitTorus i → IsGenericCocharacter i ν →
    ∀ (J K : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
      K ⊆ simpleRelativeRoots i ν → ∀ S : Over (Spec (CommRingCat.of k)),
      (↑((standardUnipotent i ν (J ∩ K)).carrier S) : Set (S ⟶ G.X)) ⊆
        (↑((standardUnipotent i ν J).carrier S) : Set (S ⟶ G.X)) *
          (↑((standardUnipotent i ν K).carrier S) : Set (S ⟶ G.X))

/-- Proof of `StandardUnipotentProductStatement`. -/
theorem standardUnipotentProduct : StandardUnipotentProductStatement.{u} := by
  intro k _ G _ T i ν hG hi hν J K hJ hK S
  exact standardUnipotent_inter_subset_mul i ν hG hi hν hJ hK S

end Langlands.Global.StandardConstantTerm
