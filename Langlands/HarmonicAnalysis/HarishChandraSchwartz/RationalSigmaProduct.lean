import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalTemperedInduction
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound

/-! # Waldspurger's Lemma II.3.1 on actual rational points

The bound on the height of a Levi projection gives the lower product-height bound for
every actual standard parabolic. No compact subgroup or Cartan decomposition is needed.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Abstract

variable {H : Type*} [Group H] {M U : Subgroup H}

/-- An additive bound on the height of the Levi factor gives the second inequality
of Waldspurger's Lemma II.3.1. -/
theorem sigmaProductBound_of_le_add_mul {σ : H → ℝ}
    (hσ : ∀ g, 0 ≤ σ g)
    (hsub : ∀ g h, σ (g * h) ≤ σ g + σ h)
    (hinv : ∀ g, σ g⁻¹ = σ g)
    {c : ℝ} (hc : 0 ≤ c)
    (hproj : ∀ m : M, ∀ u : U, σ m ≤ c + σ ((m : H) * u)) :
    SigmaProductBound M U σ := by
  have hc2 : 0 < c + 2 := by linarith
  refine ⟨(c + 2)⁻¹, inv_pos.mpr hc2, fun m u => ?_⟩
  have hm := hproj m u
  have hu : σ u ≤ c + 2 * σ ((m : H) * u) := by
    have h := hsub (m : H)⁻¹ ((m : H) * u)
    rw [inv_mul_cancel_left, hinv] at h
    linarith
  have ht := hσ ((m : H) * u)
  have hmax : max (σ m) (σ u) ≤ c + 2 * σ ((m : H) * u) :=
    max_le (by linarith) hu
  rw [inv_mul_eq_div, div_le_iff₀ hc2]
  nlinarith

end Abstract

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {i : S.toGrp ⟶ G} {ν : cocharacterLattice S} {J : Set (characterLattice S)}

/-- **Waldspurger, Lemma II.3.1, second inequality**, for actual standard parabolic
points and any closed matrix representation defining the logarithmic height. -/
theorem rationalSigmaProductBound (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hν : IsGenericCocharacter i ν)
    (hJ : J ⊆ simpleRelativeRoots i ν)
    {N : ℕ} [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N))
    (hρ : IsClosedSubgroup ρ) :
    SigmaProductBound (standardLeviPoints i ν J) (standardUnipotentPoints i ν J)
      (rationalHeight (F := F) ρ) := by
  obtain ⟨c, hc, hproj⟩ := exists_rationalHeight_projection_le ρ hG hi hν hJ hρ
  refine sigmaProductBound_of_le_add_mul (rationalHeight_nonneg ρ)
    (rationalHeight_mul_le ρ) (rationalHeight_inv ρ) hc fun m u => ?_
  let h := isSemidirectDecomposition_standard hG hi hν hJ
  have hp := hproj
    ((⟨m, h.levi_le m.2⟩ : standardParabolicPoints i ν J) *
      ⟨u, h.unipotent_le u.2⟩)
  rw [h.projection_mul] at hp
  exact hp

/-- Actual-point form of the inequality from Lemma II.3.1 used in Proposition II.4.5.
The compact and Cartan assumptions of that proposition are unnecessary here. -/
def RationalSigmaProductStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ ν : cocharacterLattice S, IsGenericCocharacter i ν →
    ∀ J : Set (characterLattice S), J ⊆ simpleRelativeRoots i ν →
    ∀ (N : ℕ) [Nonempty (Fin N)] (ρ : MatrixRepresentation G (Fin N)),
      IsClosedSubgroup ρ →
        SigmaProductBound (standardLeviPoints i ν J) (standardUnipotentPoints i ν J)
          (rationalHeight (F := F) ρ)

/-- Waldspurger's lower product-height bound on actual rational points. -/
theorem rationalSigmaProduct : RationalSigmaProductStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν J hJ N _ ρ hρ
  exact rationalSigmaProductBound hG hi hν hJ ρ hρ

end Langlands.HarishChandraSchwartz
