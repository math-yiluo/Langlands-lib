import Langlands.Representation.Whittaker.DistributionInvarianceStatement
import Langlands.Representation.Whittaker.BruhatCellVanishingProof
import Langlands.Representation.Whittaker.BruhatCellInvarianceProof
import Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingProof
import Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof

/-!
# Shalika invariance of Whittaker bi-equivariant distributions

The difference of a distribution and its Weyl-transpose pushforward is
bi-equivariant and anti-invariant. Public cell vanishing and cell invariance,
transported by the public one-cell restriction theorem, give the open
restrictions required by public finite-filtration vanishing. The difference
is therefore zero. See the paired Markdown for the proof and its provenance.
-/

noncomputable section

namespace Langlands.Whittaker.DistributionInvarianceProof

open GeneralLinear HarmonicAnalysis HarmonicAnalysis.Distribution Hecke.TestFunction

universe u

variable (n : ℕ) (R : Type u) [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

private theorem pullback_transpose_biTranslate
    (u₁ u₂ : upperUnipotent (n + 1) R)
    (f : SchwartzBruhat (GeneralLinear (n + 1) R)) :
    pullback (weylTransposeHomeomorph n R)
        (pullback ((Homeomorph.mulLeft u₁.val).trans (Homeomorph.mulRight u₂.val)) f) =
      pullback
        ((Homeomorph.mulLeft (weylTransposeUnipotent n R u₂).val).trans
          (Homeomorph.mulRight (weylTransposeUnipotent n R u₁).val))
        (pullback (weylTransposeHomeomorph n R) f) := by
  ext g
  change f (u₁.val * weylTransposeHomeomorph n R g * u₂.val) =
    f (weylTransposeHomeomorph n R
      ((weylTransposeUnipotent n R u₂).val * g *
        (weylTransposeUnipotent n R u₁).val))
  simp only [weylTransposeHomeomorph_mul, weylTransposeUnipotent_val,
    weylTransposeHomeomorph_involutive, mul_assoc]

private theorem biEquivariant_pushforward (ψ : UnitaryAdditiveCharacter R)
    (D : Distribution (GeneralLinear (n + 1) R))
    (hD : IsBiEquivariantDistribution ψ n D) :
    IsBiEquivariantDistribution ψ n (pushforward (weylTransposeHomeomorph n R) D) := by
  apply (isBiEquivariantDistribution_iff n R ψ _).mpr
  intro u₁ u₂ f
  change D (pullback (weylTransposeHomeomorph n R)
      (pullback ((Homeomorph.mulLeft u₁.val).trans (Homeomorph.mulRight u₂.val)) f)) =
    ((standardCharacter ψ n u₁ : ℂ) * (standardCharacter ψ n u₂ : ℂ)) *
      D (pullback (weylTransposeHomeomorph n R) f)
  rw [pullback_transpose_biTranslate]
  have h := (isBiEquivariantDistribution_iff n R ψ D).mp hD
    (weylTransposeUnipotent n R u₂) (weylTransposeUnipotent n R u₁)
    (pullback (weylTransposeHomeomorph n R) f)
  simpa only [standardCharacter_weylTranspose, mul_comm] using h

private theorem biEquivariant_sub (ψ : UnitaryAdditiveCharacter R)
    (D E : Distribution (GeneralLinear (n + 1) R))
    (hD : IsBiEquivariantDistribution ψ n D)
    (hE : IsBiEquivariantDistribution ψ n E) :
    IsBiEquivariantDistribution ψ n (D - E) := by
  intro u₁ u₂ f
  change D _ - E _ = _ * (D f - E f)
  rw [hD, hE, mul_sub]

private theorem antiInvariant_difference (D : Distribution (GeneralLinear (n + 1) R)) :
    pushforward (weylTransposeHomeomorph n R)
      (D - pushforward (weylTransposeHomeomorph n R) D) =
        -(D - pushforward (weylTransposeHomeomorph n R) D) := by
  rw [map_sub, pushforward_weylTranspose_involutive, neg_sub]

private theorem biEquivariant_difference (ψ : UnitaryAdditiveCharacter R)
    (D : Distribution (GeneralLinear (n + 1) R))
    (hD : IsBiEquivariantDistribution ψ n D) :
    IsBiEquivariantDistribution ψ n
      (D - pushforward (weylTransposeHomeomorph n R) D) :=
  biEquivariant_sub n R ψ D _ hD (biEquivariant_pushforward n R ψ D hD)

private theorem invariance_of_difference_zero (D : Distribution (GeneralLinear (n + 1) R))
    (hD : D - pushforward (weylTransposeHomeomorph n R) D = 0) :
    IsWeylTransposeInvariant n R D :=
  (sub_eq_zero.mp hD).symm

end Langlands.Whittaker.DistributionInvarianceProof

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis HarmonicAnalysis.Distribution

universe uF

/-- Every Whittaker bi-equivariant algebraic distribution on a positive-rank
p-adic general linear group is invariant under Weyl-conjugated transpose. -/
theorem shalikaDistributionInvariance : ShalikaDistributionInvarianceStatement.{uF} := by
  classical
  intro p hp F
  let := F.canonicalNormedField
  intro n ψ D hD
  have : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
  have : IsUltrametricDist F.Carrier :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
      (isNonarchimedean_spectralNorm (K := Padic p) (L := F.Carrier))
  have : TotallyDisconnectedSpace (GeneralLinear (n + 1) F.Carrier) := by
    have : TotallyDisconnectedSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
      inferInstanceAs (TotallyDisconnectedSpace (Fin (n + 1) → Fin (n + 1) → F.Carrier))
    exact ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  let E := D - pushforward (weylTransposeHomeomorph n F.Carrier) D
  have hEbi : IsBiEquivariantDistribution ψ n E :=
    DistributionInvarianceProof.biEquivariant_difference n F.Carrier ψ D hD
  have hEanti : pushforward (weylTransposeHomeomorph n F.Carrier) E = -E :=
    DistributionInvarianceProof.antiInvariant_difference n F.Carrier D
  have hEzero : E = 0 := by
    apply bruhatFiltrationVanishing (n + 1) F.Carrier E
    intro w hw
    apply bruhatCellRestrictionVanishing n F.Carrier w ψ
      ⟨E, hw⟩ hEbi hEanti
    by_cases hnon : (compatibleTorus ψ n w).Nonempty
    · exact Or.inr (bruhatCellInvariance p hp F n ψ w hnon)
    · exact Or.inl (bruhatCellVanishing p hp F n ψ w hnon)
  exact DistributionInvarianceProof.invariance_of_difference_zero n F.Carrier D hEzero

end Langlands.Whittaker
