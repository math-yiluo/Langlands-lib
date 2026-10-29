import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalComparisonStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPullbackProof
import Langlands.AlgebraicGeometry.Picard.RigidifiedPullbackProofs
import Langlands.AlgebraicGeometry.QuasiSeparatedTestIsoDetectionProof

/-! # Comparison of universal smooth-family parameters

Adapted from Worker 858's conditional comparison prototype, using the published
pullback theorem to obtain the unconditional comparison. -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Universal smooth-family parameters are uniquely isomorphic when the first
parameter is quasi-separated. -/
theorem smoothFamilyUniversalComparison : SmoothFamilyUniversalComparisonStatement.{u} := by
  intro S A P Q _ L M hL hM
  have hcomp := fun {T U V : Over S} (N : RigidifiedFamily A V) (h : T ⟶ U) (k : U ⟶ V) ↦
    RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
      Langlands.SchemeModule.RigidifiedModule.pullbackCoherence N h k
  -- Classify `L` by `M`.
  obtain ⟨k, hk, hkuniq⟩ := hM.2 P
    ⟨RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) L, hL.1⟩
  have hbij : ∀ (T : Over S) [QuasiSeparatedSpace T.left],
      Function.Bijective (fun (g : T ⟶ P) => g ≫ k) := by
    intro T _
    constructor
    · intro g₁ g₂ hg
      have hg' : g₁ ≫ k = g₂ ≫ k := hg
      obtain ⟨h, -, huniq⟩ := hL.2 T
        ⟨RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
          L T g₁, smoothFamilyPullback S A T P g₁ L hL.1⟩
      have e₁ : RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
          (unitSection_comp A) L T g₂ =
          RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A)
          (unitSection_comp A) L T g₁ := by
        have h₁ := hcomp M g₁ k
        have h₂ := hcomp M g₂ k
        rw [hk] at h₁ h₂
        rw [hg'] at h₁
        exact h₂.symm.trans h₁
      exact (huniq g₁ rfl).trans (huniq g₂ e₁).symm
    · intro g
      obtain ⟨h, hh, -⟩ := hL.2 T
        ⟨RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
          M T g, smoothFamilyPullback S A T Q g M hM.1⟩
      obtain ⟨g', -, huniq⟩ := hM.2 T
        ⟨RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A)
          M T g, smoothFamilyPullback S A T Q g M hM.1⟩
      refine ⟨h, ?_⟩
      have h₁ := hcomp M h k
      rw [hk] at h₁
      exact (huniq (h ≫ k) (h₁.trans hh)).trans (huniq g rfl).symm
  have : IsIso k :=
    Langlands.AlgebraicGeometry.quasiSeparatedTestIsoDetection S P Q k hbij
  refine ⟨asIso k, ?_, ?_⟩
  · exact (RigidifiedLineBundle.classifyingMap_eq_iff _ _ _ M L k).1 hk
  · intro e he
    apply Iso.ext
    exact hkuniq e.hom ((RigidifiedLineBundle.classifyingMap_eq_iff _ _ _ M L e.hom).2 he)

end Langlands.AbelianScheme
