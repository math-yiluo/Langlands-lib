import Langlands.GroupScheme.Rational.CentralNormOneHasseReduction
import Langlands.GroupScheme.Rational.CentralWeilTorsionArchimedeanCorrection

/-! # Hasse reduction for central kernels of Weil torsion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- The Hasse kernel for the target of a simply connected central cover whose
kernel is torsion in a Weil multiplicative group of a number field extension. -/
def NumberFieldWeilTorsionKernelHasseStatement : Prop :=
  ∀ (F B : Type u) [Field F] [Field B] [NumberField F] [NumberField B] [Algebra F B]
    (G H : GroupScheme (Spec (CommRingCat.of F))) (f : G ⟶ H), IsSimplyConnected G →
    IsCentralIsogeny f →
    ∀ n : ℕ, 0 < n → Nonempty (kernel f ≅ WeilGm.weilTorsion F B n) →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle H (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The simply connected Hasse kernel implies Hasse for these Weil torsion quotients. -/
theorem numberFieldWeilTorsionKernelHasse_of_simplyConnected
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u}) :
    NumberFieldWeilTorsionKernelHasseStatement.{u} := by
  rintro F B _ _ _ _ _ G H f hG hf n hn ⟨e⟩ L _ _ _ _ ξ hξ
  obtain ⟨E, _, _, _, _, _, _, ζ, hζ⟩ :=
    IsCentralIsogeny.liftsAfterFiniteGaloisRefinement_of_weilTorsionKernel n e hf hn ξ hξ
  have hζloc : (ζ.map f).LocallyTrivial := hζ.symm ▸ hξ.refine (GaloisCocycle.coverMap F L E)
  have hc := hf.hasArchimedeanCentralCorrection_of_weilTorsionKernel n e hn ζ (fun v => hζloc (.inl v))
  have ht := hf.isTrivial_map_of_archimedeanCentralCorrection hsc hG ζ hc
  rw [hζ] at ht
  exact ht.of_fieldRefinement

end Langlands.GroupScheme
