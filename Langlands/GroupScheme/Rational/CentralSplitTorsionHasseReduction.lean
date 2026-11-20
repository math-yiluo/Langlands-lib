import Langlands.GroupScheme.Rational.CentralNormOneHasseReduction
import Langlands.GroupScheme.Rational.CentralSplitTorsionArchimedeanCorrection

/-! # Hasse reduction for split torsion central kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- The Hasse kernel for the target of a simply connected central cover with a
finite split product of roots-of-unity groups as kernel. -/
def NumberFieldSplitTorsionKernelHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G H : GroupScheme (Spec (CommRingCat.of F))) (f : G ⟶ H), IsSimplyConnected G →
    IsCentralIsogeny f →
    ∀ (I : Type u) [Finite I] (n : I → ℕ), (∀ i, 0 < n i) →
      Nonempty (kernel f ≅ splitRootsOfUnityProduct F n) →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle H (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The simply connected Hasse kernel implies the Hasse kernel for these
split torsion central quotients. -/
theorem numberFieldSplitTorsionKernelHasse_of_simplyConnected
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u}) :
    NumberFieldSplitTorsionKernelHasseStatement.{u} := by
  rintro F _ _ G H f hG hf I _ n hn ⟨e⟩ L _ _ _ _ ξ hξ
  obtain ⟨E, _, _, _, _, _, _, ζ, hζ⟩ :=
    hf.liftsAfterFiniteGaloisRefinement_of_splitRootsKernel n e hn ξ hξ
  have hζloc : (ζ.map f).LocallyTrivial := hζ.symm ▸ hξ.refine (GaloisCocycle.coverMap F L E)
  have hc := hf.hasArchimedeanCentralCorrection_of_splitRootsKernel n e hn ζ (fun v => hζloc (.inl v))
  have ht := hf.isTrivial_map_of_archimedeanCentralCorrection hsc hG ζ hc
  rw [hζ] at ht
  exact ht.of_fieldRefinement

end Langlands.GroupScheme
