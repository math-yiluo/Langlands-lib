import Langlands.GroupScheme.CocycleAffineRefinement
import Langlands.GroupScheme.Rational.CentralMuHasseReduction
import Langlands.GroupScheme.Rational.CentralNormOneArchimedeanCorrection
import Langlands.GroupScheme.Rational.NumberFieldNormOneCocycleLift

/-! # Hasse reduction for norm-one torsion central kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Triviality of a cocycle after extending the coefficient field descends to the
original cover by fpqc reflection. -/
theorem Cocycle.IsTrivial.of_fieldRefinement
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E] [Algebra L E]
    [IsScalarTower F L E] {G : GroupScheme (Spec (CommRingCat.of F))}
    {ξ : Cocycle G (GaloisCocycle.cover F L)}
    (h : (ξ.refine (GaloisCocycle.coverMap F L E)).IsTrivial) : ξ.IsTrivial := by
  obtain ⟨hs, hf, hq⟩ := fieldExtension_fpqc F E
  let : Surjective (GaloisCocycle.cover F E).hom := hs
  let : Flat (GaloisCocycle.cover F E).hom := hf
  let : QuasiCompact (GaloisCocycle.cover F E).hom := hq
  exact Cocycle.IsTrivial.of_refine_fpqcCover _ h

namespace IsCentralIsogeny

variable {F L : Type u} [Field F] [NumberField F] [Field L] [Algebra F L]
  {G H : GroupScheme (Spec (CommRingCat.of F))} {f : G ⟶ H} (hf : IsCentralIsogeny f)

/-- The simply connected Hasse kernel turns an archimedean central correction into
triviality of the projected cocycle. -/
theorem isTrivial_map_of_archimedeanCentralCorrection
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u}) (hG : IsSimplyConnected G)
    (ζ : Cocycle G (GaloisCocycle.cover F L)) (h : hf.HasArchimedeanCentralCorrection ζ) :
    (ζ.map f).IsTrivial := by
  obtain ⟨E, _, _, _, _, _, _, α, hα⟩ := h
  let r := GaloisCocycle.coverMap F L E
  let δ := (ζ.refine r).divCentral α (kernelι f) hf.isCentral_kernelι
  have hδ : δ.IsTrivial := hsc F G hG E δ (Cocycle.LocallyTrivial.of_archimedean hG hα)
  obtain ⟨x, hx⟩ := hδ.map f
  apply Cocycle.IsTrivial.of_fieldRefinement (E := E)
  refine ⟨x, fun a b => ?_⟩
  have hp := Cocycle.divCentral_kernel_map_toFun (ζ.refine r) α hf.isCentral_kernelι a b
  exact hp.symm.trans (hx a b)

end IsCentralIsogeny

/-- The Hasse kernel for a target with a simply connected central cover and a
quadratic or coprime degree norm-one torsion kernel. -/
def NumberFieldNormOneKernelHasseStatement : Prop :=
  ∀ (F B : Type u) [Field F] [Field B] [NumberField F] [NumberField B] [Algebra F B]
    (G H : GroupScheme (Spec (CommRingCat.of F))) (f : G ⟶ H), IsSimplyConnected G →
    IsCentralIsogeny f →
    ∀ n : ℕ, 0 < n → Nonempty (kernel f ≅ WeilGm.normOneTorsion F B n) →
      (Module.finrank F B = 2 ∨ (Module.finrank F B).Coprime n) →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle H (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- The simply connected Hasse kernel implies Hasse for every central quotient
with the specified norm-one torsion kernel. -/
theorem numberFieldNormOneKernelHasse_of_simplyConnected
    (hsc : NumberFieldSimplyConnectedGaloisHasseKernelStatement.{u}) :
    NumberFieldNormOneKernelHasseStatement.{u} := by
  rintro F B _ _ _ _ _ G H f hG hf n hn ⟨e⟩ hB L _ _ _ _ ξ hξ
  obtain ⟨E, _, _, _, _, _, _, ζ, hζ⟩ := numberFieldNormOneKernelLifting
    F B L f hf n hn ⟨e⟩ hB ξ hξ
  have hζloc : (ζ.map f).LocallyTrivial := hζ.symm ▸ hξ.refine (GaloisCocycle.coverMap F L E)
  have hc := hf.hasArchimedeanCentralCorrection_of_normOneKernel n hn e hB ζ (fun v => hζloc (.inl v))
  have ht := hf.isTrivial_map_of_archimedeanCentralCorrection hsc hG ζ hc
  rw [hζ] at ht
  exact ht.of_fieldRefinement

end Langlands.GroupScheme
