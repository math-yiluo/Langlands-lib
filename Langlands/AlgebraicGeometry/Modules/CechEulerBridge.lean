import Langlands.AlgebraicGeometry.Modules.CechHSuccBridge
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le

/-! # Čech Euler characteristics in the FLT port and actual Euler characteristics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.CechBridge

variable {R : CommRingCat.{u}} {X : Scheme.{u}} {π : X ⟶ Spec R}

/-- The FLT Čech group `H0` is the homology of the Čech complex in degree `0`. -/
def homologyZeroEquiv (F : OModulePresheaf π) (K : X.OrderedAffineCover) :
    (cechComplex F K).homology 0 ≃ₗ[R] F.H0 K := by
  let C := cechComplex F K
  have h00 : C.d 0 0 = 0 := C.shape 0 0 (by simp)
  let S := ModuleCat.shortComplexOfCompEqZero (0 : F.cochain K 0 →ₗ[R] F.cochain K 0) (F.d K 0)
    (by simp)
  let e : C.sc' 0 0 1 ≅ S :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        simp only [Iso.refl_hom]
        change C.d 0 0 ≫ 𝟙 _ = 𝟙 _ ≫ ModuleCat.ofHom 0
        rw [h00]
        rfl)
      (by simp only [Iso.refl_hom]; exact (cechComplex_d F K 0).symm)
  exact (C.homologyIsoSc' 0 0 1 (by simp) (by simp) ≪≫ ShortComplex.homologyMapIso e ≪≫
    S.moduleCatHomologyIso).toLinearEquiv ≪≫ₗ
      Submodule.quotEquivOfEqBot _ (by
        rw [eq_bot_iff]
        rintro x ⟨y, rfl⟩
        apply Subtype.ext
        rfl)

/-- For an invertible module, the FLT Čech `H0` is the actual cohomology in degree `0`. -/
def h0EquivRelativeCohomology [IsSeparated π] (K : X.OrderedAffineCover) (M : X.Modules)
    [M.IsQuasicoherent] :
    (OModulePresheaf.ofModules π M).H0 K ≃ₗ[R] (DerivedSections.relativeCohomology π 0).obj M :=
  (homologyZeroEquiv (OModulePresheaf.ofModules π M) K).symm ≪≫ₗ
    (CechResolution.cechCohomologyIso π K M 0).toLinearEquiv

/-- The FLT Čech Euler characteristic of a quasi-coherent module on a separated scheme is the
alternating sum of the dimensions of its actual cohomology. -/
theorem eulerChar_ofModules_eq [Nontrivial R] [IsSeparated π] (K : X.OrderedAffineCover)
    (M : X.Modules) [M.IsQuasicoherent] :
    (OModulePresheaf.ofModules π M).eulerChar K =
      ∑ᶠ p : ℕ, (-1 : ℤ) ^ p *
        (Module.finrank R ((DerivedSections.relativeCohomology π p).obj M) : ℤ) := by
  obtain ⟨-, hcoch, hsucc, -⟩ :=
    (OModulePresheaf.ofModules π M).subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le K
  rw [OModulePresheaf.eulerChar_def,
    finsum_eq_sum_of_support_subset _ (s := Finset.range (Fintype.card K.ι)) ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    cases i with
    | zero =>
      rw [OModulePresheaf.cechFinrank_zero]
      exact (h0EquivRelativeCohomology K M).finrank_eq
    | succ i =>
      rw [OModulePresheaf.cechFinrank_succ]
      exact (hsuccEquivRelativeCohomology K M i).finrank_eq
  · intro p hp
    rw [Function.mem_support] at hp
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcard
    apply hp
    cases p with
    | zero =>
      have : Subsingleton ((OModulePresheaf.ofModules π M).cochain K 0) := hcoch 0 (by omega)
      have : Subsingleton ((OModulePresheaf.ofModules π M).H0 K) := inferInstance
      rw [← (h0EquivRelativeCohomology K M).finrank_eq,
        Module.finrank_zero_of_subsingleton]
      simp
    | succ i =>
      have : Subsingleton ((OModulePresheaf.ofModules π M).HSucc K i) := hsucc i (by omega)
      rw [← (hsuccEquivRelativeCohomology K M i).finrank_eq,
        Module.finrank_zero_of_subsingleton]
      simp

end Langlands.AlgebraicGeometry.Modules.CechBridge
