import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.Representation.Plancherel.AmbientCharacterIntertwiningCone
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Open nonempty regions of regular Eisenstein parameters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Langlands.Global.AdelicGroupPoints Langlands.Plancherel Langlands.LinearAlgebra

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)

private theorem finite_unipotentRoots (hT : IsSplitTorus r.data.T.toGrp) :
    r.unipotentRoots.Finite :=
  ((hT.finite_positiveRelativeRoots r.data.i r.data.ν).image (r.data.f ≫ ·)).subset
    (fun _ h => h.2)

variable
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- The strict inequalities that define regular parameters give an open
region in every complex linear chart. -/
theorem isOpen_regularParameter_inCoordinates (R : ℝ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) :
    IsOpen {x | r.IsRegularParameter hA hT R (e x)} := by
  let : Finite r.unipotentRoots := (r.finite_unipotentRoots hT).to_subtype
  let B := weylInducedCharacterForm hA hT r.data.f r.data.i
  let L (α : characterLattice A) : (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    (B.flip ((1 : ℝ) ⊗ₜ[ℤ] α)).comp
      ((realParameterRestriction (a ≫ l)).comp
        ((parameterRealPart F P).comp (e.toLinearMap.restrictScalars ℝ)))
  have heq : {x | r.IsRegularParameter hA hT R (e x)} =
      ⋂ α : r.unipotentRoots, {x | R < L α x} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, Subtype.forall]
    rfl
  rw [heq]
  exact isOpen_iInter_of_finite (fun α => isOpen_lt continuous_const
    (L α).continuous_of_finiteDimensional)

private theorem parameterRealPart_surjective :
    Function.Surjective (parameterRealPart F P) := by
  let f : RealCharacterParameter F P →ₗ[ℝ] ComplexCharacterParameter F P :=
    AlgebraTensorModule.map Complex.ofRealCLM.toLinearMap LinearMap.id
  have hf : (parameterRealPart F P).comp f = LinearMap.id := by
    apply AlgebraTensorModule.ext
    intro s χ
    change (s : ℂ).re ⊗ₜ[ℤ] χ = s ⊗ₜ[ℤ] χ
    rw [Complex.ofReal_re]
  exact fun y => ⟨f y, LinearMap.congr_fun hf y⟩

private theorem realParameterRestriction_surjective
    (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a) :
    Function.Surjective (realParameterRestriction (F := F) (a ≫ l)) := by
  let f := (characterRestrict (a ≫ l)).toIntLinearMap
  have hf : Function.Surjective (f.baseChange ℚ) := by
    have hs₁ := LinearMap.baseChange_surjective ℚ
      (g := (characterRestrict l).toIntLinearMap) hl.characterRestrict_bijective.surjective
    have hs₂ := ha.rationalCharacterRestrictRat_surjective hl.isConnectedReductive
    change Function.Surjective (((characterRestrict (a ≫ l)).toIntLinearMap).baseChange ℚ)
    rw [characterRestrict_comp]
    change Function.Surjective (((characterRestrict a).toIntLinearMap.comp
      (characterRestrict l).toIntLinearMap).baseChange ℚ)
    rw [LinearMap.baseChange_comp]
    exact hs₂.comp hs₁
  intro y
  obtain ⟨x, hx⟩ := (LinearMap.baseChange_surjective ℝ hf)
    ((rationalRealTensorEquiv (characterLattice A)).symm y)
  refine ⟨rationalRealTensorEquiv (rationalCharacters P) x, ?_⟩
  have hnat := LinearMap.congr_fun (rationalRealTensorEquiv_naturality f) x
  change (rationalRealTensorEquiv (characterLattice A)) ((f.baseChange ℚ).baseChange ℝ x) =
    (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) at hnat
  change (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) = y
  rw [← hnat, hx, LinearEquiv.apply_symm_apply]

/-- Each regularity threshold is achieved by a complex character parameter. -/
theorem exists_regularParameter (R : ℝ) :
    ∃ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R lam := by
  let : Module.Finite ℤ (characterLattice A) := hA.finite_characterLattice
  let : FiniteDimensional ℝ (RealTorusSpace.Vstar A) :=
    inferInstanceAs (Module.Finite ℝ (ℝ ⊗[ℤ] characterLattice A))
  let B := weylInducedCharacterForm hA hT r.data.f r.data.i
  have hB : B.Nondegenerate :=
    weylInducedCharacterForm_nondegenerate hA hT r.data.f r.data.i
  let s := max R 0 + 1
  obtain ⟨v, hv⟩ := (B.toDual hB).surjective (s • r.splitComponentEvaluation)
  obtain ⟨u, hu⟩ := realParameterRestriction_surjective
    r.isCompatible.levi r.isCompatible.splitComponent v
  obtain ⟨lam, hlam⟩ := parameterRealPart_surjective u
  refine ⟨lam, ?_⟩
  rintro α ⟨hne, β, hβ, rfl⟩
  have hroot := (r.restrict_positive_eq_zero_or_mem hβ).resolve_left hne
  have hone : (1 : ℤ) ≤ latticePairing A (r.data.f ≫ β) r.splitComponentCocharacter := by
    have hpos := hroot.2
    omega
  have hone' : (1 : ℝ) ≤ latticePairing A (r.data.f ≫ β) r.splitComponentCocharacter := by
    exact_mod_cast hone
  have hs : 0 ≤ s := (le_max_right R 0).trans (le_add_of_nonneg_right zero_le_one)
  change R < B (realParameterRestriction (a ≫ l) (parameterRealPart F P lam))
    ((1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ β))
  rw [hlam, hu, ← LinearMap.BilinForm.toDual_def hB, hv, LinearMap.smul_apply,
    r.splitComponentEvaluation_tmul, one_mul, smul_eq_mul]
  calc
    R < s := (le_max_left R 0).trans_lt (lt_add_of_pos_right _ zero_lt_one)
    _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hone' hs

/-- The regular region is nonempty in any specified chart. -/
theorem nonempty_regularParameter_inCoordinates (R : ℝ) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) :
    {x | r.IsRegularParameter hA hT R (e x)}.Nonempty := by
  obtain ⟨lam, hlam⟩ := r.exists_regularParameter hA hT R
  exact ⟨e.symm lam, by simpa using hlam⟩

end Langlands.GroupScheme.ParabolicRootPresentation
