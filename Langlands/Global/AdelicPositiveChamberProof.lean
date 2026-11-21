import Langlands.Global.AdelicPositiveChamberStatement
import Langlands.GroupScheme.Rational.LeviRetraction
import Langlands.GroupScheme.Rational.ParabolicRootConeEvaluation
import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.GroupScheme.Rational.RelativeRootsCharacterSpan
import Langlands.GroupScheme.Rational.StandardCocharacterFiniteness
import Langlands.Representation.Plancherel.AmbientCharacterIntertwiningCone

/-! # Nonemptiness of the adelic parabolic positive chamber

The Weyl-induced form represents evaluation on the presentation's defining
split-component cocharacter. Lift the representing vector to a parabolic
character parameter using the rational Levi retraction and scalar extension. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.GroupScheme.ParabolicRootPresentation

open Langlands.Global.AdelicGroupPoints Langlands.LinearAlgebra Langlands.Plancherel

variable {F : Type u} [Field F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}

/-- Restriction from the parabolic to the split component is onto over `ℝ`:
characters of the Levi extend by a retraction, and restriction from the Levi
to its split component is already onto over `ℚ`. -/
private theorem realParameterRestriction_surjective
    (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a) :
    Function.Surjective (realParameterRestriction (F := F) (a ≫ l)) := by
  obtain ⟨_, _, q, _, _, hq, _⟩ := hl.exists_unipotentRadical_retraction
  have hχ : Function.RightInverse (characterRestrict q) (characterRestrict l) := by
    intro χ
    change ((characterRestrict l).comp (characterRestrict q)) χ = χ
    rw [← characterRestrict_comp, hq, characterRestrict_id]
    rfl
  let f := (characterRestrict (a ≫ l)).toIntLinearMap
  have hf : Function.Surjective (f.baseChange ℚ) := by
    change Function.Surjective (rationalCharacterRestrictRat (a ≫ l))
    rw [rationalCharacterRestrictRat_comp]
    exact (ha.rationalCharacterRestrictRat_surjective hl.isConnectedReductive).comp
      (LinearMap.baseChange_surjective ℚ (g := (characterRestrict l).toIntLinearMap)
        hχ.surjective)
  intro v
  obtain ⟨x, hx⟩ := (LinearMap.baseChange_surjective ℝ hf)
    ((rationalRealTensorEquiv (characterLattice A)).symm v)
  refine ⟨rationalRealTensorEquiv (rationalCharacters P) x, ?_⟩
  have hnat := LinearMap.congr_fun (rationalRealTensorEquiv_naturality f) x
  change (rationalRealTensorEquiv (characterLattice A)) ((f.baseChange ℚ).baseChange ℝ x) =
    (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) at hnat
  change (f.baseChange ℝ) (rationalRealTensorEquiv (rationalCharacters P) x) = v
  rw [← hnat, hx, LinearEquiv.apply_symm_apply]

/-- The positive chamber of the actual parabolic presentation contains a
complex character parameter with strictly positive root pairings. -/
theorem exists_zeroRegularParameter [NumberField F] [IsAffineHom G.X.hom]
    (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (hG : IsConnectedReductive G) :
    ∃ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT 0 lam := by
  let : Smooth G.X.hom := hG.smooth
  let : Module.Finite ℤ (characterLattice A) := hA.finite_characterLattice
  let : FiniteDimensional ℝ (RealTorusSpace.Vstar A) :=
    inferInstanceAs (Module.Finite ℝ (ℝ ⊗[ℤ] characterLattice A))
  let B := weylInducedCharacterForm hA hT r.data.f r.data.i
  have hB : B.Nondegenerate := weylInducedCharacterForm_nondegenerate hA hT r.data.f r.data.i
  obtain ⟨v, hv⟩ := (B.toDual hB).surjective r.splitComponentEvaluation
  obtain ⟨y, hy⟩ := realParameterRestriction_surjective
    r.isCompatible.levi r.isCompatible.splitComponent v
  let c : RealCharacterParameter F P →ₗ[ℝ] ComplexCharacterParameter F P :=
    AlgebraTensorModule.map Complex.ofRealCLM.toLinearMap LinearMap.id
  have hc : (parameterRealPart F P).comp c = LinearMap.id := by
    apply AlgebraTensorModule.ext
    intro s χ
    change (s : ℂ).re ⊗ₜ[ℤ] χ = s ⊗ₜ[ℤ] χ
    rw [Complex.ofReal_re]
  have hre : parameterRealPart F P (c y) = y := LinearMap.congr_fun hc y
  refine ⟨c y, ?_⟩
  rintro α ⟨hne, β, hβ, rfl⟩
  have hroot := (r.restrict_positive_eq_zero_or_mem hβ).resolve_left hne
  change 0 < B (realParameterRestriction (a ≫ l) (parameterRealPart F P (c y)))
    ((1 : ℝ) ⊗ₜ[ℤ] (r.data.f ≫ β))
  rw [hre, hy, ← LinearMap.BilinForm.toDual_def hB, hv, r.splitComponentEvaluation_tmul, one_mul]
  exact_mod_cast hroot.2

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Global

/-- Nonemptiness of the positive chamber on the number-field parameter space. -/
theorem positiveChamberNonempty : PositiveChamberNonemptyStatement.{u} := by
  intro F _ _ G P M A _ _ _ p _ l a r _ _ _ hA hT hG
  exact r.exists_zeroRegularParameter hA hT hG

end Langlands.Global
