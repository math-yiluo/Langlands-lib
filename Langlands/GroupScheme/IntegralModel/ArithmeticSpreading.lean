import Langlands.GroupScheme.IntegralModel
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.SmoothSubalgebraDescentProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
import Langlands.Global.AdelicSIntegersColimitProof
import Mathlib.RingTheory.Localization.AsSubring

/-! # Actual smooth affine models over finite S-integer rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Global
open scoped NumberField

namespace Langlands.GroupScheme.IntegralModel.ArithmeticSpreading

variable (F : Type u) [Field F] [NumberField F]

/-- A finite set of coefficients is contained in one actual finite S-integer ring. -/
theorem exists_integer_contains_finset (s : Finset F) :
    ∃ S : Finset (FinitePlace F), (s : Set F) ⊆ (S : Set (FinitePlace F)).integer F := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simp⟩
  | @insert a s _ ih =>
    obtain ⟨S, hS⟩ := ih
    obtain ⟨T, hT⟩ := exists_mem_numberFieldSIntegers F a
    refine ⟨S ∪ T, ?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact numberFieldSIntegers_mono F Finset.subset_union_right hT
    · exact numberFieldSIntegers_mono F Finset.subset_union_left (hS hx)

/-- Every finitely generated integer-coefficient subalgebra embeds into one
actual finite S-integer ring through its original inclusion in the field. -/
theorem exists_integer_contains_subalgebra (T : Subalgebra (𝓞 F) F) (hT : T.FG) :
    ∃ S : Finset (FinitePlace F), T ≤ (S : Set (FinitePlace F)).integer F := by
  obtain ⟨s, hs⟩ := hT
  obtain ⟨S, hS⟩ := exists_integer_contains_finset F s
  exact ⟨S, hs ▸ Algebra.adjoin_le hS⟩

set_option maxHeartbeats 1000000 in
/-- Any supplied smooth affine number-field group has an actual smooth affine
finite-type model over some finite S-integer ring. -/
theorem exists_smoothIntegralModel (G : GroupScheme (Spec (CommRingCat.of F)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    ∃ S : Finset (FinitePlace F),
      ∃ M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G,
        Smooth M.group.X.hom := by
  classical
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨T₀, hT₀, _, _, X₀, f₀, π₀, ha₀, hfp₀, hqc₀, hqs₀, hpb₀⟩ :=
    exists_fg_subalgebra_isPullback_of_isAffine_of_locallyOfFinitePresentation
      (A₀ := 𝓞 F) (R := 𝓞 F) G.X.hom ∅
  let : IsAffine X₀ := ha₀
  let : LocallyOfFinitePresentation f₀ := hfp₀
  let : QuasiCompact f₀ := hqc₀
  let : QuasiSeparated f₀ := hqs₀
  let : IsAffineHom f₀ := inferInstance
  let : Smooth (pullback.snd f₀ (Spec.algebraMap T₀ F)) := by
    rw [← hpb₀.isoPullback_inv_snd]
    infer_instance
  obtain ⟨T₁, hT₁, _, hs₁⟩ :=
    Langlands.AlgebraicGeometry.NoetherianApproximation.smoothSubalgebraDescent
      (A := F) f₀ ∅
  let b₁ := Spec.algebraMap T₀ T₁
  let a₁ := Spec.algebraMap T₁ F
  have hab₁ : a₁ ≫ b₁ = Spec.algebraMap T₀ F := by
    dsimp [a₁, b₁, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let f₁ := pullback.snd f₀ b₁
  let : Smooth f₁ := hs₁
  let : IsAffineHom f₁ := inferInstance
  let : QuasiCompact f₁ := inferInstance
  let : QuasiSeparated f₁ := inferInstance
  let : LocallyOfFinitePresentation f₁ := inferInstance
  have hright₁ : IsPullback (pullback.fst f₀ b₁) f₁ f₀ b₁ :=
    IsPullback.of_hasPullback f₀ b₁
  have houter₁ : IsPullback π₀ G.X.hom f₀ (a₁ ≫ b₁) := hab₁.symm ▸ hpb₀
  let π₁ := hright₁.lift π₀ (G.X.hom ≫ a₁)
    (by simpa only [Category.assoc] using houter₁.w)
  have hpb₁ : IsPullback π₁ G.X.hom f₁ a₁ := houter₁.of_right' hright₁
  obtain ⟨T₂, hT₂, _, G₀, _, hpb₂, _, ⟨e⟩⟩ :=
    Langlands.GroupScheme.subalgebraDescent f₁ G π₁ hpb₁ ∅
  let : Smooth G₀.X.hom := MorphismProperty.of_isPullback hpb₂ hs₁
  let : IsAffineHom G₀.X.hom :=
    MorphismProperty.of_isPullback hpb₂ (inferInstance : IsAffineHom f₁)
  let : Algebra.FiniteType (𝓞 F) T₀ := T₀.fg_iff_finiteType.mp hT₀
  let : Algebra.FiniteType T₀ T₁ := T₁.fg_iff_finiteType.mp hT₁
  let : Algebra.FiniteType T₁ T₂ := T₂.fg_iff_finiteType.mp hT₂
  let : Algebra.FiniteType (𝓞 F) T₁ := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType (𝓞 F) T₀)
    (inferInstance : Algebra.FiniteType T₀ T₁)
  let : Algebra.FiniteType (𝓞 F) T₂ := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType (𝓞 F) T₁)
    (inferInstance : Algebra.FiniteType T₁ T₂)
  let T : Subalgebra (𝓞 F) F := T₂.restrictScalars (𝓞 F)
  have hT : T.FG := by
    apply T.fg_iff_finiteType.mpr
    let q : T₂ →ₐ[𝓞 F] T :=
      { toFun := fun x => x
        map_zero' := rfl
        map_one' := rfl
        map_add' := fun _ _ => rfl
        map_mul' := fun _ _ => rfl
        commutes' := fun r => by
          apply Subtype.ext
          exact (IsScalarTower.algebraMap_apply (𝓞 F) T₂ F r).symm }
    exact Algebra.FiniteType.of_surjective q (fun x => ⟨x, rfl⟩)
  obtain ⟨S, hS⟩ := exists_integer_contains_subalgebra F T hT
  let R : Type u := (S : Set (FinitePlace F)).integer F
  let i : CommRingCat.of T₂ ⟶ CommRingCat.of R := CommRingCat.ofHom
    { toFun := fun x => ⟨x.val, hS x.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let b := Spec.map i
  let a := Spec.algebraMap R F
  have hab : a ≫ b = Spec.algebraMap T₂ F := by
    dsimp [a, b, i, Spec.algebraMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let H := (baseChange b).obj G₀
  let : Smooth H.X.hom := by
    change Smooth (pullback.snd G₀.X.hom b)
    infer_instance
  let : IsAffineHom H.X.hom := by
    change IsAffineHom (pullback.snd G₀.X.hom b)
    infer_instance
  let M : IntegralModel R F G :=
    { group := H
      genericIso := (baseChangeCompIso b a G₀).symm ≪≫
        eqToIso (congrArg (fun q => (baseChange q).obj G₀) hab) ≪≫ e.symm }
  exact ⟨S, M, inferInstance⟩

/-- A choice of actual smooth integral model together with its finite set of places. -/
def smoothIntegralModelData (G : GroupScheme (Spec (CommRingCat.of F)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    Σ S : Finset (FinitePlace F),
      { M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G //
        Smooth M.group.X.hom } :=
  let h := exists_smoothIntegralModel F G
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

end Langlands.GroupScheme.IntegralModel.ArithmeticSpreading
