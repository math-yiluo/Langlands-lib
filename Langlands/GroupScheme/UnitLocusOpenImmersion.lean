import Langlands.GroupScheme.Reductive.LocalRankOneUnitCell

/-! # Open immersions onto the unit locus of a global function -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.UnitLocus

variable {S : Scheme.{u}} {X Y : Over S}

/-- **Open immersion criterion through a unit locus.** A monomorphism `f : X ⟶ Y` of schemes
over `S` is an open immersion if some global function `g` of `Y` pulls back to a unit on `X` and
every point of `Y` at which `g` is a unit factors through `f`. Then `f` identifies `X` with the
basic open subscheme `D(g)` of `Y`. -/
theorem isOpenImmersion_of_unitLocus (f : X ⟶ Y) [Mono f] (g : Γ(Y.left, ⊤))
    (hunit : IsUnit (f.left.appTop g))
    (hex : ∀ (Z : Over S) (y : Z ⟶ Y), IsUnit (y.left.appTop g) → ∃ x : Z ⟶ X, x ≫ f = y) :
    IsOpenImmersion f.left := by
  let U := Y.left.basicOpen g
  let Z : Over S := Over.mk (U.ι ≫ Y.hom)
  let y : Z ⟶ Y := Over.homMk U.ι rfl
  have hyU : IsUnit (y.left.appTop g) := by
    apply LocalRankOneUnitCell.isUnit_appTop_of_range_subset_basicOpen
    change Set.range U.ι ⊆ _
    rw [Scheme.Opens.range_ι]
  obtain ⟨x, hx⟩ := hex Z y hyU
  have hrange : Set.range f.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have h : f.left ⁻¹ᵁ Y.left.basicOpen g = ⊤ := by
      rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hunit]
    have hp : p ∈ f.left ⁻¹ᵁ Y.left.basicOpen g := by rw [h]; trivial
    exact hp
  let l : X ⟶ Z := Over.homMk (IsOpenImmersion.lift U.ι f.left hrange) (by
    change IsOpenImmersion.lift U.ι f.left hrange ≫ U.ι ≫ Y.hom = X.hom
    rw [IsOpenImmersion.lift_fac_assoc, Over.w f])
  have hl : l ≫ y = f := by
    ext
    exact IsOpenImmersion.lift_fac _ _ _
  have : Mono y := by
    have : Mono y.left := (inferInstance : Mono U.ι)
    exact Over.mono_of_mono_left y
  have h1 : x ≫ l = 𝟙 Z := by
    rw [← cancel_mono y, Category.assoc, hl, hx, Category.id_comp]
  have h2 : l ≫ x = 𝟙 X := by
    rw [← cancel_mono f, Category.assoc, hx, hl, Category.id_comp]
  have : IsIso l := ⟨⟨x, h2, h1⟩⟩
  have : IsIso l.left := (inferInstance : IsIso ((Over.forget S).map l))
  have hf : f.left = l.left ≫ U.ι := congrArg CommaMorphism.left hl.symm
  rw [hf]
  infer_instance

end Langlands.GroupScheme.UnitLocus
