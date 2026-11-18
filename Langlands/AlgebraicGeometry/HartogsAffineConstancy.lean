import Langlands.AlgebraicGeometry.FactorialHartogsExtension
import Langlands.AlgebraicGeometry.ProperConnectedAffineConstancy
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Affine-valued maps on a proper integral scheme minus a factorial point -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.HartogsAffineConstancy

open FactorialHartogsExtension

variable {X : Scheme.{u}} [IsIntegral X]

/-- On an integral scheme, restriction of global functions to a nonempty open is injective. -/
theorem restrict_injective {W : X.Opens} {y : X} (hy : y ∈ W) :
    Function.Injective (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) := by
  intro a b h
  have hg : genericPoint X ∈ W := genericPoint_mem hy
  apply germ_injective_of_isIntegral X (genericPoint X) (show genericPoint X ∈ (⊤ : X.Opens) from
    trivial)
  have h' := congrArg (X.presheaf.germ W (genericPoint X) hg) h
  rwa [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h'

/-- **Hartogs constancy.** Let `X` be a proper integral scheme over an algebraically closed
field `k`, `z` a point with factorial stalk and a chain `y₀ ⤳ y₁ ⤳ z` of proper
generizations, and `W` the complement of `z`. Then every morphism from `W` to an affine
scheme is constant: it factors through the structure map to `Spec k`. -/
theorem exists_eq_const {k : Type u} [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] {W : X.Opens} {z y₀ y₁ : X}
    (hW : ∀ y : X, y ∉ W ↔ y = z) (h₀₁ : y₀ ⤳ y₁) (h₁z : y₁ ⤳ z) (hne₀₁ : y₀ ≠ y₁)
    (hne₁z : y₁ ≠ z) [UniqueFactorizationMonoid (X.presheaf.stalk z)]
    {Y : Scheme.{u}} [IsAffine Y] (f : W.toScheme ⟶ Y) :
    ∃ c : Spec (CommRingCat.of k) ⟶ Y, f = W.ι ≫ p ≫ c := by
  have hy₁W : y₁ ∈ W := by
    by_contra h
    exact hne₁z ((hW y₁).mp h)
  -- Global functions of `W` are those of `X`, hence constants.
  have hbij : ∀ O : X.Opens, O = W →
      Function.Bijective (X.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op) := by
    rintro O rfl
    exact ⟨restrict_injective hy₁W,
      restrict_surjective_of_generization_chain hW h₀₁ h₁z hne₀₁ hne₁z⟩
  have hι : IsIso W.ι.appTop :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij _ W.ι_image_top)
  have hp : IsIso p.appTop := isIso_appTop_of_proper_connected_reduced k X p
  have hWp : IsIso (W.ι ≫ p).appTop := by
    rw [Scheme.Hom.comp_appTop]
    infer_instance
  -- A rational point of `W`.
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x, hxW, hx'⟩ := nonempty_inter_closedPoints ⟨y₁, hy₁W⟩ W.isOpen.isLocallyClosed
  have hx : IsClosed {x} := hx'
  have hrange : Set.range (pointOfClosedPoint p x hx) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨a, rfl⟩
    rw [pointOfClosedPoint_apply]
    exact hxW
  let s : Spec (CommRingCat.of k) ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι (pointOfClosedPoint p x hx) hrange
  have hs : s ≫ (W.ι ≫ p) = 𝟙 _ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pointOfClosedPoint_comp]
  refine ⟨s ≫ f, ?_⟩
  exact (affineMap_eq_constant_of_isIso_appTop (W.ι ≫ p) s hs f).trans
    (by simp only [Category.assoc])

end Langlands.AlgebraicGeometry.HartogsAffineConstancy
