import Langlands.AlgebraicGeometry.Modules.SerreVanishing.Twist

/-! # Iterated twisting by a line bundle, and killing cohomology by powers of a section -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

variable {X : Scheme.{u}}

section Iterate

variable (N : X.Modules) (s : GlobalSections N)

/-- Multiplication by `s` is natural in the module. -/
lemma twistMul_naturality {A B : X.Modules} (g : A ⟶ B) :
    twistMul N s A ≫ tensorMap g (𝟙 N) = g ≫ twistMul N s B := by
  have h1 : (tensorRightUnitor A).inv ≫ tensorMap g (𝟙 (structureSheaf X)) =
      g ≫ (tensorRightUnitor B).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, tensorRightUnitor_naturality]
  unfold twistMul
  calc ((tensorRightUnitor A).inv ≫ tensorMap (𝟙 A) (sectionHom N s)) ≫ tensorMap g (𝟙 N)
      = (tensorRightUnitor A).inv ≫ tensorMap g (𝟙 (structureSheaf X)) ≫
          tensorMap (𝟙 B) (sectionHom N s) := by
        rw [Category.assoc, tensorMap_comp, tensorMap_comp, Category.id_comp, Category.comp_id,
          Category.id_comp, Category.comp_id]
    _ = g ≫ (tensorRightUnitor B).inv ≫ tensorMap (𝟙 B) (sectionHom N s) := by
        rw [← Category.assoc, h1, Category.assoc]

/-- Tensoring `k` times on the right with `N`. -/
def twistIter : ℕ → (X.Modules ⥤ X.Modules)
  | 0 => 𝟭 _
  | k + 1 => twistIter k ⋙ tensorBy N

/-- Multiplication by `s` from the `k`-th to the `(k + 1)`-st twist. -/
def stepNat (k : ℕ) : twistIter N k ⟶ twistIter N (k + 1) where
  app G := twistMul N s ((twistIter N k).obj G)
  naturality _ _ g := (twistMul_naturality N s ((twistIter N k).map g)).symm

/-- Multiplication by `s ^ k`, from a module to its `k`-th twist. -/
def twistPow : (k : ℕ) → (𝟭 X.Modules ⟶ twistIter N k)
  | 0 => 𝟙 _
  | k + 1 => twistPow k ≫ stepNat N s k

lemma twistPow_succ_app (k : ℕ) (G : X.Modules) :
    (twistPow N s (k + 1)).app G = (twistPow N s k).app G ≫ (stepNat N s k).app G := rfl

end Iterate

/-- Killing of cohomology classes by powers of a section (after Stacks 01XR): on a proper
scheme over a field, if the trivialization locus of a global section `s` of a line bundle `N`
is affine, then every class in positive degree of a quasi-coherent module `Z` is killed by
multiplication by `s ^ k`, `Z ⟶ Z ⊗ N ⊗ ⋯ ⊗ N`, for some `k`. -/
def TwistKillingStatement : Prop :=
  ∀ (K : Type u) [Field K] (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)),
    IsProper f →
      ∀ (N : X.Modules), IsLocallyFreeRankOne N → ∀ s : GlobalSections N,
        IsAffineOpen (trivializationOpen N s) →
          ∀ (Z : X.Modules), Z.IsQuasicoherent → ∀ (p : ℕ)
            (ξ : (DerivedSections.relativeCohomology f (p + 1)).obj Z),
              ∃ k : ℕ, ((DerivedSections.relativeCohomology f (p + 1)).map
                ((twistPow N s k).app Z)).hom ξ = 0

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
