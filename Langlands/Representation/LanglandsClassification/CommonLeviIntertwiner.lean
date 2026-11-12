import Langlands.Representation.LanglandsClassification.CommonStandardLevi
import Langlands.Representation.Category.Twist
import Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof

/-! # Nonzero intertwiners over a common actual Levi

The final algebraic step of Renard VII.4.2(ii): a nonzero map intertwining
irreducible actions on the same ambient Levi image is an equivalence.
Equality of Levi images and existence of that map remain hypotheses.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G P₁ M₁ P₂ M₂ : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (p₁ : P₁ ⟶ G) (l₁ : M₁ ⟶ P₁)
  (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
  (p₂ : P₂ ⟶ G) (l₂ : M₂ ⟶ P₂)
  (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
  (hL : pointImage (l₁ ≫ p₁) = pointImage (l₂ ≫ p₂))
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  {W : Type w} [AddCommGroup W] [Module ℂ W]
  (ρ₁ : Representation ℂ (rationalPoints M₁) V)
  (ρ₂ : Representation ℂ (rationalPoints M₂) W)

local instance commonIntertwinerAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- Bundle the common-ambient-point equivariance condition as an intertwiner
over the first Levi, leaving its linear map unchanged. -/
def commonLeviIntertwiningMap (φ : V →ₗ[ℂ] W)
    (hφ : ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ∀ x : V, φ (ρ₁ m₁ x) = ρ₂ m₂ (φ x)) :
    letI := leviPointTopology l₁ hl₁
    letI := leviPointTopology l₂ hl₂
    ρ₁.IntertwiningMap
      (ρ₂.comp (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL).toMonoidHom) :=
  φ.intertwiningMap_of_isIntertwiningMap _ _
    ((commonLeviPoints_intertwines_iff p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
      ρ₁ ρ₂ φ).mp hφ)

@[simp]
theorem commonLeviIntertwiningMap_toLinearMap (φ : V →ₗ[ℂ] W) (hφ) :
    (commonLeviIntertwiningMap p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL ρ₁ ρ₂ φ hφ).toLinearMap =
      φ := rfl

/-- A nonzero common-Levi intertwiner of irreducible actions is an actual
representation equivalence. Its forward map is the supplied linear map. -/
def commonLeviEquivOfNonzero
    (hρ₁ : ρ₁.IsIrreducible) (hρ₂ : ρ₂.IsIrreducible)
    (φ : V →ₗ[ℂ] W) (hφ₀ : φ ≠ 0)
    (hφ : ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ∀ x : V, φ (ρ₁ m₁ x) = ρ₂ m₂ (φ x)) :
    letI := leviPointTopology l₁ hl₁
    letI := leviPointTopology l₂ hl₂
    ρ₁.Equiv
      (ρ₂.comp (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL).toMonoidHom) := by
  letI := leviPointTopology l₁ hl₁
  letI := leviPointTopology l₂ hl₂
  let e := commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
  letI := hρ₁
  letI := hρ₂
  letI : Representation.IsIrreducible (ρ₂.comp e.toMonoidHom) :=
    CuspidalSupport.isIrreducible_comp_of_surjective ρ₂ e.toMonoidHom e.surjective
  let F := commonLeviIntertwiningMap p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL ρ₁ ρ₂ φ hφ
  have hF : F ≠ 0 := by
    intro h
    apply hφ₀
    exact congrArg Representation.IntertwiningMap.toLinearMap h
  exact F.ofBijective
    ((Representation.IsIrreducible.bijective_or_eq_zero F).resolve_right hF)

@[simp]
theorem commonLeviEquivOfNonzero_toLinearMap
    (hρ₁ : ρ₁.IsIrreducible) (hρ₂ : ρ₂.IsIrreducible)
    (φ : V →ₗ[ℂ] W) (hφ₀ : φ ≠ 0) (hφ) :
    (commonLeviEquivOfNonzero p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
      ρ₁ ρ₂ hρ₁ hρ₂ φ hφ₀ hφ).toLinearEquiv.toLinearMap = φ := rfl

include hp₁ hl₁ hp₂ hl₂ hL in
/-- The isomorphism conclusion on the original ambient points follows from any
nonzero common-Levi intertwiner of irreducible actions. -/
theorem exists_commonLeviEquiv_of_nonzero
    (hρ₁ : ρ₁.IsIrreducible) (hρ₂ : ρ₂.IsIrreducible)
    (φ : V →ₗ[ℂ] W) (hφ₀ : φ ≠ 0)
    (hφ : ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ∀ x : V, φ (ρ₁ m₁ x) = ρ₂ m₂ (φ x)) :
    ∃ e : V ≃ₗ[ℂ] W, e.toLinearMap = φ ∧
      ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
        rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
          ∀ x : V, e (ρ₁ m₁ x) = ρ₂ m₂ (e x) := by
  let e := commonLeviEquivOfNonzero p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
    ρ₁ ρ₂ hρ₁ hρ₂ φ hφ₀ hφ
  exact ⟨e.toLinearEquiv, rfl, hφ⟩

section Twists

variable (χ₁ : rationalPoints M₁ →* ℂˣ) (χ₂ : rationalPoints M₂ →* ℂˣ)

/-- The same construction applies to scalar twists of irreducible actions;
neither finite dimension nor admissibility is needed. -/
def commonLeviTwistEquivOfNonzero
    (hρ₁ : ρ₁.IsIrreducible) (hρ₂ : ρ₂.IsIrreducible)
    (φ : V →ₗ[ℂ] W) (hφ₀ : φ ≠ 0)
    (hφ : ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ∀ x : V, φ (Langlands.twist χ₁ ρ₁ m₁ x) =
          Langlands.twist χ₂ ρ₂ m₂ (φ x)) :
    letI := leviPointTopology l₁ hl₁
    letI := leviPointTopology l₂ hl₂
    (Langlands.twist χ₁ ρ₁).Equiv
      ((Langlands.twist χ₂ ρ₂).comp
        (commonLeviPointsEquiv p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL).toMonoidHom) :=
  commonLeviEquivOfNonzero p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
    (Langlands.twist χ₁ ρ₁) (Langlands.twist χ₂ ρ₂)
    ((isIrreducible_twist_iff χ₁ ρ₁).mpr hρ₁)
    ((isIrreducible_twist_iff χ₂ ρ₂).mpr hρ₂) φ hφ₀ hφ

include hp₁ hl₁ hp₂ hl₂ hL in
/-- The ambient-point isomorphism conclusion for the two twists, retaining the
supplied map and independent carrier universes. -/
theorem exists_commonLeviTwistEquiv_of_nonzero
    (hρ₁ : ρ₁.IsIrreducible) (hρ₂ : ρ₂.IsIrreducible)
    (φ : V →ₗ[ℂ] W) (hφ₀ : φ ≠ 0)
    (hφ : ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
      rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
        ∀ x : V, φ (Langlands.twist χ₁ ρ₁ m₁ x) =
          Langlands.twist χ₂ ρ₂ m₂ (φ x)) :
    ∃ e : V ≃ₗ[ℂ] W, e.toLinearMap = φ ∧
      ∀ (m₁ : rationalPoints M₁) (m₂ : rationalPoints M₂),
        rationalPoints.map (l₁ ≫ p₁) m₁ = rationalPoints.map (l₂ ≫ p₂) m₂ →
          ∀ x : V, e (Langlands.twist χ₁ ρ₁ m₁ x) =
            Langlands.twist χ₂ ρ₂ m₂ (e x) :=
  exists_commonLeviEquiv_of_nonzero p₁ l₁ hp₁ hl₁ p₂ l₂ hp₂ hl₂ hL
    (Langlands.twist χ₁ ρ₁) (Langlands.twist χ₂ ρ₂)
    ((isIrreducible_twist_iff χ₁ ρ₁).mpr hρ₁)
    ((isIrreducible_twist_iff χ₂ ρ₂).mpr hρ₂) φ hφ₀ hφ

end Twists

end Langlands.Aubert.General.RepresentedParabolic
