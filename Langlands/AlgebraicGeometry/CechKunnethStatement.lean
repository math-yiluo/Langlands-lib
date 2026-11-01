import Langlands.AlgebraicGeometry.CechPullback
import Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.Core

/-!
# Künneth detection of products of degree-one Čech cocycles (statement)

Let `P` be the fibre product of `πX : X ⟶ Spec R` and `πY : Y ⟶ Spec R`, with projections `p₁`
and `p₂`, and cover `P` by the opens `p₁⁻¹ U a ⊓ p₂⁻¹ V b`. Let `λ` be an `R`-linear functional
on Čech `1`-cochains of `𝒪_X` for `U` that kills coboundaries, with `λ (z 0) = 1` and
`λ (z r) = 0` for the other `1`-cocycles `z r`. If the product of the `1`-cocycles
`p₁^* z k + p₂^* y k` (`k = 0, …, n + 1`) is a Čech coboundary on the product cover, then the
product of `y 1, …, y (n + 1)` is a Čech coboundary for `V`.
-/

universe w w' u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.Cohomology.Cech

open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-- Künneth detection of products of degree-one Čech cocycles on a product cover. -/
def KunnethDetectionStatement : Prop :=
  ∀ {R : CommRingCat.{u}} {X Y P : Scheme.{u}} {πX : X ⟶ Spec R} {πY : Y ⟶ Spec R}
    {p₁ : P ⟶ X} {p₂ : P ⟶ Y}, IsPullback p₁ p₂ πX πY →
  ∀ [∀ W : X.Opens, Algebra R Γ(X, W)], (∀ W : X.Opens, algebraMap R Γ(X, W) = (secHom πX W).hom) →
  ∀ [∀ W : Y.Opens, Algebra R Γ(Y, W)], (∀ W : Y.Opens, algebraMap R Γ(Y, W) = (secHom πY W).hom) →
  ∀ {ι : Type w} {κ : Type w'} [Finite ι] [Finite κ] (U : ι → X.Opens) (V : κ → Y.Opens),
    (∀ σ : Fin 2 → ι, IsAffineOpen (inter U σ)) →
    (∀ (m : ℕ) (τ : Fin (m + 1) → κ), IsAffineOpen (inter V τ)) →
  ∀ (l : (∀ σ : Fin 2 → ι, Γ(X, inter U σ)) →ₗ[R] R),
    (∀ y : C (ab X.presheaf) U 0, l (d (ab X.presheaf) U 0 y) = 0) →
  ∀ (n : ℕ) (z : Fin (n + 2) → C (ab X.presheaf) U 1) (y : Fin (n + 2) → C (ab Y.presheaf) V 1),
    (∀ k, d (ab X.presheaf) U 1 (z k) = 0) → (∀ k, d (ab Y.presheaf) V 1 (y k) = 0) →
    l (z 0) = 1 → (∀ r : Fin (n + 1), l (z r.succ) = 0) →
  ∀ c : C (ab P.presheaf) (prodCover p₁ p₂ U V) (n + 1),
    prod P.presheaf (prodCover p₁ p₂ U V) (n + 2)
        (fun k => pull p₁ U (prodCover p₁ p₂ U V) Prod.fst (fun _ => inf_le_left) 1 (z k) +
          pull p₂ V (prodCover p₁ p₂ U V) Prod.snd (fun _ => inf_le_right) 1 (y k)) =
      d (ab P.presheaf) (prodCover p₁ p₂ U V) (n + 1) c →
    ∃ c' : C (ab Y.presheaf) V n,
      prod Y.presheaf V (n + 1) (Fin.tail y) = d (ab Y.presheaf) V n c'

end Langlands.Cohomology.Cech
