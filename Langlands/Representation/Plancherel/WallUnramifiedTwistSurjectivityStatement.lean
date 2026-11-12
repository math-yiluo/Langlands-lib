import Langlands.Representation.Plancherel.RationalUnramifiedRestriction
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Reductive.Basic

/-! # Unramified twists across a rank-one wall

Let `L` be a rational Levi of a parabolic of a rational Levi `M`, and also a maximal proper
rational Levi of a parabolic of a rational Levi `M₁`, all inside a connected reductive `G`
over a nonarchimedean local field. If the split component `A_M` of `M`, which lies in `L`,
is not central in `M₁`, then every unramified character of `L(F)` is the product of the
restrictions of an unramified character of `M(F)` and one of `M₁(F)`.
This is a proof target, not a theorem.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

open GroupScheme

/-- Unramified twists across a rank-one wall: with `L ⊂ M` and `L ⊂ M₁` rational Levis
inside `G` (same embedding of `L`), `L` the Levi of a maximal proper parabolic `Q₁` of
`M₁`, and a split component `a : A_M → M` factoring through `L` by `b` and not central in
`M₁`, restriction gives a surjection `X(M) × X(M₁) → X(L)`, `(ψ, χ) ↦ ψ|_L · χ|_L`, of
actual unramified character groups. This is a proof target, not a theorem. -/
def WallUnramifiedTwistSurjectivityStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ (P M Q L P₁ M₁ Q₁ : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (m : M ⟶ P) (q : Q ⟶ M) (l : L ⟶ Q)
      (p₁ : P₁ ⟶ G) (m₁ : M₁ ⟶ P₁) (q₁ : Q₁ ⟶ M₁) (l₁ : L ⟶ Q₁),
      IsParabolicSubgroup p → ∀ (hm : IsRationalLeviSubgroup m),
      IsParabolicSubgroup q → ∀ (hl : IsRationalLeviSubgroup l),
      IsParabolicSubgroup p₁ → ∀ (hm₁ : IsRationalLeviSubgroup m₁),
      IsParabolicSubgroup q₁ → IsRationalLeviSubgroup l₁ →
      l ≫ q ≫ m ≫ p = l₁ ≫ q₁ ≫ m₁ ≫ p₁ →
      ¬ IsIso q₁ →
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ M₁) (f : Q₁ ⟶ H),
        IsParabolicSubgroup h → f ≫ h = q₁ → IsIso f ∨ IsIso h) →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k)))
        (a : A.toGrp ⟶ M) (b : A.toGrp ⟶ L),
        IsSplitComponent a → b ≫ l ≫ q = a → ¬ IsCentral (b ≫ l₁ ≫ q₁) →
        haveI : IsAffine M.X.left :=
          haveI := hm.isConnectedReductive.isAffineHom; isAffine_of_isAffineHom M.X.hom
        haveI : IsAffine L.X.left :=
          haveI := hl.isConnectedReductive.isAffineHom; isAffine_of_isAffineHom L.X.hom
        haveI : IsAffine M₁.X.left :=
          haveI := hm₁.isConnectedReductive.isAffineHom; isAffine_of_isAffineHom M₁.X.hom
        letI : TopologicalSpace (rationalPoints M) := rationalPointTopology k M.X
        letI : TopologicalSpace (rationalPoints L) := rationalPointTopology k L.X
        letI : TopologicalSpace (rationalPoints M₁) := rationalPointTopology k M₁.X
        ∀ φ : unramifiedCharacters (fun χ => (rationalNormCharacters L χ).toMul),
          ∃ (ψ : unramifiedCharacters (fun χ => (rationalNormCharacters M χ).toMul))
            (χ : unramifiedCharacters (fun χ => (rationalNormCharacters M₁ χ).toMul)),
            φ = rationalUnramifiedCharacterRestrict (l ≫ q) ψ *
              rationalUnramifiedCharacterRestrict (l₁ ≫ q₁) χ

end Langlands.Plancherel
