import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Mathlib.Algebra.MvPolynomial.Eval

/-! # Invariant polynomials and flat surjective restriction -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Matrix

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- A polynomial is invariant if its evaluation is unchanged by the representation
on section-valued vectors over every test scheme. -/
def IsInvariantPolynomial (ρ : MatrixRepresentation G n) (F : MvPolynomial n R) : Prop :=
  ∀ (T : Over (Spec R)) (g : T ⟶ G.X) (x : n → Γ(T.left, ⊤)),
    MvPolynomial.eval₂ (scalarMap T)
        ((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) F =
      MvPolynomial.eval₂ (scalarMap T) x F

omit [Fintype n] [DecidableEq n] in
/-- Polynomial evaluation commutes with pullback along every relative test map. -/
theorem eval₂_scalarMap_naturality {T U : Over (Spec R)} (a : U ⟶ T)
    (x : n → Γ(T.left, ⊤)) (F : MvPolynomial n R) :
    a.left.appTop (MvPolynomial.eval₂ (scalarMap T) x F) =
      MvPolynomial.eval₂ (scalarMap U) (fun i => a.left.appTop (x i)) F := by
  rw [MvPolynomial.eval₂_comp_left a.left.appTop.hom]
  have hscalar : a.left.appTop.hom.comp (scalarMap T) = scalarMap U := by
    ext c
    exact scalarMap_naturality a c
  rw [hscalar]
  rfl

/-- Invariant polynomials remain invariant after restriction along a homomorphism. -/
theorem IsInvariantPolynomial.restrict {ρ : MatrixRepresentation G n}
    {F : MvPolynomial n R} (hF : ρ.IsInvariantPolynomial F) (q : H ⟶ G) :
    (ρ.restrict q).IsInvariantPolynomial F := by
  intro T g x
  rw [pointMatrix_restrict]
  exact hF T (g ≫ q.hom.hom) x

/-- Flat surjective restriction detects polynomial invariance on all test schemes. -/
theorem isInvariantPolynomial_restrict_iff (ρ : MatrixRepresentation G n) (q : H ⟶ G)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] (F : MvPolynomial n R) :
    (ρ.restrict q).IsInvariantPolynomial F ↔ ρ.IsInvariantPolynomial F := by
  constructor
  · intro hF T g x
    let U : Over (Spec R) :=
      Over.mk (pullback.fst g.left q.hom.hom.left ≫ T.hom)
    let a : U ⟶ T := Over.homMk (pullback.fst g.left q.hom.hom.left) rfl
    let h : U ⟶ H.X := Over.homMk (pullback.snd g.left q.hom.hom.left) (by
      dsimp [U]
      rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
        Category.assoc, Over.w g])
    have hcomp : a ≫ g = h ≫ q.hom.hom := by
      apply Over.OverMorphism.ext
      exact pullback.condition
    have : Epi a.left := by
      change Epi (pullback.fst g.left q.hom.hom.left)
      exact Flat.epi_of_flat_of_surjective _
    apply Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi a.left
    rw [eval₂_scalarMap_naturality, eval₂_scalarMap_naturality]
    have hvec :
        (fun i => a.left.appTop
          (((ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ x) i)) =
        ((ρ.restrict q).pointMatrix U h : Matrix n n Γ(U.left, ⊤)) *ᵥ
          (fun i => a.left.appTop (x i)) := by
      rw [pointMatrix_restrict, ← hcomp, pointMatrix_naturality]
      funext i
      exact a.left.appTop.hom.map_mulVec _ _ i
    rw [hvec]
    exact hF U h _
  · exact fun hF => hF.restrict q

end Langlands.GroupScheme.MatrixRepresentation
