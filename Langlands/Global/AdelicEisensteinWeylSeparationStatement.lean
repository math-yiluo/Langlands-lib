import Langlands.Global.AdelicEisensteinConvergenceStatement
import Langlands.Representation.Aubert.General.RationalWeylRootAction

/-! # Shifted Weyl translates of regular parameters leave the leading chamber -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints Langlands.Plancherel
  Langlands.GroupScheme.RealTorusSpace Langlands.Aubert.General.RationalPointFamily

/-- For a finite set of shifts, all nonidentity Weyl elements preserving
positivity on the selected simple roots send sufficiently regular parameters
outside the ambient closed positive chamber, after any of those shifts. -/
def EisensteinAmbientWeylSeparationStatement : Prop :=
  ∀ (F : Type u) [Field F] (G P M : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G →
      ∀ S : Set (Vstar r.data.T), S.Finite →
        ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
          ∀ w : relativeWeylGroup r.data.i, w ≠ 1 →
            (∀ α ∈ r.data.J, schemeWeylCharacterAction r.data.i w α ∈
              positiveRelativeRoots r.data.i r.data.ν) →
            ∀ shift ∈ S, ∃ β ∈ simpleRelativeRoots r.data.i r.data.ν,
              relativeWeylInvariantForm r.data.i hT
                (relativeWeylRealCharacterAction r.data.i w
                  (weylCharacterRestrictionLift hA hT r.data.f r.data.i
                    (realParameterRestriction (a ≫ l) (parameterRealPart F P lam))) + shift)
                ((1 : ℝ) ⊗ₜ[ℤ] β) < 0

end Langlands.Global
