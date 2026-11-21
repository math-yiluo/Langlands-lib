import Langlands.Global.AdelicEisensteinConvergenceStatement

/-! # Nonemptiness of the regular-parameter region -/

noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global

open GroupScheme AdelicGroupPoints

/-- The actual complex character parameters of a presented parabolic contain an
`R`-regular point for every real threshold `R`. -/
def EisensteinRegularParameterStatement : Prop :=
  ∀ (F : Type u) [Field F] (G P M : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
    IsConnectedReductive G → ∀ R : ℝ, ∃ lam : ComplexCharacterParameter F P,
      r.IsRegularParameter hA hT R lam

end Langlands.Global
