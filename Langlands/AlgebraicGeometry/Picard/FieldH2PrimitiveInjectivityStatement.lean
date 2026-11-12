import Langlands.AlgebraicGeometry.Modules.CohomologyPullback
import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero

/-! # Absence of primitive structure-sheaf cohomology classes in degree two -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- For an abelian scheme over a field, the difference of multiplication pullback
and the two projection pullbacks is injective on actual structure-sheaf H².
All three maps use the canonical cohomology pullback and structure-sheaf
coefficient comparison. This is a proposition target, not a proof. -/
def FieldH2PrimitiveInjectivityStatement : Prop :=
  ∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K))),
    let P : Over (Spec (CommRingCat.of K)) := A.X ⨯ A.X
    let p1 : P ⟶ A.X := Limits.prod.fst
    let p2 : P ⟶ A.X := Limits.prod.snd
    let m : P ⟶ A.X := p1 * p2
    let O := SheafOfModules.unit A.X.left.ringCatSheaf
    let pull (f : P ⟶ A.X) :=
      (relativeCohomologyPullback f O 2 ≫
        (relativeCohomology P.hom 2).map
          (Langlands.Scheme.Modules.pullbackUnitIso f.left).hom).hom
    Function.Injective (pull m - pull p1 - pull p2)

end Langlands.AbelianScheme
