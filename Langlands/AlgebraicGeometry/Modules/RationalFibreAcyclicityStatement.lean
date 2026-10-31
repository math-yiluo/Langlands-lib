import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Open-local vanishing of higher direct images from rational-fibre acyclicity -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open DerivedSections

/-- For a smooth proper family over a locally finite-type scheme over an
algebraically closed field, vanishing cohomology on all rational fibres over
an open set implies vanishing of every higher direct image on that open.
This is a proposition statement, not a proof. -/
def RationalFibreAcyclicityStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (X Y : Scheme.{u}) (g : Y ⟶ Spec (CommRingCat.of K)),
    LocallyOfFiniteType g →
    ∀ f : X ⟶ Y, Smooth f → IsProper f →
    ∀ (Q : Picard.LineBundle X) (U : Y.Opens),
      (∀ (x : Spec (CommRingCat.of K) ⟶ U.toScheme),
        x ≫ U.ι ≫ g = 𝟙 (Spec (CommRingCat.of K)) →
        ∀ n : ℕ,
          IsZero ((relativeCohomology (pullback.snd f (x ≫ U.ι)) n).obj
            ((Scheme.Modules.pullback (pullback.fst f (x ≫ U.ι))).obj Q.obj))) →
      ∀ n : ℕ,
        IsZero ((Scheme.Modules.pullback U.ι).obj ((higherDirectImage f n).obj Q.obj))

end Langlands.AlgebraicGeometry.Modules
