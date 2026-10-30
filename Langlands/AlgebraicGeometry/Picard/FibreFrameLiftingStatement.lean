import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Local lifting of a fibre frame detected by two restrictions -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.AlgebraicGeometry.Modules

/-- If two closed restrictions detect degree-one fibre cohomology and trivialize
a line bundle, a frame on one fibre extends to a section near that fibre whose
fibre pullback is still a frame. The section is not asserted to be a frame
away from that fibre. -/
def FibreFrameLiftingStatement : Prop :=
  ∀ (S : Scheme.{u}) (X X₁ X₂ : Over S),
    Smooth X.hom → IsProper X.hom → GeometricallyConnected X.hom →
    Smooth X₁.hom → IsProper X₁.hom → GeometricallyConnected X₁.hom →
    Smooth X₂.hom → IsProper X₂.hom → GeometricallyConnected X₂.hom →
    ∀ (i₁ : X₁ ⟶ X) (i₂ : X₂ ⟶ X),
      IsClosedImmersion i₁.left → IsClosedImmersion i₂.left →
      ∀ (L : LineBundle X.left) (s : S),
        Nonempty ((Scheme.Modules.pullback i₁.left).obj L.obj ≅
          Langlands.Scheme.Modules.structureSheaf X₁.left) →
        Nonempty ((Scheme.Modules.pullback i₂.left).obj L.obj ≅
          Langlands.Scheme.Modules.structureSheaf X₂.left) →
        Nonempty ((Scheme.Modules.pullback (X.hom.fiberι s)).obj L.obj ≅
          Langlands.Scheme.Modules.structureSheaf (X.hom.fiber s)) →
        let j₁ : X₁.hom.fiber s ⟶ X.hom.fiber s :=
          pullback.lift (X₁.hom.fiberι s ≫ i₁.left)
            (X₁.hom.fiberToSpecResidueField s) (by
              rw [Category.assoc, Over.w i₁]
              exact X₁.hom.fiber_fac s)
        let j₂ : X₂.hom.fiber s ⟶ X.hom.fiber s :=
          pullback.lift (X₂.hom.fiberι s ≫ i₂.left)
            (X₂.hom.fiberToSpecResidueField s) (by
              rw [Category.assoc, Over.w i₂]
              exact X₂.hom.fiber_fac s)
        let O := Langlands.Scheme.Modules.structureSheaf (X.hom.fiber s)
        let H := DerivedSections.relativeCohomology
          (X.hom.fiberToSpecResidueField s) 1
        (∀ c : H.obj O,
          (H.map ((Scheme.Modules.pullbackPushforwardAdjunction j₁).unit.app O)).hom c = 0 →
          (H.map ((Scheme.Modules.pullbackPushforwardAdjunction j₂).unit.app O)).hom c = 0 →
          c = 0) →
        ∃ (U : S.Opens) (hs : s ∈ U)
          (σ : Langlands.Scheme.Modules.structureSheaf (pullback X.hom U.ι) ⟶
            (Scheme.Modules.pullback (pullback.fst X.hom U.ι)).obj L.obj),
          IsIso ((Scheme.Modules.pullback
            ((pullback.snd X.hom U.ι).fiberι ⟨s, hs⟩)).map σ)

end Langlands.AlgebraicGeometry.Picard
