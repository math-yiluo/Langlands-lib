import Langlands.AlgebraicGeometry.Modules.Tensor
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Lifting primitive line bundles along elementary Artinian thickenings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Let `φ : B' → B` be a surjection of local Artinian rings whose kernel is killed by the
maximal ideal of `B'`, let `A` be an abelian scheme over `Spec B'`, and let `A₀` be its base
change along `Spec φ`. A line bundle `L` on `A₀` whose multiplication pullback is isomorphic
to the tensor product of its two projection pullbacks on `A₀ ×_B A₀` is the pullback of a
line bundle on `A` along the first projection `A₀ = A ×_{B'} Spec B ⟶ A`.
This proposition is a statement target, not a proof. -/
def ArtinianPrimitiveLineBundleLiftingStatement : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] (φ : B' →+* B),
    Function.Surjective φ → maximalIdeal B' * RingHom.ker φ = ⊥ →
      ∀ (A : AbelianScheme (Spec (CommRingCat.of B'))),
        let j : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B') :=
          Spec.map (CommRingCat.ofHom φ)
        let A₀ : AbelianScheme (Spec (CommRingCat.of B)) := (baseChange j).obj A
        ∀ L : LineBundle A₀.X.left,
          (let P : Over (Spec (CommRingCat.of B)) := A₀.X ⨯ A₀.X
            let p1 : P ⟶ A₀.X := Limits.prod.fst
            let p2 : P ⟶ A₀.X := Limits.prod.snd
            let m : P ⟶ A₀.X := p1 * p2
            Nonempty ((Scheme.Modules.pullback m.left).obj L.obj ≅
              Langlands.Scheme.Modules.tensorObj
                ((Scheme.Modules.pullback p1.left).obj L.obj)
                ((Scheme.Modules.pullback p2.left).obj L.obj))) →
          ∃ L' : LineBundle A.X.left,
            Nonempty ((LineBundle.pullback (pullback.fst A.X.hom j)).obj L' ≅ L)

end Langlands.AbelianScheme
