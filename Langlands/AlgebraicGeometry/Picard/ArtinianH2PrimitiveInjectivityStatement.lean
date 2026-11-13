import Langlands.AlgebraicGeometry.Picard.StructureKernelModule
import Langlands.AlgebraicGeometry.Modules.CohomologyPullback
import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Reduced-coproduct injectivity for elementary Artinian ideal cohomology -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard.StructureKernelModule
  Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- On an abelian scheme over a local Artinian ring, the reduced coproduct is
injective on the actual ideal H² of an elementary Artinian thickening. Each
coefficient map is characterized by compatibility with the actual ideal
inclusion. This is a proposition target, not a proof. -/
def ArtinianH2PrimitiveInjectivityStatement : Prop :=
  ∀ (B' B : Type u) [CommRing B'] [CommRing B] [IsLocalRing B'] [IsLocalRing B]
    [IsArtinianRing B'] [IsArtinianRing B] (φ : B' →+* B),
    Function.Surjective φ → maximalIdeal B' * RingHom.ker φ = ⊥ →
      ∀ (A : AbelianScheme (Spec (CommRingCat.of B'))),
        let j : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of B') :=
          Spec.map (CommRingCat.ofHom φ)
        let P : Over (Spec (CommRingCat.of B')) := A.X ⨯ A.X
        let p1 : P ⟶ A.X := Limits.prod.fst
        let p2 : P ⟶ A.X := Limits.prod.snd
        let m : P ⟶ A.X := p1 * p2
        let i := pullback.fst A.X.hom j
        let iP := pullback.fst P.hom j
        let compatible (f : P ⟶ A.X)
            (k : kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule iP)) :=
          k ≫ (Scheme.Modules.pushforward f.left).map (kernelModuleι iP) =
            kernelModuleι i ≫ unitToPushforwardUnit f.left
        let pull (f : P ⟶ A.X)
            (k : kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule iP)) :=
          (relativeCohomologyPullback f (kernelModule i) 2 ≫
            (relativeCohomology P.hom 2).map
              (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm k)).hom
        ∀ (km : kernelModule i ⟶ (Scheme.Modules.pushforward m.left).obj (kernelModule iP))
          (k1 : kernelModule i ⟶ (Scheme.Modules.pushforward p1.left).obj (kernelModule iP))
          (k2 : kernelModule i ⟶ (Scheme.Modules.pushforward p2.left).obj (kernelModule iP)),
          compatible m km → compatible p1 k1 → compatible p2 k2 →
            Function.Injective (pull m km - pull p1 k1 - pull p2 k2)

end Langlands.AbelianScheme
