import Langlands.AlgebraicGeometry.Picard.SquareZeroRelativeObstructionNaturality
import Langlands.AlgebraicGeometry.Modules.CohomologyPullback

/-! # Naturality of square-zero Picard obstructions under morphisms of thickenings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open SquareZeroUnitCohomology StructureKernelModule Langlands.Scheme.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Let `f : X' ⟶ X` be a morphism over `Spec R` and let `i : Y ⟶ X`, `i' : Y' ⟶ X'` be
closed immersions with square-zero ideals, with `g : Y' ⟶ Y` and `i' ≫ f = g ≫ i`. Let
`k : I ⟶ f_* I'` be the map of ideal modules induced by `f`, characterized by its
compatibility with the inclusions into the structure sheaves. Then for every Picard class
`y` on `Y`, the obstruction of `g^* y` is the image of the obstruction of `y` under the
cohomology pullback `H²(X, I) ⟶ H²(X', f^* I)` followed by the adjoint `f^* I ⟶ I'` of `k`.
This proposition is a statement target, not a proof. -/
def SquareZeroObstructionMorphismNaturalityStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X X' : Over (Spec R)) (f : X' ⟶ X) (Y Y' : Scheme.{u})
    (i : Y ⟶ X.left) (i' : Y' ⟶ X'.left) (g : Y' ⟶ Y)
    [CompactSpace X.left] [CompactSpace Y] [CompactSpace X'.left] [CompactSpace Y']
    [IsClosedImmersion i] [IsClosedImmersion i'] (hi : i.ker ^ 2 = ⊥) (hi' : i'.ker ^ 2 = ⊥),
    i' ≫ f.left = g ≫ i →
    ∀ k : kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule i'),
      k ≫ (Scheme.Modules.pushforward f.left).map (kernelModuleι i') =
        kernelModuleι i ≫ unitToPushforwardUnit f.left →
      ∀ y : Group Y,
        SquareZeroRelativeObstructionNaturality.relativeIdealCohomologyAddEquiv X'.hom i' 2
            (SquareZeroPicardObstruction.obstructionMap i' hi' (Group.pullback g y)) =
          ((relativeCohomology X'.hom 2).map
              (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm k)).hom
            ((relativeCohomologyPullback f (kernelModule i) 2).hom
              (SquareZeroRelativeObstructionNaturality.relativeIdealCohomologyAddEquiv X.hom i 2
                (SquareZeroPicardObstruction.obstructionMap i hi y)))

end Langlands.AlgebraicGeometry.Picard
