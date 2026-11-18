import Langlands.BruhatTits.Cartan.RenardLeviCones
import Langlands.GroupScheme.Rational.StandardRepresentability

/-! # Partition of Renard's full split-component cone modulo the common norm kernel -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.BruhatTits.Cartan.RenardLeviCones

/-- The image of the full nonnegative cone of a standard Levi split component
modulo its common norm kernel is partitioned by the images of the strict
cones of the split components of the containing standard parabolics. -/
def LeviConePartitionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ (ν : cocharacterLattice T), IsGenericCocharacter i ν →
      ∀ (J : Set (characterLattice T)), J ⊆ simpleRelativeRoots i ν →
        ∀ (A : CommGroupScheme (Spec (CommRingCat.of F)))
          (a : A.toGrp ⟶ Standard.leviScheme i ν J), IsSplitComponent a →
          ∀ (f : A ⟶ T), CommGroupScheme.groupHom f ≫ i = a ≫ Standard.leviHom i ν J →
            let q := QuotientGroup.mk' (rationalCommonNormKernel A.toGrp)
            let cone := q '' componentPlus F i ν J f
            let piece (K : Set (characterLattice T)) :=
              {c | J ⊆ K ∧ K ⊆ simpleRelativeRoots i ν ∧
                ∃ (B : CommGroupScheme (Spec (CommRingCat.of F)))
                  (b : B.toGrp ⟶ Standard.leviScheme i ν K), IsSplitComponent b ∧
                  ∃ g : B ⟶ A,
                    CommGroupScheme.groupHom (g ≫ f) ≫ i = b ≫ Standard.leviHom i ν K ∧
                    c ∈ (q ∘ rationalPoints.map (CommGroupScheme.groupHom g)) ''
                      componentStrict F i ν K (g ≫ f)}
            (∀ K, piece K ⊆ cone) ∧ ∀ c ∈ cone, ∃! K, c ∈ piece K

end Langlands.BruhatTits.Cartan.RenardLeviCones
