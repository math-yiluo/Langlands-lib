import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.FieldTheory.Galois.Basic

/-! # Statement: rational points of Galois-stable strongly regular classes -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Rational points of Galois-stable strongly regular classes.** Let `G` be a simply
connected quasi-split group over a field `K` and `L/K` a finite Galois extension. Let `z` be
a point of `G` over `Spec L`, viewed as an object over `Spec K`, whose all-test centralizer
in the base change `G_L` lies in a closed `L`-torus `S`. Suppose that for every
`K`-endomorphism `σ` of `Spec L` the point `σ ≫ z` is conjugate to `z` over some field
extension. Then some `K`-rational point `x` of `G` is conjugate to `z` over some field
extension. -/
def QuasiSplitRegularClassRationalStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → IsQuasiSplit G →
    ∀ (z : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶ G.X)
      (S : GroupScheme (Spec (CommRingCat.of L)))
      (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of L))}
          (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj G).X),
        c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm z) =
            (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm z) * c →
          ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      (∀ σ : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))),
        ∃ (E : Type u) (_ : Field E) (_ : Algebra K E)
          (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
          h * (q ≫ z) * h⁻¹ = q ≫ σ ≫ z) →
      ∃ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
        (E : Type u) (_ : Field E) (_ : Algebra K E)
        (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
        (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
        g * (toUnit _ ≫ x) * g⁻¹ = q ≫ z

end Langlands.GroupScheme
