import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Torus.Lattice

/-! # Statement: Steinberg's class quotient of a simply connected quasi-split group -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Steinberg's class quotient with strongly regular fibres and rational points.** Let `G` be
a simply connected quasi-split group over a field `K`. There are a `K`-scheme `V` and a
`K`-morphism `ρ : G → V` with three properties.

1. `ρ` is invariant under conjugation on every test object.
2. For every field `F` over `K`, two points `y` and `w` of `G` over `Spec F` with the same image
   under `ρ`, where the all-test centralizer of `w` in `G_F` lies in a closed `F`-torus, are
   conjugate over some field extension of `F`.
3. A `K`-point of `V` that becomes the image under `ρ` of such a strongly regular point over some
   field `F` is the image under `ρ` of a `K`-rational point of `G`. -/
def QuasiSplitSteinbergQuotientStatement : Prop :=
  ∀ (K : Type u) [Field K] (G : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → IsQuasiSplit G →
    ∃ (V : Over (Spec (CommRingCat.of K))) (ρ : G.X ⟶ V),
      (∀ {Z : Over (Spec (CommRingCat.of K))} (g x : Z ⟶ G.X),
        (g * x * g⁻¹) ≫ ρ = x ≫ ρ) ∧
      (∀ (F : Type u) [Field F] [Algebra K F]
        (y w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
        (S : GroupScheme (Spec (CommRingCat.of F)))
        (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G),
        IsTorus S → IsClosedSubgroup j →
        (∀ {Z : Over (Spec (CommRingCat.of F))}
            (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G).X),
          c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) =
              (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) * c →
            ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
        y ≫ ρ = w ≫ ρ →
        ∃ (E : Type u) (_ : Field E) (_ : Algebra K E)
          (q : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))))
          (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K E))) ⟶ G.X),
          g * (q ≫ y) * g⁻¹ = q ≫ w) ∧
      (∀ (v : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ V)
        (F : Type u) [Field F] [Algebra K F]
        (w : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟶ G.X)
        (S : GroupScheme (Spec (CommRingCat.of F)))
        (j : S ⟶ (baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G),
        IsTorus S → IsClosedSubgroup j →
        (∀ {Z : Over (Spec (CommRingCat.of F))}
            (c : Z ⟶ ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap K F)))).obj G).X),
          c * (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) =
              (toUnit Z ≫ (baseChangeBasePointsEquiv _ G).symm w) * c →
            ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
        toUnit _ ≫ v = w ≫ ρ →
        ∃ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X, x ≫ ρ = v)

end Langlands.GroupScheme
