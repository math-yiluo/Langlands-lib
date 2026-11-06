import Langlands.GroupScheme.LocalGroupIso
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.FieldTheory.Galois.Basic

/-! # Statement: rational representatives of strongly regular classes of inner forms -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Steinberg's rational conjugacy theorem, in finite-Galois inner-form form.** Let `G` be
a simply connected quasi-split group over a field `K`, `π : G ⟶ A` a central isogeny and `a`
the action of `A` on `G` with `a(π h) g = h g h⁻¹`. Let `H` be the twist of `G` by a natural
cocycle `ξ` of `A` on the cover `Spec L → Spec K` of a finite Galois extension, given by
natural local isomorphisms `e` with discrepancy `ξ`. For a rational point `y` of `H` whose
all-test centralizer lies in a closed torus of `H`, there are a rational point `x` of `G`
whose all-test centralizer lies in a closed torus of `G`, a finite Galois extension `L'/K`, a
morphism `r` of covers from `Spec L'` to `Spec L` and a point `g` of `G` over `Spec L'` such
that `e` at `r` carries `g x g⁻¹` to `y`. -/
def QuasiSplitSimplyConnectedRegularConjugateStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (G A : GroupScheme (Spec (CommRingCat.of K))),
    IsSimplyConnected G → IsQuasiSplit G →
    ∀ (π : G ⟶ A), IsCentralIsogeny π →
    ∀ (a : AutomorphicAction A G),
      (∀ {Z : Over (Spec (CommRingCat.of K))} (h g : Z ⟶ G.X),
        a.act (h ≫ π.hom.hom) g = h * g * h⁻¹) →
    ∀ (ξ : Cocycle A (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
      (H : GroupScheme (Spec (CommRingCat.of K)))
      (e : LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      e.HasDiscrepancy a ξ →
    ∀ (y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ H.X)
      (S : GroupScheme (Spec (CommRingCat.of K))) (j : S ⟶ H),
      IsTorus S → IsClosedSubgroup j →
      (∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ H.X),
        c * (toUnit Z ≫ y) = (toUnit Z ≫ y) * c → ∃ s : Z ⟶ S.X, s ≫ j.hom.hom = c) →
      ∃ (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ G.X)
        (T : GroupScheme (Spec (CommRingCat.of K))) (i : T ⟶ G),
        IsTorus T ∧ IsClosedSubgroup i ∧
        (∀ {Z : Over (Spec (CommRingCat.of K))} (c : Z ⟶ G.X),
          c * (toUnit Z ≫ x) = (toUnit Z ≫ x) * c → ∃ t : Z ⟶ T.X, t ≫ i.hom.hom = c) ∧
        ∃ (L' : Type u) (_ : Field L') (_ : Algebra K L')
          (_ : FiniteDimensional K L') (_ : IsGalois K L')
          (r : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))
          (g : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L'))) ⟶ G.X),
          e.toFun r (g * (toUnit _ ≫ x) * g⁻¹) = toUnit _ ≫ y

end Langlands.GroupScheme
