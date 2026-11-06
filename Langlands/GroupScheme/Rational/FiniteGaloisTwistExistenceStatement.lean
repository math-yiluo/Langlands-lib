import Langlands.GroupScheme.LocalGroupIso
import Mathlib.FieldTheory.Galois.Basic

/-! # Statement: twisting an affine field group by a finite-Galois cocycle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Existence of finite-Galois twisted forms.** For a finite Galois extension `L/K`, an
affine group scheme `G` over `K`, an automorphic action `a` of a group scheme `A` on `G`
and a natural cocycle `ξ` of `A` on the cover `Spec L → Spec K`, there are an affine group
scheme `H` over `K` and natural local group isomorphisms `e` from `G` to `H` on the points
of the cover whose discrepancy is `ξ` acting through `a`. -/
def FiniteGaloisTwistExistenceStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (A G : GroupScheme (Spec (CommRingCat.of K))),
    IsAffineHom G.X.hom →
    ∀ (a : AutomorphicAction A G)
      (ξ : Cocycle A (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
      ∃ (H : GroupScheme (Spec (CommRingCat.of K)))
        (e : LocalGroupIso G H (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))))),
        IsAffineHom H.X.hom ∧ e.HasDiscrepancy a ξ

end Langlands.GroupScheme
