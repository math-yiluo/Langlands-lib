import Langlands.GroupScheme.Torus.ExponentIsogenies
import Langlands.LinearAlgebra.RootDatumIsogeny

/-! # The prescribed torus map for an affine split root-datum isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.AffineRootDatumIsogeny

variable {I I' J J' : Type u} [Fintype I] [Fintype I']
  [Finite J] [Finite J']
  {P : RootDatum J (I → ℤ) (I → ℤ)}
  {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}

/-- The homomorphism of coordinate split tori with the prescribed integral
character pullback, over an arbitrary base scheme. -/
def torusMap (S : Scheme.{u})
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P) :
    splitTorus S I ⟶ splitTorus S I' := by
  classical
  exact CommGroupScheme.groupHom (splitTorus.exponentHom S I I' f.weightMap)

/-- Both injective lattice maps force the coordinate ranks to agree. -/
theorem card_eq (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P) :
    Fintype.card I = Fintype.card I' := by
  apply Nat.le_antisymm
  · simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_le_finrank_of_injective f.coweightMap_injective
  · simpa only [Module.finrank_fintype_fun_eq_card] using
      LinearMap.finrank_le_finrank_of_injective f.weightMap_injective

/-- The given weight map has finite cokernel on the integral lattices. -/
theorem finite_weightMap_cokernel
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P) :
    Finite ((I → ℤ) ⧸ LinearMap.range f.weightMap) :=
  finite_quotient_range_of_injective_of_card_le f.weightMap
    f.weightMap_injective (card_eq f).le

/-- The prescribed monomial identity holds on every scheme test. -/
theorem points_torusMap (S : Scheme.{u})
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (U : Over S) (x : U ⟶ (splitTorus S I).X) (m : I' → ℤ) :
    ∏ j', splitTorus.pointsEquiv I' U (x ≫ (torusMap S f).hom.hom) j' ^ m j' =
      ∏ j, splitTorus.pointsEquiv I U x j ^ f.weightMap m j := by
  classical
  exact splitTorus.pointsEquiv_exponentHom S I I' f.weightMap x m

/-- Over every affine base, the canonical torus map is finite, flat and surjective.
No characteristic assumption on the coefficient ring is needed. -/
theorem isIsogeny_torusMap (R : CommRingCat.{u})
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P) :
    IsIsogeny (torusMap (Spec R) f) := by
  classical
  have := finite_weightMap_cokernel f
  exact splitTorus.isIsogeny_exponentHom (R := R) I I' f.weightMap
    f.weightMap_injective

end Langlands.GroupScheme.AffineRootDatumIsogeny
