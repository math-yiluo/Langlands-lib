import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom
import Langlands.Algebra.DiagonalizableHomSmooth

/-! # Smoothness of homomorphisms out of a finite power of roots of unity

For a smooth affine group scheme `G` over `Spec R`, a finite index type `I` and `m > 0`, every
universal family of homomorphisms `μ_m^I → G` has a smooth base. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.HomScheme

section Uniqueness

variable {S : Scheme.{u}} {H G : GroupScheme S}

/-- Two universal families of homomorphisms `H → G` have isomorphic bases. -/
def IsUniversal.iso {M N : Over S} {i : RelativeHom H G M} {j : RelativeHom H G N}
    (hi : IsUniversal i) (hj : IsUniversal j) : M ≅ N where
  hom := ((hj M).surjective i).choose
  inv := ((hi N).surjective j).choose
  hom_inv_id := (hi M).injective <| by
    rw [evaluate_comp, ((hi N).surjective j).choose_spec, ((hj M).surjective i).choose_spec,
      evaluate_id]
  inv_hom_id := (hj N).injective <| by
    rw [evaluate_comp, ((hj M).surjective i).choose_spec, ((hi N).surjective j).choose_spec,
      evaluate_id]

/-- Smoothness of the base of a universal family does not depend on the family. -/
theorem IsUniversal.smooth_hom {M N : Over S} {i : RelativeHom H G M} {j : RelativeHom H G N}
    (hi : IsUniversal i) (hj : IsUniversal j) [Smooth N.hom] : Smooth M.hom := by
  rw [← Over.w (hi.iso hj).hom]
  infer_instance

end Uniqueness

namespace FiniteDiagonalizable

open Langlands.FiniteBialgebraHom FiniteSource

section Coordinates

variable {R : Type u} [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left]

/-- The coordinate Hopf algebra of a smooth affine group scheme is smooth. -/
theorem smooth_hopfAlgebra [Smooth G.X.hom] :
    Algebra.Smooth R (AffineCoordinates.hopfAlgebra G) := by
  let eX : (hopfGroup R (AffineCoordinates.hopfAlgebra G)).X ≅ G.X :=
    (Grp.forget _).mapIso (coordinateIso G)
  have : IsIso eX.hom.left := (Over.forget _).map_isIso eX.hom
  have h : Smooth
      (Spec.map (CommRingCat.ofHom (algebraMap R (AffineCoordinates.hopfAlgebra G)))) := by
    change Smooth (hopfGroup R (AffineCoordinates.hopfAlgebra G)).X.hom
    rw [← Over.w eX.hom]
    infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h
  exact RingHom.smooth_algebraMap.mp h

instance [Smooth G.X.hom] : Algebra.FormallySmooth R (AffineCoordinates.hopfAlgebra G) :=
  (smooth_hopfAlgebra G).formallySmooth

end Coordinates

section Universal

variable (R : Type u) [CommRing R] (I : Type u) [Fintype I] (m : ℕ) [NeZero m]
  (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffine G.X.left] [Smooth G.X.hom]

/-- The representing algebra of homomorphisms `μ_m^I → G` is smooth when `G` is smooth. -/
theorem smooth_homAlgebra : Algebra.Smooth R (homAlgebra R I m G) :=
  inferInstance

/-- The base of the universal family `universalHom` is smooth over `Spec R`. -/
theorem smooth_specOver_homAlgebra : Smooth (specOver R (homAlgebra R I m G)).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (homAlgebra R I m G))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (smooth_homAlgebra R I m G)

end Universal

/-- **Smoothness of homomorphisms out of `μ_m^I`.** For a smooth affine group scheme `G` over
`Spec R`, a finite index type `I` and `m > 0`, the base of every universal family of
homomorphisms `μ_m^I → G` is smooth over `Spec R`. -/
theorem smooth_of_isUniversal_muPower (R : Type u) [CommRing R] (I : Type u) [Finite I] {m : ℕ}
    (hm : 0 < m) (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    [Smooth G.X.hom] {Y : Over (Spec (CommRingCat.of R))}
    {i : RelativeHom (pi fun _ : I => (mu (Spec (CommRingCat.of R)) m).toGrp) G Y}
    (hi : IsUniversal i) : Smooth Y.hom := by
  have : NeZero m := ⟨hm.ne'⟩
  have := Fintype.ofFinite I
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := smooth_specOver_homAlgebra R I m G
  exact hi.smooth_hom (isUniversal_universalHom R I m G)

end FiniteDiagonalizable

end Langlands.GroupScheme.HomScheme
