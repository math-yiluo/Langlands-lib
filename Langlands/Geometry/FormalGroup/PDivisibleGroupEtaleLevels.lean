import Langlands.AlgebraicGeometry.FiniteEtale.Definitions
import Langlands.Geometry.FormalGroup.PDivisibleGroupTatePolarization
import Langlands.GroupScheme.Lie.SquareZeroKernelAdditive
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Finite étale levels of a p-divisible group where p is invertible -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open _root_.Langlands.GroupScheme.Lie
open _root_.Langlands.GroupScheme.Lie.SquareZero

attribute [local instance] Lie.coordinateOriginAlgebra

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffineHom G.X.hom]
variable (n : ℕ) (hn : IsUnit (n : R))
variable (hkill : ∀ (A : Type u) [CommRing A] [Algebra R A] (x : AffinePoints G A), x ^ n = 1)

include hn hkill in
private theorem reduction_injective_of_pow_eq_one
    {A : Type u} [CommRing A] [Algebra R A] (I : Ideal A) (hI : I ^ 2 = ⊥) :
    Function.Injective (Lie.SquareZero.reduction G I) := by
  let r := Lie.SquareZero.reduction G I
  intro x y hxy
  have hxy' : r x = r y := hxy
  let z : Lie.SquareZero.kernel G I := ⟨x * y⁻¹, by
    change r (x * y⁻¹) = 1
    rw [map_mul, map_inv, hxy', mul_inv_cancel]⟩
  let e := kernelAddEquiv G I hI
  have hz : z ^ n = 1 := Subtype.ext (hkill A z.val)
  have hzero : n • e (Additive.ofMul z) = 0 := by
    rw [← map_nsmul]
    change e (Additive.ofMul (z ^ n)) = 0
    rw [hz]
    exact map_zero e
  have he : e (Additive.ofMul z) = 0 := hn.smul_eq_zero.mp (by
    rw [Nat.cast_smul_eq_nsmul]
    exact hzero)
  have hz' : z = 1 := congrArg Additive.toMul (e.injective (he.trans (map_zero e).symm))
  exact mul_inv_eq_one.mp (congrArg Subtype.val hz')

include hn hkill in
/-- An affine group scheme annihilated by an invertible integer is formally unramified. -/
theorem formallyUnramified_of_invertible_exponent : FormallyUnramified G.X.hom := by
  have halg : Algebra.FormallyUnramified R (coordinateAlgebra G) :=
    Algebra.FormallyUnramified.iff_comp_injective.mpr (by
      intro A _ _ I hI a b hab
      apply (pointCoordinates G).symm.injective
      apply reduction_injective_of_pow_eq_one G n hn hkill I hI
      apply (pointCoordinates G).injective
      simp only [Lie.SquareZero.reduction, pointCoordinates_naturality, Equiv.apply_symm_apply]
      exact hab)
  let X := (algSpec R).obj (op (coordinateAlgebra G))
  have hX : FormallyUnramified X.hom := by
    change FormallyUnramified (Spec.map (CommRingCat.ofHom (algebraMap R (coordinateAlgebra G))))
    exact (HasRingHomProperty.Spec_iff (P := @FormallyUnramified)).mpr
      (RingHom.formallyUnramified_algebraMap.mpr halg)
  let f := (coordinateIso G).inv
  have : IsIso f.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (coordinateIso G)).inv)
  rw [← Over.w f]
  exact MorphismProperty.comp_mem @FormallyUnramified f.left X.hom inferInstance hX

end Langlands.GroupScheme

namespace Langlands.PDivisibleGroup

open GroupScheme GroupScheme.Cartier.FiniteDual

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p)

/-- The actual p-power groups are étale where `p` is a unit. -/
theorem finiteLevel_etale (hp : IsUnit (p : R)) (n : ℕ) :
    Etale (G.inclusions.obj n).X.hom := by
  let H := G.inclusions.obj n
  have hfin : IsFinite H.X.hom := (G.finiteLocallyFree n).1
  have hflat : Flat H.X.hom := (G.finiteLocallyFree n).2.1
  have hfp : LocallyOfFinitePresentation H.X.hom := (G.finiteLocallyFree n).2.2
  have hp' : IsUnit ((p ^ n : ℕ) : R) := by
    rw [Nat.cast_pow]
    exact hp.pow n
  have hkill : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (x : Lie.AffinePoints H.toGrp A), x ^ (p ^ n) = 1 := by
    intro A _ _ x
    exact congrArg Additive.toMul
      (schematicTateLevel_nsmul (G := G) (CommGroupScheme.affineTest (CommAlgCat.of R A)) n
        (Additive.ofMul x))
  have : FormallyUnramified H.X.hom :=
    GroupScheme.formallyUnramified_of_invertible_exponent H.toGrp (p ^ n) hp' hkill
  exact Etale.of_formallyUnramified_of_flat H.X.hom

/-- The actual `n`-th group of a p-divisible group as a finite étale cover
in the locus where `p` is invertible. -/
def finiteEtaleLevelCover (hp : IsUnit (p : R)) (n : ℕ) :
    Langlands.AlgebraicGeometry.FiniteEtale.Cover (Spec R) :=
  ⟨(G.inclusions.obj n).X, (G.finiteLocallyFree n).1, G.finiteLevel_etale hp n⟩

end Langlands.PDivisibleGroup
