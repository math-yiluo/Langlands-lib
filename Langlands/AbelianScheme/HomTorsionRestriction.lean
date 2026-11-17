import Langlands.AbelianScheme.Rational
import Langlands.AlgebraicGeometry.Picard.PolarizedAutomorphismRosati
import Langlands.AbelianScheme.Tate.IntegralReflectionAlgebra
import Langlands.AbelianScheme.Tate.ConnectedTorsionDetection
import Langlands.AbelianScheme.TorsionFiniteEtale
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Finite torsion restriction of actual integral Hom groups -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} {A B : AbelianScheme S}

/-- Restriction of an actual homomorphism to the level-`n` points on a test scheme. -/
def homTorsionRestriction (T : Over S) (n : ℕ) :
    (A ⟶ B) →ₗ[ℤ] (Tate.Level A T n → Tate.Level B T n) :=
  AddMonoidHom.toIntLinearMap {
    toFun := fun f x => Tate.levelMap T f n x
    map_zero' := by
      funext x
      apply GroupScheme.Tate.toSection_injective
      change (Additive.toMul x).val ≫ (1 : A.toGrp ⟶ B.toGrp).hom.hom = 1
      exact MonObj.comp_one _
    map_add' := by
      intro f g
      funext x
      apply GroupScheme.Tate.toSection_injective
      change (Additive.toMul x).val ≫ (groupHom f * groupHom g).hom.hom =
        ((Additive.toMul x).val ≫ (groupHom f).hom.hom) *
          ((Additive.toMul x).val ≫ (groupHom g).hom.hom)
      exact MonObj.comp_mul _ _ _ }

variable {k : Type u} [Field k]

/-- A positive integer is invertible in the global sections of a characteristic-zero field. -/
theorem field_nat_isUnit [CharZero k] {n : ℕ} (hn : 0 < n) :
    IsUnit (n : Γ(Spec (CommRingCat.of k), ⊤)) := by
  simpa using (Ne.isUnit (Nat.cast_ne_zero.mpr hn.ne' : (n : k) ≠ 0)).map
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

variable (A B : AbelianScheme (Spec (CommRingCat.of k)))

/-- Every positive geometric torsion level is a finite set. -/
theorem torsionLevel_finite [IsAlgClosed k] [CharZero k] (n : ℕ) (hn : 0 < n) :
    Finite (Tate.Level A (Over.mk (𝟙 (Spec (CommRingCat.of k)))) n) :=
  Tate.level_finite (𝟙 _) (Langlands.AlgebraicGeometry.FiniteEtale.geometricFiberFinite (𝟙 _))
    torsionFiniteEtale A n hn (field_nat_isUnit hn)

/-- The kernel of restriction to geometric `n`-torsion is exactly `n Hom`. -/
theorem homTorsionRestriction_ker [IsAlgClosed k] [CharZero k] (n : ℕ) (hn : 0 < n) :
    LinearMap.ker (homTorsionRestriction (A := A) (B := B) (Over.mk (𝟙 _)) n) =
      LinearMap.range (LinearMap.lsmul ℤ (A ⟶ B) n) := by
  ext f
  constructor
  · intro hf
    have hz : ∀ x : Tate.Level A (Over.mk (𝟙 _)) n,
        Tate.levelMap (Over.mk (𝟙 _)) f n x = 0 := fun x => congrFun hf x
    have hker := Tate.kernel_comp_eq_one_of_levelMap_eq_zero
      torsionFiniteEtale (𝟙 _) f n hn (field_nat_isUnit hn) hz
    let hnisog := multiplication_isIsogeny_of_ne_zero A n
      (Nat.cast_ne_zero.mpr hn.ne')
    let g : A ⟶ B :=
      Additive.ofMul (GroupScheme.IsogenyFactorization.lift hnisog (groupHom f) hker)
    have hfac : (n • 𝟙 A) ≫ g = f := by
      apply Additive.toMul.injective
      change groupHom (n • 𝟙 A) ≫ groupHom g = groupHom f
      rw [Tate.groupHom_nsmul_id]
      exact GroupScheme.IsogenyFactorization.fac hnisog (groupHom f) hker
    refine ⟨g, ?_⟩
    simpa only [LinearMap.lsmul_apply, Nat.cast_smul_eq_nsmul,
      Preadditive.nsmul_comp, Category.id_comp] using hfac
  · rintro ⟨g, rfl⟩
    change homTorsionRestriction (Over.mk (𝟙 _)) n ((n : ℤ) • g) = 0
    rw [map_smul]
    funext x
    change (n : ℤ) • Tate.levelMap (Over.mk (𝟙 _)) g n x = 0
    rw [Nat.cast_smul_eq_nsmul]
    exact GroupScheme.Tate.level_nsmul_eq_zero B.toGrp _ n _

/-- The actual integral Hom group has a finite quotient modulo every positive integer. -/
theorem hom_modN_finite [IsAlgClosed k] [CharZero k] (n : ℕ) (hn : 0 < n) :
    Finite (ModN (A ⟶ B) n) := by
  let T := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let R := homTorsionRestriction (A := A) (B := B) T n
  haveI := torsionLevel_finite A n hn
  haveI := torsionLevel_finite B n hn
  have hfin : Finite ((A ⟶ B) ⧸ LinearMap.ker R) :=
    Finite.of_injective R.quotKerEquivRange R.quotKerEquivRange.injective
  simpa only [R, T, homTorsionRestriction_ker A B n hn] using hfin

end Langlands.AbelianScheme
