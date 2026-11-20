import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Integral

/-! # Normalization after tensoring an integral algebra tower -/

open TensorProduct

noncomputable section

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

section Tensor

variable (R S A B G : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [CommRing A] [CommRing B] [CommRing G]
    [Algebra R A] [Algebra R B] [Algebra R G] [Algebra A B] [Algebra A G] [Algebra B G]
    [IsScalarTower R A B] [IsScalarTower R A G] [IsScalarTower R B G]

variable {B G} in
/-- The algebra structure on a tensor base change from a map in a scalar tower. -/
@[instance_reducible]
def tensorBaseChangeAlgebra : Algebra (S ⊗[R] A) (S ⊗[R] B) :=
  (Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R A B)).toAlgebra

local notation "A'" => S ⊗[R] A
local notation "B'" => S ⊗[R] B
local notation "G'" => S ⊗[R] G

variable {B G} in
theorem tensorBaseChangeAlgebra_isScalarTower :
    letI := tensorBaseChangeAlgebra R S A (B := B)
    IsScalarTower S A' B' := by
  let : Algebra A' B' := tensorBaseChangeAlgebra R S A
  exact IsScalarTower.of_algebraMap_eq fun s =>
    ((Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom R A B)).commutes s).symm

/-- The tensor base-change algebra map is integral if the original algebra map is. -/
theorem integral_tensorBaseChange [Algebra.IsIntegral A B] :
    letI := tensorBaseChangeAlgebra R S A (B := B)
    Algebra.IsIntegral A' B' := by
  let : Algebra A' B' := tensorBaseChangeAlgebra R S A
  constructor
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s b =>
    let f : A →+* A' := (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom
    let g : B →+* B' := (Algebra.TensorProduct.includeRight (R := R) (A := S)).toRingHom
    have hi : IsIntegral A' (g b) :=
      (Algebra.IsIntegral.isIntegral (R := A) b).map_of_comp_eq f g rfl
    have hs := hi.smul (s ⊗ₜ[R] (1 : A))
    rw [Algebra.smul_def] at hs
    change IsIntegral A' ((s ⊗ₜ[R] algebraMap A B 1) * (1 ⊗ₜ[R] b)) at hs
    simpa only [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] using hs
  | add x y hx hy => exact hx.add hy

/-- After tensor base change, integral closure can be computed from any integral
intermediate algebra in the original tower. -/
def integralClosureTensorTowerEquiv [IsScalarTower A B G] [Algebra.IsIntegral A B] :
    letI := tensorBaseChangeAlgebra R S A (B := G)
    letI := tensorBaseChangeAlgebra R S B (B := G)
    letI := tensorBaseChangeAlgebra_isScalarTower R S A (B := G)
    letI := tensorBaseChangeAlgebra_isScalarTower R S B (B := G)
    integralClosure A' G' ≃ₐ[S] integralClosure B' G' := by
  let : Algebra A' G' := tensorBaseChangeAlgebra R S A
  let : Algebra B' G' := tensorBaseChangeAlgebra R S B
  let : Algebra A' B' := tensorBaseChangeAlgebra R S A
  have : IsScalarTower S A' G' := tensorBaseChangeAlgebra_isScalarTower R S A
  have : IsScalarTower S B' G' := tensorBaseChangeAlgebra_isScalarTower R S B
  have : IsScalarTower A' B' G' := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      change s ⊗ₜ[R] algebraMap A G a = s ⊗ₜ[R] algebraMap B G (algebraMap A B a)
      rw [IsScalarTower.algebraMap_apply A B G]
    | add a b ha hb => simp only [map_add, ha, hb]
  have : Algebra.IsIntegral A' B' := integral_tensorBaseChange R S A B
  have h : integralClosure A' G' = (integralClosure B' G').restrictScalars A' := by
    ext x
    change IsIntegral A' x ↔ IsIntegral B' x
    exact ⟨IsIntegral.tower_top, isIntegral_trans (R := A') (A := B') x⟩
  exact
    { (Subalgebra.equivOfEq _ _ h).toRingEquiv with
      commutes' := fun _ => Subtype.ext rfl }

end Tensor

section Localization

variable {A Aₘ G Gₘ : Type*} [CommRing A] [CommRing Aₘ] [CommRing G] [CommRing Gₘ]
    [Algebra A G] [Algebra A Aₘ] [Algebra A Gₘ] [Algebra G Gₘ] [Algebra Aₘ Gₘ]
    [IsScalarTower A G Gₘ] [IsScalarTower A Aₘ Gₘ]

/-- The map on integral closures induced by a commutative square of algebra rings. -/
def integralClosureLocalizedMap : integralClosure A G →ₐ[A] integralClosure Aₘ Gₘ :=
  ((IsScalarTower.toAlgHom A G Gₘ).comp (integralClosure A G).val).codRestrict
    ((integralClosure Aₘ Gₘ).restrictScalars A) fun x =>
      (x.property.map (IsScalarTower.toAlgHom A G Gₘ)).tower_top

/-- The localized integral closure agrees with the integral closure of the
localized base in the localized target. -/
def localizationIntegralClosureEquiv (M : Submonoid A) [IsLocalization M Aₘ]
    [IsLocalization (Algebra.algebraMapSubmonoid G M) Gₘ] :
    letI : Algebra (integralClosure A G) (integralClosure Aₘ Gₘ) :=
      (integralClosureLocalizedMap (A := A) (G := G) (Aₘ := Aₘ) (Gₘ := Gₘ)).toRingHom.toAlgebra
    Localization (Algebra.algebraMapSubmonoid (integralClosure A G) M) ≃ₐ[integralClosure A G]
      integralClosure Aₘ Gₘ := by
  let : Algebra (integralClosure A G) (integralClosure Aₘ Gₘ) :=
    integralClosureLocalizedMap.toRingHom.toAlgebra
  have : IsScalarTower A (integralClosure A G) (integralClosure Aₘ Gₘ) :=
    IsScalarTower.of_algebraMap_eq fun _ => (integralClosureLocalizedMap.commutes _).symm
  have : IsScalarTower (integralClosure A G) (integralClosure Aₘ Gₘ) Gₘ :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let M' := Algebra.algebraMapSubmonoid (integralClosure A G) M
  have : IsLocalization M' (integralClosure Aₘ Gₘ) := IsLocalization.integralClosure M
  exact IsLocalization.algEquiv M' _ _

end Localization

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
