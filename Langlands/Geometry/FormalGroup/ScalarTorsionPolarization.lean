import Langlands.Geometry.FormalGroup.OrderAction
import Langlands.Geometry.FormalGroup.ScalarTorsionCharacters
import Langlands.Geometry.FormalGroup.ScalarTorsionSchemeHom
import Langlands.AlgebraicGeometry.Picard.KernelCartierDuality
import Langlands.Shimura.Unitary.Involution

/-! # Cartier duality and polarizations on the actual scalar-power kernels -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite _root_.AlgebraicGeometry
open Langlands.GroupScheme Langlands.Shimura
open scoped CategoryTheory.MonObj CategoryTheory.Obj

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

/-- A coherent identification of one actual torsion system with the Cartier dual of another. -/
structure TorsionCartierDuality (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) where
  level (n : ℕ) : additivePoints (hM.torsionSchemeInclusions.obj n).toGrp ≅
    hN.torsionCharacters n
  inclusion {m n : ℕ} (i : m ⟶ n) (T : Over (Spec (CommRingCat.of R)))
      (x : T ⟶ (hM.torsionSchemeInclusions.obj m).X) :
    (level n).hom.app (op T)
        (Additive.ofMul (x ≫ (hM.torsionSchemeInclusions.map i).toMul.hom.hom)) =
      (hN.torsionCharacterInclusions.map i).app (op T)
        ((level m).hom.app (op T) (Additive.ofMul x))

namespace TorsionCartierDuality

variable {hM : M.IsPiDivisible π} {hN : N.IsPiDivisible π}
variable {T T' : Over (Spec (CommRingCat.of R))}

/-- Evaluate the relative character supplied by the first point on the second point. -/
def pairing (e : TorsionCartierDuality hM hN)
    (n : ℕ) (x : T ⟶ (hM.torsionSchemeInclusions.obj n).X)
    (y : T ⟶ (hN.torsionSchemeInclusions.obj n).X) :
    T ⟶ (Gm (Spec (CommRingCat.of R))).X :=
  Cartier.evaluation (G := hN.torsionSchemeInclusions.obj n)
    (H := Gm (Spec (CommRingCat.of R))) ((e.level n).hom.app (op T) (Additive.ofMul x)) y

variable (e : TorsionCartierDuality hM hN)

theorem pairing_mul_left (n : ℕ) (x x' : T ⟶ (hM.torsionSchemeInclusions.obj n).X)
    (y : T ⟶ (hN.torsionSchemeInclusions.obj n).X) :
    e.pairing n (x * x') y = e.pairing n x y * e.pairing n x' y := by
  change Cartier.evaluation ((e.level n).hom.app (op T)
    (Additive.ofMul x + Additive.ofMul x')) y = _
  erw [map_add, Cartier.evaluation_add]
  rfl

theorem pairing_mul_right (n : ℕ) (x : T ⟶ (hM.torsionSchemeInclusions.obj n).X)
    (y y' : T ⟶ (hN.torsionSchemeInclusions.obj n).X) :
    e.pairing n x (y * y') = e.pairing n x y * e.pairing n x y' :=
  Cartier.evaluation_mul _ _ _

/-- The pairing is natural on all scheme tests over the affine coefficient base. -/
theorem pairing_restrict (n : ℕ) (a : T' ⟶ T)
    (x : T ⟶ (hM.torsionSchemeInclusions.obj n).X)
    (y : T ⟶ (hN.torsionSchemeInclusions.obj n).X) :
    e.pairing n (a ≫ x) (a ≫ y) = a ≫ e.pairing n x y := by
  have h := congrArg (fun k => k (Additive.ofMul x)) ((e.level n).hom.naturality a.op)
  change (e.level n).hom.app (op T') (Additive.ofMul (a ≫ x)) =
    Cartier.restrict _ _ a ((e.level n).hom.app (op T) (Additive.ofMul x)) at h
  unfold pairing
  rw [h]
  exact Cartier.evaluation_restrict a ((e.level n).hom.app (op T) (Additive.ofMul x)) y

/-- Inclusions on the first group and scalar transitions on the second are adjoint. -/
theorem pairing_inclusion {m n : ℕ} (i : m ⟶ n)
    (x : T ⟶ (hM.torsionSchemeInclusions.obj m).X)
    (y : T ⟶ (hN.torsionSchemeInclusions.obj n).X) :
    e.pairing n (x ≫ (hM.torsionSchemeInclusions.map i).toMul.hom.hom) y =
      e.pairing m x (y ≫ (hN.torsionSchemeTower.map i.op).toMul.hom.hom) := by
  unfold pairing
  rw [e.inclusion]
  exact hN.evaluation_torsionCharacterInclusions_map i _ y

end TorsionCartierDuality

/-- A principal polarization is an antisymmetric self-duality of the actual scalar kernels. -/
structure TorsionPrincipalPolarization (hM : M.IsPiDivisible π)
    extends TorsionCartierDuality hM hM where
  skew (n : ℕ) (T : Over (Spec (CommRingCat.of R)))
      (x y : T ⟶ (hM.torsionSchemeInclusions.obj n).X) :
    toTorsionCartierDuality.pairing n x y = (toTorsionCartierDuality.pairing n y x)⁻¹

namespace TorsionPrincipalPolarization

variable {hM : M.IsPiDivisible π}

/-- Antisymmetry also makes scalar transition on the first argument adjoint to
inclusion on the second. -/
theorem pairing_transition (polarization : TorsionPrincipalPolarization hM)
    {m n : ℕ} (i : m ⟶ n) {T : Over (Spec (CommRingCat.of R))}
    (x : T ⟶ (hM.torsionSchemeInclusions.obj n).X)
    (y : T ⟶ (hM.torsionSchemeInclusions.obj m).X) :
    polarization.toTorsionCartierDuality.pairing m
        (x ≫ (hM.torsionSchemeTower.map i.op).toMul.hom.hom) y =
      polarization.toTorsionCartierDuality.pairing n x
        (y ≫ (hM.torsionSchemeInclusions.map i).toMul.hom.hom) := by
  rw [polarization.skew m T, ← polarization.toTorsionCartierDuality.pairing_inclusion i y x]
  exact (polarization.skew n T x _).symm

end TorsionPrincipalPolarization

namespace OrderAction

variable {A : Type w} [Ring A] [Algebra O A]
variable (E : OrderAction A M) {hM : M.IsPiDivisible π}
variable (star : AlgebraInvolution O A) (polarization : TorsionPrincipalPolarization hM)

/-- The order action and its involution are adjoint under the principal polarization. -/
def IsAntilinearTorsionPolarization : Prop :=
  ∀ (a : A) (n : ℕ) (T : Over (Spec (CommRingCat.of R)))
      (x : T ⟶ (hM.torsionSchemeInclusions.obj n).X),
    (polarization.level n).hom.app (op T)
        (Additive.ofMul (x ≫ ((E.action a).scalarTorsionSchemeMap hM hM n).toMul.hom.hom)) =
      Cartier.precompose (Gm (Spec (CommRingCat.of R)))
        ((E.action (star a)).scalarTorsionSchemeMap hM hM n) T
        ((polarization.level n).hom.app (op T) (Additive.ofMul x))

/-- Evaluating the character identity gives the pointwise adjointness law. -/
theorem IsAntilinearTorsionPolarization.pairing
    (hpolarization : E.IsAntilinearTorsionPolarization star polarization)
    (a : A) (n : ℕ) {T : Over (Spec (CommRingCat.of R))}
    (x y : T ⟶ (hM.torsionSchemeInclusions.obj n).X) :
    polarization.toTorsionCartierDuality.pairing n
        (x ≫ ((E.action a).scalarTorsionSchemeMap hM hM n).toMul.hom.hom) y =
      polarization.toTorsionCartierDuality.pairing n x
        (y ≫ ((E.action (star a)).scalarTorsionSchemeMap hM hM n).toMul.hom.hom) := by
  unfold TorsionCartierDuality.pairing
  rw [hpolarization a n T x]
  exact Cartier.evaluation_precompose _ _ _

end OrderAction

end Langlands.FormalGroup.ModuleLaw
