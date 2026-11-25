import Langlands.Geometry.FormalGroup.RamifiedSpecialPDivisible
import Langlands.Geometry.FormalGroup.PDivisibleOrderRigidifier
import Langlands.Geometry.FormalGroup.PDivisibleSplitBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleSplitHeight
import Langlands.Geometry.FormalGroup.NilpotentReduction

/-! # Split polarized C1 data on actual p-divisible groups over an affine test -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

universe u v s

open CategoryTheory ValuativeRel

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{v}} {p : ℕ} [Fact p.Prime] {G H : PDivisibleGroup R p}
variable {A : Type u} [Ring A] {a : A →+* End G} {b : A →+* End H}

/-- An actual order-linear tower isomorphism induces an order-linear quasi-isogeny. -/
def OrderQuasiIsogeny.ofIso (e : G ≅ H) (h : ∀ t, (a t).asHom ≫ e.hom = e.hom ≫ (b t).asHom) :
    OrderQuasiIsogeny a b where
  val := RationalCategory.inclusion.mapIso e
  commutes t := by
    change RationalHom.comp (RationalHom.ofHom (a t).asHom) (RationalHom.ofHom e.hom) =
      RationalHom.comp (RationalHom.ofHom e.hom) (RationalHom.ofHom (b t).asHom)
    rw [← RationalHom.ofHom_comp, ← RationalHom.ofHom_comp, h t]

section CommonBase

open GroupScheme.Cartier

variable {R₁ R₂ S : Type v} [CommRing R₁] [CommRing R₂] [CommRing S]
  [Algebra R₁ S] [Algebra R₂ S]
variable {G₁ : PDivisibleGroup (CommRingCat.of R₁) p}
  {G₂ : PDivisibleGroup (CommRingCat.of R₂) p}

/-- Transport the split rigidifier across the two split base-change comparisons. -/
def splitOrderRigidifierOnBaseChange (hExact : FiniteCartierDualExactnessStatement.{v})
    (a₁ : A →+* End G₁) (a₂ : A →+* End G₂)
    (q : OrderQuasiIsogeny ((baseChangeEnd (S := S) G₁).comp a₁)
      ((baseChangeEnd (S := S) G₂).comp a₂)) (c : ℚ_[p]ˣ) :
    OrderQuasiIsogeny
      ((baseChangeEnd (S := S) (G₁.splitWithDual hExact)).comp (splitOrderAction a₁ hExact))
      ((baseChangeEnd (S := S) (G₂.splitWithDual hExact)).comp (splitOrderAction a₂ hExact)) := by
  let e₁ := OrderQuasiIsogeny.ofIso
    (a := (baseChangeEnd (S := S) (G₁.splitWithDual hExact)).comp (splitOrderAction a₁ hExact))
    (b := splitOrderAction ((baseChangeEnd (S := S) G₁).comp a₁) hExact)
    (baseChangeSplitIso (S := S) G₁ hExact)
    (baseChangeSplitIso_order (S := S) G₁ hExact a₁)
  let e₂ := OrderQuasiIsogeny.ofIso
    (a := (baseChangeEnd (S := S) (G₂.splitWithDual hExact)).comp (splitOrderAction a₂ hExact))
    (b := splitOrderAction ((baseChangeEnd (S := S) G₂).comp a₂) hExact)
    (baseChangeSplitIso (S := S) G₂ hExact)
    (baseChangeSplitIso_order (S := S) G₂ hExact a₂)
  exact e₁.trans ((splitOrderRigidifier hExact q c).trans e₂.symm)

end CommonBase

end Langlands.PDivisibleGroup

namespace Langlands.FormalGroup.Harris

open LocalDivision CentralDivision CentralSimple GroupScheme.Cartier PDivisibleGroup

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {W : Type v} [CommRing W] [Algebra 𝒪[K] W] {π : 𝒪[K]}
variable {p e : ℕ} [Fact p.Prime] {b : 𝒪[K]ˣ}

local notation "πW" => algebraMap 𝒪[K] W π

local instance splitPointTestAlgebra (T : Nilp.{v, v} W πW) : Algebra 𝒪[K] T.obj :=
  Algebra.compHom T.obj (algebraMap 𝒪[K] W)

/-- The test's special fibre is the actual quotient by the central uniformizer. -/
abbrev specialFibre (T : Nilp.{v, v} W πW) := Nilp.Reduction πW T.obj

/-- Split special polarized data in the affine coordinate chart. The target is
an actual special formal module and the two primal towers are pulled back to
the special fibre before specifying the rigidifier. -/
structure SplitPDivisibleAffinePoint
    (Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := ResidueRing W πW) π)
    (hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e) (he : 0 < e) (T : Nilp.{v, v} W πW) where
  target : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := T.obj) π
  primalRigidifier : OrderQuasiIsogeny
    ((baseChangeEnd (S := specialFibre T) (Φ.pDivisibleGroup hp he)).comp (Φ.pDivisibleAction hp he))
    ((baseChangeEnd (S := specialFibre T) (target.pDivisibleGroup hp he)).comp (target.pDivisibleAction hp he))
  multiplier : ℚ_[p]ˣ

namespace SplitPDivisibleAffinePoint

variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι)
  (R := ResidueRing W (algebraMap 𝒪[K] W π)) π}
variable {hp : (p : 𝒪[K]) = (b : 𝒪[K]) * π ^ e} {he : 0 < e}
variable {T : Nilp.{v, v} W (algebraMap 𝒪[K] W π)}
variable (X : SplitPDivisibleAffinePoint (π := π) (W := W) Φ hp he T)
variable (hExact : FiniteCartierDualExactnessStatement.{v})

open SpecialModule.HeightSquaredModule

/-- The actual split target of the point over the original test. -/
def targetTower : PDivisibleGroup (CommRingCat.of T.obj) p :=
  splitPDivisibleGroup (R := T.obj) X.target hp he hExact

/-- The tautological alternating polarization of the actual target. -/
def polarization : (X.targetTower hExact).PrincipalPolarization :=
  splitPDivisiblePolarization (R := T.obj) X.target hp he hExact

/-- The full split order acts on the polarized target. -/
def orderAction : (IntegerRing K D)ᵐᵒᵖ × IntegerRing K D →+* End (X.targetTower hExact) :=
  splitPDivisibleAction (R := T.obj) X.target hp he hExact

/-- The height of the actual target is twice the computed primal height. -/
theorem targetTower_hasHeight {f : ℕ} (hq : Nat.card 𝓀[K] = p ^ f) :
    (X.targetTower hExact).HasHeight (2 * (e * f * (reducedDegree K D) ^ 2)) :=
  (pDivisibleGroup_hasHeight (R := T.obj) X.target hp he hq).splitWithDual hExact

/-- The order-linear rigidifier between the actual special fibres of the
polarized frame and target, formed from the primal rigidifier and one multiplier. -/
def rigidifier : OrderQuasiIsogeny
    ((baseChangeEnd (S := specialFibre (π := π) T) (Φ.splitPDivisibleGroup hp he hExact)).comp
      (Φ.splitPDivisibleAction hp he hExact))
    ((baseChangeEnd (S := specialFibre (π := π) T) (X.targetTower hExact)).comp
      (X.orderAction hExact)) :=
  splitOrderRigidifierOnBaseChange (S := specialFibre (π := π) T) hExact
    (Φ.pDivisibleAction hp he) (pDivisibleAction (R := T.obj) X.target hp he)
    X.primalRigidifier X.multiplier

end SplitPDivisibleAffinePoint
end Langlands.FormalGroup.Harris
