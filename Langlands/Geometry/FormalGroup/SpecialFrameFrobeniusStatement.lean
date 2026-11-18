import Langlands.Geometry.FormalGroup.RelativeFrobenius
import Langlands.Geometry.FormalGroup.SpecialModule
import Langlands.Geometry.FormalGroup.OrderRationalMorphism

/-! # Actual global rational invertibility of Frobenius on a special frame -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.LocalDivision.SpecialModule

open ValuativeRel CentralDivision ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}

/-- The actual relative Frobenius of a supplied height-certified special frame
has an actual inverse in the whole global rational full-order Hom. -/
def RelativeFrobeniusQuasiIsogenyStatement
    (Φ : HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
    (p n : ℕ) [ExpChar κ p] : Prop :=
  ∀ (θ : κ →ₐ[𝒪[K]] κ) (hθ : θ.toRingHom = iterateFrobenius κ p n),
    ∃ q : ModuleLaw.OrderAction.QuasiIsogeny K Φ.val.order (Φ.val.order.map θ),
      q.hom = ModuleLaw.OrderAction.RationalHom.ofHom (Φ.val.order.frobeniusHom p n θ hθ)

/-- The specified actual Frobenius forward tensor determines the whole quasi-isogeny uniquely. -/
theorem frobeniusQuasiIsogeny_unique
    (Φ : HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
    (p n : ℕ) [ExpChar κ p] (θ : κ →ₐ[𝒪[K]] κ)
    (hθ : θ.toRingHom = iterateFrobenius κ p n)
    (a b : ModuleLaw.OrderAction.QuasiIsogeny K Φ.val.order (Φ.val.order.map θ))
    (ha : a.hom = ModuleLaw.OrderAction.RationalHom.ofHom (Φ.val.order.frobeniusHom p n θ hθ))
    (hb : b.hom = ModuleLaw.OrderAction.RationalHom.ofHom (Φ.val.order.frobeniusHom p n θ hθ)) : a = b :=
  ModuleLaw.OrderAction.QuasiIsogeny.ext (ha.trans hb.symm)

/-- A proof of the full inverse target supplies an actual specified-forward Frobenius quasi-isogeny. -/
def frobeniusQuasiIsogenyOfStatement
    (Φ : HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
    (p n : ℕ) [ExpChar κ p] (h : RelativeFrobeniusQuasiIsogenyStatement Φ p n)
    (θ : κ →ₐ[𝒪[K]] κ) (hθ : θ.toRingHom = iterateFrobenius κ p n) :
    ModuleLaw.OrderAction.QuasiIsogeny K Φ.val.order (Φ.val.order.map θ) :=
  (h θ hθ).choose

/-- The conditional inverse construction has exactly the original actual Frobenius forward tensor. -/
@[simp]
theorem frobeniusQuasiIsogenyOfStatement_hom
    (Φ : HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π)
    (p n : ℕ) [ExpChar κ p] (h : RelativeFrobeniusQuasiIsogenyStatement Φ p n)
    (θ : κ →ₐ[𝒪[K]] κ) (hθ : θ.toRingHom = iterateFrobenius κ p n) :
    (frobeniusQuasiIsogenyOfStatement Φ p n h θ hθ).hom =
      ModuleLaw.OrderAction.RationalHom.ofHom (Φ.val.order.frobeniusHom p n θ hθ) :=
  (h θ hθ).choose_spec

end Langlands.FormalGroup.LocalDivision.SpecialModule
