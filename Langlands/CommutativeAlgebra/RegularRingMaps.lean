import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Geometric regularity, regular algebra maps and G-rings -/

universe u v w

namespace Langlands.CommutativeAlgebra

open TensorProduct

/-- A Noetherian field algebra is geometrically regular if it remains regular
after every finite purely inseparable extension of the field. -/
def GeometricallyRegular (k : Type u) [Field k] (A : Type v)
    [CommRing A] [Algebra k A] : Prop :=
  IsNoetherianRing A ∧
    ∀ (k' : Type u) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'], IsRegularRing (k' ⊗[k] A)

/-- The algebra map is flat and all its actual prime fibres are Noetherian
geometrically regular algebras over the corresponding residue fields. -/
def RegularAlgebra (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  Module.Flat R S ∧
    ∀ (p : Ideal R) [p.IsPrime], GeometricallyRegular p.ResidueField (p.Fiber S)

/-- A G-ring is Noetherian and every prime localization has a regular canonical
map to its maximal-ideal adic completion. -/
def IsGRing (R : Type u) [CommRing R] : Prop :=
  IsNoetherianRing R ∧
    ∀ (p : Ideal R) [p.IsPrime],
      RegularAlgebra (Localization.AtPrime p)
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (Localization.AtPrime p))

section GeometricRegularity

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]

/-- Geometric regularity includes ordinary regularity. -/
theorem GeometricallyRegular.isRegularRing (h : GeometricallyRegular k A) :
    IsRegularRing A := by
  letI := h.2 k
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.lid k A).toRingEquiv

/-- Transport geometric regularity along an algebra equivalence. -/
theorem GeometricallyRegular.of_algEquiv {B : Type w} [CommRing B] [Algebra k B]
    (h : GeometricallyRegular k A) (e : A ≃ₐ[k] B) :
    GeometricallyRegular k B := by
  letI := h.1
  refine ⟨isNoetherianRing_of_ringEquiv A e.toRingEquiv, ?_⟩
  intro k' _ _ _ _
  letI := h.2 k'
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : k' ≃ₐ[k] k') e).toRingEquiv

/-- A field is geometrically regular over itself. -/
theorem geometricallyRegular_self (k : Type u) [Field k] :
    GeometricallyRegular k k := by
  refine ⟨inferInstance, ?_⟩
  intro k' _ _ _ _
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.rid k k k').symm.toRingEquiv

end GeometricRegularity

section RegularAlgebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

theorem RegularAlgebra.flat (h : RegularAlgebra R S) : Module.Flat R S :=
  h.1

theorem RegularAlgebra.geometricallyRegular_fiber (h : RegularAlgebra R S)
    (p : Ideal R) [p.IsPrime] : GeometricallyRegular p.ResidueField (p.Fiber S) :=
  h.2 p

end RegularAlgebra

theorem IsGRing.isNoetherianRing {R : Type u} [CommRing R] (h : IsGRing R) :
    IsNoetherianRing R :=
  h.1

theorem IsGRing.regularAlgebra_completion {R : Type u} [CommRing R] (h : IsGRing R)
    (p : Ideal R) [p.IsPrime] :
    RegularAlgebra (Localization.AtPrime p)
      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p)) :=
  h.2 p

end Langlands.CommutativeAlgebra
