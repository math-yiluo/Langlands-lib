import Langlands.ClassFieldTheory.Local.Galois
import Langlands.Weil.Pullback
import Mathlib.Analysis.Complex.Basic

/-!
# Abelianized integer-Frobenius pullbacks

These are actual closed-commutator and inertia quotients of the existing
`Weil.Pullback`, with their quotient topologies. A local residue-degree map is
an explicit input; this module does not construct or identify that map.
-/

noncomputable section

namespace Langlands.LocalClassField.WeilQuotients

universe u v

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  (φ : Γ →ₜ* Weil.ProfiniteIntegers)

/-- The existing pullback divided by its closed commutator subgroup.
Its topology is the quotient of the Weil pullback topology. -/
abbrev Abelianization := TopologicalAbelianization (Weil.Pullback φ)

/-- The actual continuous quotient projection. -/
def projection : Weil.Pullback φ →ₜ* Abelianization φ :=
  abelianizationProjection _

/-- Integer degree descends continuously to the abelianization. -/
def degree : Abelianization φ →ₜ* Weil.Degree :=
  abelianizationLift (Weil.degree φ)

/-- The continuous comparison from the Weil abelianization to the
abelianization of the original group. It is not asserted to be an isomorphism. -/
def toGroupAbelianization : Abelianization φ →ₜ* TopologicalAbelianization Γ :=
  abelianizationMap (Weil.projection φ)

/-- The degree-zero subgroup of the actual abelianization. -/
def inertia : Subgroup (Abelianization φ) := (degree φ).toMonoidHom.ker

/-- The degree-zero subgroup is exactly the image of the original inertia
under the quotient map. This is an intrinsic quotient calculation. -/
theorem inertia_eq_image :
    inertia φ = (Weil.inertiaSubgroup φ).map (projection φ).toMonoidHom := by
  ext x
  refine QuotientGroup.induction_on x ?_
  intro w
  constructor
  · intro hw
    exact ⟨w, hw, rfl⟩
  · rintro ⟨v, hv, h⟩
    have hv' : degree φ (projection φ v) = 1 := hv
    change projection φ v = QuotientGroup.mk w at h
    change degree φ (QuotientGroup.mk w) = 1
    rw [h] at hv'
    exact hv'

/-- The actual quotient by inertia, with the quotient topology. -/
abbrev UnramifiedQuotient := Abelianization φ ⧸ inertia φ

/-- The continuous projection to the unramified quotient. -/
def unramifiedProjection : Abelianization φ →ₜ* UnramifiedQuotient φ where
  toMonoidHom := QuotientGroup.mk' _
  continuous_toFun := QuotientGroup.continuous_mk

/-- The quotient by inertia is canonically the image of degree, with its
discrete subspace topology. No surjectivity premise is needed. -/
def unramifiedDegreeEquivRange :
    UnramifiedQuotient φ ≃ₜ* (degree φ).toMonoidHom.range := by
  refine { QuotientGroup.quotientKerEquivRange (degree φ).toMonoidHom with
    continuous_toFun := ?_
    continuous_invFun := continuous_of_discreteTopology }
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact (degree φ).continuous.subtype_mk _

/-- If the original pullback degree is onto, its unramified quotient is
continuously isomorphic to the discrete integers. The hypothesis is explicit. -/
def unramifiedDegreeEquiv (h : Function.Surjective (Weil.degree φ)) :
    UnramifiedQuotient φ ≃ₜ* Weil.Degree := by
  have hd : Function.Surjective (degree φ) := by
    intro n
    obtain ⟨w, hw⟩ := h n
    exact ⟨projection φ w, hw⟩
  refine { QuotientGroup.quotientKerEquivOfSurjective
      (degree φ).toMonoidHom hd with
    continuous_toFun := ?_
    continuous_invFun := continuous_of_discreteTopology }
  exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
    (degree φ).continuous

/-- Continuous complex characters factor through the genuine topological
abelianization, without a local reciprocity assumption. -/
def characterDescent :
    (Weil.Pullback φ →ₜ* ℂˣ) ≃ (Abelianization φ →ₜ* ℂˣ) :=
  abelianizationLiftEquiv

variable {Γ' : Type v} [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ']
  (φ' : Γ' →ₜ* Weil.ProfiniteIntegers)

/-- A specified continuous map between the actual pullbacks induces a
continuous map on their actual abelianizations. Field functoriality must
supply its genuine pullback map; no arbitrary inverse is chosen. -/
def map (f : Weil.Pullback φ →ₜ* Weil.Pullback φ') :
    Abelianization φ →ₜ* Abelianization φ' :=
  abelianizationMap f

end Langlands.LocalClassField.WeilQuotients

namespace Langlands.LocalClassField

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- Specialize to the actual absolute Galois group of a p-adic field and an
explicit continuous residue-degree map. Identifying this map with geometric
residue Frobenius remains an external construction obligation. -/
abbrev localPullbackAbelianization
    (φ : Field.absoluteGaloisGroup F.Carrier →ₜ* Weil.ProfiniteIntegers) :=
  WeilQuotients.Abelianization φ

/-- The actual comparison from this pullback abelianization to the compact
absolute-Galois abelianization. No surjectivity or equivalence is asserted. -/
def localPullbackToGalois
    (φ : Field.absoluteGaloisGroup F.Carrier →ₜ* Weil.ProfiniteIntegers) :
    localPullbackAbelianization F φ →ₜ*
      Field.absoluteGaloisGroupAbelianization F.Carrier :=
  WeilQuotients.toGroupAbelianization φ

end Langlands.LocalClassField
