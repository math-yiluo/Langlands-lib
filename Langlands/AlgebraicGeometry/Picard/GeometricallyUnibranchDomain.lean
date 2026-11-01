import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RingHom.PurelyInseparable

/-! # Geometric unibranchness for local domains -/

universe u

open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- The geometric-unibranch condition specialized to a local domain:
its normalization is local and the induced residue extension is purely
inseparable. -/
def GeometricallyUnibranchDomain (R : Type u) [CommRing R] [IsDomain R]
    [IsLocalRing R] : Prop :=
  ∃ hB : IsLocalRing (integralClosure R (FractionRing R)),
    letI := hB
    ∃ hf : IsLocalHom (algebraMap R (integralClosure R (FractionRing R))),
      letI := hf
      (IsLocalRing.ResidueField.map
        (algebraMap R (integralClosure R (FractionRing R)))).IsPurelyInseparable

/-- A local integrally closed domain satisfies the actual normalization
and residue-extension condition. -/
theorem geometricallyUnibranchDomain_of_isIntegrallyClosed
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsIntegrallyClosed R] : GeometricallyUnibranchDomain R := by
  let B := integralClosure R (FractionRing R)
  let f : R →+* B := algebraMap R B
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral z.property
    exact ⟨r, Subtype.ext hr⟩
  let hB : IsLocalRing B := IsLocalRing.of_surjective' f hf
  let hlocal : IsLocalHom f := IsLocalHom.of_surjective f hf
  refine ⟨hB, hlocal, ?_⟩
  let g := IsLocalRing.ResidueField.map f
  have hg : Function.Surjective g := by
    intro z
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := B) z
    obtain ⟨r, rfl⟩ := hf b
    exact ⟨IsLocalRing.residue R r, IsLocalRing.ResidueField.map_residue f r⟩
  change g.IsPurelyInseparable
  let : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B) :=
    g.toAlgebra
  change IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField B)
  apply isPurelyInseparable_iff.mpr
  intro z
  obtain ⟨r, rfl⟩ := hg z
  exact ⟨isIntegral_algebraMap, fun _ => ⟨r, rfl⟩⟩

/-- Stalkwise geometric unibranchness, specialized to an integral scheme. -/
def GeometricallyUnibranchIntegralScheme (S : Scheme.{u}) [IsIntegral S] : Prop :=
  ∀ x : S, GeometricallyUnibranchDomain (S.presheaf.stalk x)

/-- On an integral scheme, integral closedness of every actual stalk
implies the geometric-unibranch condition at every point. -/
theorem geometricallyUnibranchIntegralScheme_of_stalks
    (S : Scheme.{u}) [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)) :
    GeometricallyUnibranchIntegralScheme S := by
  intro x
  let := hS x
  exact geometricallyUnibranchDomain_of_isIntegrallyClosed (S.presheaf.stalk x)

end Langlands.AlgebraicGeometry
