import Langlands.LocalField.Canonical
import Langlands.LocalField.RelativeIntegers
import Langlands.LocalFactor.Ramification.Galois
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.DedekindDomain.Different

/-! The actual different of a prime totally ramified extension with a supplied
single lower ramification break. -/

namespace Langlands.PadicField.TopologicalData

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {F : PadicField.{u} p} {E : PadicField.{v} p}
variable [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
variable (T : F.TopologicalData) (S : E.TopologicalData)

/-- The supplied extension integer ring is torsion-free over the supplied base
integer ring for the named relative scalars, since the relative integer map is
the restriction of an injective field map. -/
theorem relativeIntegerAlgebra_isTorsionFree :
    letI := relativeIntegerAlgebra T S
    Module.IsTorsionFree T.Integers S.Integers := by
  let := relativeIntegerAlgebra T S
  refine Module.isTorsionFree_iff_algebraMap_injective.mpr ?_
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap F.Carrier E.Carrier).injective
  exact congrArg Subtype.val hxy

end Langlands.PadicField.TopologicalData

namespace Langlands.LocalClassField

universe u v

/-- For a prime totally ramified Galois extension with the supplied single lower
ramification break `t`, the actual different ideal of the supplied integer rings
is the `(t + 1) * (ell - 1)`-th power of the actual maximal ideal. -/
def PrimeRamifiedDifferent : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (L : PadicField.{v} p)
    [Algebra F.Carrier L.Carrier] [IsScalarTower (Padic p) F.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [IsGalois F.Carrier L.Carrier],
    let ell := Module.finrank F.Carrier L.Carrier
    let TF := F.canonicalTopologicalData
    let TL := L.canonicalTopologicalData
    letI := TF.topology
    letI := TF.valuativeRel
    letI := TF.localField
    letI := TL.topology
    letI := TL.valuativeRel
    letI := TL.localField
    letI := PadicField.TopologicalData.relativeIntegerAlgebra TF TL
    letI := PadicField.TopologicalData.relativeIntegerFieldAlgebra (E := L) TF
    haveI := PadicField.TopologicalData.relativeIntegerFieldTower (E := L) TF
    haveI := PadicField.TopologicalData.relativeIntegerTower TF TL
    haveI := PadicField.TopologicalData.relativeIntegerAlgebra_isTorsionFree TF TL
    Nat.Prime ell →
      TL.ramificationIndex = ell * TF.ramificationIndex →
        ∀ t : ℕ,
          (∀ i : ℕ, Ramification.Padic.lowerRamificationGroup TL F.Carrier i =
            if i ≤ t then ⊤ else ⊥) →
          differentIdeal TF.Integers TL.Integers =
            (IsLocalRing.maximalIdeal TL.Integers) ^ ((t + 1) * (ell - 1))

end Langlands.LocalClassField
