import Langlands.BushnellKutzko.DerivedStratum
import Langlands.BushnellKutzko.ElementFieldInvariants

/-! # The refinement theorem (BK93 (2.2.8), printed p. 56; T6) -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uE

variable (F : Type uF) [Field F] [ValuativeRel F]
  {V : Type uV} [AddCommGroup V] [Module F V]

open scoped Classical in
/-- The ramification index of a specified subalgebra when it is a field.
This auxiliary total construction permits `F[β,c]` in the refinement theorem. -/
def subalgebraRamificationIndex (R : Subalgebra F (Module.End F V)) : ℕ :=
  if h : IsField R then
    letI := h.toField
    subfieldRamificationIndex F R
  else 0

open scoped Classical in
/-- The residue degree of a specified field subalgebra, with value zero in the nonfield case. -/
def subalgebraResidueDegree (R : Subalgebra F (Module.End F V)) : ℕ :=
  if h : IsField R then
    letI := h.toField
    subfieldResidueDegree F R
  else 0

/-- **BK93 (2.2.8), printed p. 56 (T6).** A refinement with derived stratum
equivalent to a simple stratum is equivalent to a simple stratum, with the stated
ramification, residue degree and critical exponent. -/
def RefinementStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
    (S : Stratum 𝒪[F] F V) (b : Module.End F V)
    (s : TameCorestriction 𝒪[F] F E V)
    (D C : Stratum (subfieldIntegers F E) E V),
    S.IsDerivedStratum E b s D →
    S.chain.valuation b = (-S.r : WithTop ℤ) →
    C.chain = D.chain → C.n = D.n → C.r = D.r →
    D.Equivalent C → C.IsSimple →
    let E₁ := Algebra.adjoin F ({S.b, C.b.restrictScalars F} : Set (Module.End F V))
    ∃ T : Stratum 𝒪[F] F V,
      T.chain = S.chain ∧ T.n = S.n ∧ T.r = S.r - 1 ∧ T.IsSimple ∧
      T.coset = {x | x - (S.b + b) ∈ S.chain.endFiltration (1 - S.r)} ∧
      elementRamificationIndex F T.b = subalgebraRamificationIndex F E₁ ∧
      elementResidueDegree F T.b = subalgebraResidueDegree F E₁ ∧
      criticalExponent T.chain T.b =
        max (criticalExponent S.chain S.b) (criticalExponent C.chain C.b)

end Langlands.BushnellKutzko
