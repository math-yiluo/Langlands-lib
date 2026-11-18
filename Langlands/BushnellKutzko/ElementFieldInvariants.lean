import Langlands.BushnellKutzko.MinimalElement
import Langlands.BushnellKutzko.PureSimpleStratum

/-! # Invariants of the actual generated field

Auxiliary constructions for BK93 (2.1.4), p. 50, and (2.4.1), p. 65.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

variable (F : Type uF) [Field F] [ValuativeRel F]
  (E : Type uE) [Field E] [Algebra F E]

/-- The residue degree `f(E|F)`, as the length of `𝔬_E/𝔭_E` over `𝔬_F`.
For finite local-field extensions this equals its dimension over `k_F`. -/
def subfieldResidueDegree : ℕ :=
  (Module.length 𝒪[F] (subfieldResidueRing F E)).toNat

variable {E} {V : Type uV} [AddCommGroup V] [Module F V]

open scoped Classical in
/-- The ramification index of the actual generated algebra `F[β]` when it is a
field. The value in the nonfield case is set to zero. -/
def elementRamificationIndex (β : Module.End F V) : ℕ :=
  if h : IsField (elementAlgebra β) then
    letI := h.toField
    subfieldRamificationIndex F (elementAlgebra β)
  else 0

open scoped Classical in
/-- The residue degree of the actual field `F[β]`, with value zero when the
generated algebra is not a field. -/
def elementResidueDegree (β : Module.End F V) : ℕ :=
  if h : IsField (elementAlgebra β) then
    letI := h.toField
    subfieldResidueDegree F (elementAlgebra β)
  else 0

/-- The dimension `[F[β]:F]` of the actual generated algebra. -/
def elementDegree (β : Module.End F V) : ℕ :=
  Module.finrank F (elementAlgebra β)

end Langlands.BushnellKutzko
