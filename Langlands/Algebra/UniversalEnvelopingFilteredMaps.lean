import Langlands.Algebra.UniversalEnvelopingFiltration

/-! # Maps preserving the actual enveloping degree filtration -/

noncomputable section
universe u v w
set_option autoImplicit false

namespace Langlands.Algebra.UniversalEnveloping

variable (R : Type u) (L : Type v) (L' : Type w)
  [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "U'" => UniversalEnvelopingAlgebra R L'

/-- An algebra homomorphism taking actual generators into degree one preserves
the degree-one submodule, including constants. -/
theorem algHom_mem_degreeOne (f : U →ₐ[R] U')
    (hgen : ∀ x : L, f (UniversalEnvelopingAlgebra.ι R x) ∈ degreeOne R L')
    {a : U} (ha : a ∈ degreeOne R L) :
    f a ∈ degreeOne R L' := by
  obtain ⟨c, hc, x, hx, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
  obtain ⟨x, rfl⟩ := hx
  rw [map_add, f.commutes]
  exact (degreeOne R L').add_mem
    ((one_le_degreeOne R L') (Submodule.algebraMap_mem r)) (hgen x)

/-- Preservation of generators in degree one implies preservation of every
piece of the genuine quotient filtration. -/
theorem algHom_mem_degreeFiltration (f : U →ₐ[R] U')
    (hgen : ∀ x : L, f (UniversalEnvelopingAlgebra.ι R x) ∈ degreeOne R L')
    {d : ℕ} {a : U} (ha : a ∈ degreeFiltration R L d) :
    f a ∈ degreeFiltration R L' d := by
  induction ha using Submodule.pow_induction_on_right' with
  | algebraMap r =>
    simpa only [AlgHom.commutes, degreeFiltration_zero] using
      (Submodule.algebraMap_mem r : algebraMap R U' r ∈ (1 : Submodule R U'))
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact (degreeFiltration R L' i).add_mem ihx ihy
  | mul_mem i x hx ih m hm =>
    rw [map_mul]
    exact mul_mem_degreeFiltration R L' ih
      (show f m ∈ degreeFiltration R L' 1 from by
        simpa only [degreeFiltration_one] using algHom_mem_degreeOne R L L' f hgen hm)

/-- If an algebra equivalence and its inverse preserve generators in degree one,
then membership in every degree piece is equivalent on both sides. -/
theorem algEquiv_mem_degreeFiltration_iff (e : U ≃ₐ[R] U')
    (hgen : ∀ x : L, e (UniversalEnvelopingAlgebra.ι R x) ∈ degreeOne R L')
    (hgen' : ∀ x : L', e.symm (UniversalEnvelopingAlgebra.ι R x) ∈ degreeOne R L)
    (d : ℕ) (a : U) :
    e a ∈ degreeFiltration R L' d ↔ a ∈ degreeFiltration R L d := by
  constructor
  · intro ha
    have hb := algHom_mem_degreeFiltration R L' L e.symm.toAlgHom hgen' ha
    change e.symm (e a) ∈ degreeFiltration R L d at hb
    simpa only [AlgEquiv.symm_apply_apply] using hb
  · exact algHom_mem_degreeFiltration R L L' e.toAlgHom hgen

end Langlands.Algebra.UniversalEnveloping
