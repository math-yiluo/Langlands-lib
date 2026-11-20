import Langlands.BushnellKutzko.UnitFiltration
import Mathlib.LinearAlgebra.Quotient.Defs

/-! # From filtered units to an additive quotient

The map `g ↦ [g - 1]` gives the additive quotient used in the proof of
Bushnell–Kutzko (1993), (1.1.5)–(1.1.6), printed p. 22.
-/

namespace Langlands.BushnellKutzko.LatticeChain

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-- Reduction of `g - 1` modulo the `j`th filtration when products of two elements
of the `i`th filtration lie in the `j`th. -/
def unitFiltrationToQuotient {i j : ℕ} (hij : j ≤ i + i) :
    𝓛.unitFiltration i →* Multiplicative
      ((𝓛.endFiltration i) ⧸ (𝓛.endFiltration j).comap (𝓛.endFiltration i).subtype) := by
  let subOne (g : 𝓛.unitFiltration i) : 𝓛.endFiltration i :=
    ⟨(g.val : Module.End K V) - 1, g.property.2.2⟩
  refine
    { toFun := fun g => Multiplicative.ofAdd (Submodule.Quotient.mk (subOne g))
      map_one' := ?_
      map_mul' := ?_ }
  · have h : subOne 1 = 0 := Subtype.ext (sub_self (1 : Module.End K V))
    simp [h]
  · intro g h
    apply Multiplicative.ext
    let p := (𝓛.endFiltration j).comap (𝓛.endFiltration i).subtype
    change Submodule.Quotient.mk (p := p) (subOne (g * h)) =
      Submodule.Quotient.mk (subOne g + subOne h)
    apply (Submodule.Quotient.eq p).mpr
    change (subOne (g * h) : Module.End K V) -
      ((subOne g : Module.End K V) + (subOne h : Module.End K V)) ∈ 𝓛.endFiltration j
    have defect : (subOne (g * h) : Module.End K V) -
        ((subOne g : Module.End K V) + (subOne h : Module.End K V)) =
        (subOne g : Module.End K V) * (subOne h : Module.End K V) := by
      change (g.val : Module.End K V) * (h.val : Module.End K V) - 1 -
        (((g.val : Module.End K V) - 1) + ((h.val : Module.End K V) - 1)) = _
      dsimp only [subOne]
      noncomm_ring
    rw [defect]
    have hdepth : (j : ℤ) ≤ (i : ℤ) + i := by exact_mod_cast hij
    exact 𝓛.endFiltration_antitone hdepth
      (𝓛.mul_mem_endFiltration (subOne g).property (subOne h).property)

@[simp]
theorem unitFiltrationToQuotient_apply {i j : ℕ} (hij : j ≤ i + i) (g : 𝓛.unitFiltration i) :
    (𝓛.unitFiltrationToQuotient hij g).toAdd =
      Submodule.Quotient.mk ⟨(g.val : Module.End K V) - 1, g.property.2.2⟩ :=
  rfl

/-- At positive depth, `1 + x` is a filtered unit for every representative `x`. -/
theorem unitFiltrationToQuotient_surjective {i j : ℕ} (hij : j ≤ i + i) (hi : 1 ≤ i) :
    Function.Surjective (𝓛.unitFiltrationToQuotient hij) := by
  intro y
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ y.toAdd
  obtain ⟨g, hg, hgx⟩ := 𝓛.exists_mem_unitFiltration hi x.property
  refine ⟨⟨g, hg⟩, Multiplicative.ext ?_⟩
  rw [𝓛.unitFiltrationToQuotient_apply, ← hx]
  have hsub : (⟨(g : Module.End K V) - 1, hg.2.2⟩ : 𝓛.endFiltration i) = x :=
    Subtype.ext (by simp [hgx])
  rw [hsub]

/-- A filtered unit lies in the kernel exactly when it lies in the `j`th unit group. -/
theorem mem_ker_unitFiltrationToQuotient {i j : ℕ} (hij : j ≤ i + i)
    (g : 𝓛.unitFiltration i) :
    g ∈ (𝓛.unitFiltrationToQuotient hij).ker ↔ g.val ∈ 𝓛.unitFiltration j := by
  rw [MonoidHom.mem_ker, ← Multiplicative.toAdd.injective.eq_iff, toAdd_one,
    𝓛.unitFiltrationToQuotient_apply, Submodule.Quotient.mk_eq_zero]
  change (g.val : Module.End K V) - 1 ∈ 𝓛.endFiltration j ↔ _
  exact ⟨fun h => ⟨g.property.1, g.property.2.1, h⟩, fun h => h.2.2⟩

end Langlands.BushnellKutzko.LatticeChain
