import Langlands.Global.Arithmetic.AuxiliaryFirstOrderHelpers

/-! Compare the actual intermediate-field subtype topology with supplied p-adic data. -/

noncomputable section

namespace Langlands.Global.AuxiliaryFirstOrder

universe u v

/-- Transport continuity along an equality of field topologies without changing values. -/
def transportUnitCharacter {A : Type u} [Monoid A]
    (τ τ' : TopologicalSpace A) (h : τ = τ')
    (χ : letI := τ; Aˣ →ₜ* ℂˣ) : letI := τ'; Aˣ →ₜ* ℂˣ := by
  subst τ'
  exact χ

@[simp]
theorem transportUnitCharacter_apply {A : Type u} [Monoid A]
    (τ τ' : TopologicalSpace A) (h : τ = τ')
    (χ : letI := τ; Aˣ →ₜ* ℂˣ) (a : Aˣ) :
    transportUnitCharacter τ τ' h χ a = χ a := by
  subst τ'
  rfl

/-- Every supplied realization of L has the actual subspace topology inherited from M. -/
theorem intermediate_topology_eq {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [FiniteDimensional F.Carrier M.Carrier]
    (L : IntermediateField F.Carrier M.Carrier)
    (T : (intermediatePadicField F M L).TopologicalData) :
    letI := M.canonicalNormedField
    T.topology = (inferInstance : TopologicalSpace L) := by
  let := M.canonicalNormedField
  let := M.canonicalNormedAlgebra
  let : NormedAlgebra (Padic p) L :=
    NormedAlgebra.induced (Padic p) L M.Carrier (L.val.restrictScalars (Padic p))
  let : FiniteDimensional (Padic p) L := Module.Finite.trans F.Carrier L
  let : IsModuleTopology (Padic p) L := isModuleTopologyOfFiniteDimensional
  exact T.topology_eq_canonicalModule.trans (eq_moduleTopology (Padic p) L).symm

/-- The intermediate presentation has exactly the ambient restricted spectral norm. -/
theorem intermediate_canonicalNorm_eq {p : ℕ} [Fact p.Prime]
    (F : PadicField.{u} p) (M : PadicField.{v} p)
    [Algebra F.Carrier M.Carrier] [IsScalarTower (Padic p) F.Carrier M.Carrier]
    [FiniteDimensional F.Carrier M.Carrier]
    (L : IntermediateField F.Carrier M.Carrier) (x : L) :
    (intermediatePadicField F M L).canonicalNorm x = M.canonicalNorm (x : M.Carrier) := by
  exact (Weil.Local.canonicalNorm_map (intermediatePadicField F M L) M
    (L.val.restrictScalars (Padic p)) x).symm

end Langlands.Global.AuxiliaryFirstOrder
