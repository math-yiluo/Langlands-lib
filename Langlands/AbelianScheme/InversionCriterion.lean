import Langlands.AbelianScheme.SourceDefinition

/-! # Bundling geometric abelian schemes from multiplicative inversion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands

namespace GroupScheme

/-- A group scheme is commutative if its inversion is a monoid-object homomorphism. -/
theorem isCommMonObj_of_inverse_isMonHom {S : Scheme.{u}} (G : GroupScheme S)
    [IsMonHom ι[G.X]] : IsCommMonObj G.X := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun a b => ?_⟩⟩
  have h := MonObj.mul_comp a⁻¹ b⁻¹ ι[G.X]
  simpa only [← Hom.inv_def, mul_inv_rev, inv_inv] using h.symm

end GroupScheme

namespace AbelianScheme

/-- Bundle a geometric abelian scheme once multiplicativity of inversion is proved. -/
def ofIsAbelianOfInverseIsMonHom {S : Scheme.{u}} (G : GroupScheme S)
    (h : GroupScheme.IsAbelian G) [IsMonHom ι[G.X]] : AbelianScheme S where
  toGrp := G
  comm := GroupScheme.isCommMonObj_of_inverse_isMonHom G
  smooth := h.1
  proper := h.2.1
  geometricallyConnected := h.2.2

@[simp]
theorem ofIsAbelianOfInverseIsMonHom_toGrp {S : Scheme.{u}} (G : GroupScheme S)
    (h : GroupScheme.IsAbelian G) [IsMonHom ι[G.X]] :
    (ofIsAbelianOfInverseIsMonHom G h).toGrp = G := rfl

/-- The source equivalence reduces to proving multiplicativity of inversion. -/
theorem sourceDefinitionEquivalence_of_inverse_isMonHom
    (h : ∀ (S : Scheme.{u}) (G : GroupScheme S),
      GroupScheme.IsAbelian G → IsMonHom ι[G.X]) :
    SourceDefinitionEquivalence.{u} := by
  intro S G
  constructor
  · intro hG
    let := h S G hG
    exact ⟨ofIsAbelianOfInverseIsMonHom G hG, rfl⟩
  · rintro ⟨A, rfl⟩
    exact A.isAbelian

end AbelianScheme
end Langlands
