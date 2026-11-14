import Langlands.GroupScheme.RelativeLevi.BorelFiberTransport

/-! # The Borel locus and its compatibility with base change -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeLevi

variable {S S' : Scheme.{u}} {G P : GroupScheme S}

/-- Points where the actual residue-field inclusion is geometric Borel. -/
def borelLocus (i : P ⟶ G) : Set S :=
  {s | IsGeometricBorelSubgroup (residueFiberHom i s)}

@[simp] theorem mem_borelLocus (i : P ⟶ G) (s : S) :
    s ∈ borelLocus i ↔ IsGeometricBorelSubgroup (residueFiberHom i s) :=
  Iff.rfl

/-- The Borel locus of a relative parabolic in a reductive group pulls back
under every morphism of base schemes. -/
theorem borelLocus_baseChange (i : P ⟶ G)
    (hG : IsReductive G) (hi : IsRelativeParabolicSubgroup i) (b : S' ⟶ S) :
    borelLocus ((baseChange b).map i) = b ⁻¹' borelLocus i := by
  ext s'
  exact isGeometricBorelSubgroup_residueFiber_baseChange_iff hG hi b s'

end Langlands.GroupScheme.RelativeLevi
