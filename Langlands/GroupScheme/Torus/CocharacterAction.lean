import Langlands.GroupScheme.Torus.Maximal

/-! # Integral character and cocharacter automorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RealTorusSpace

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Postcomposition by an actual automorphism on the cocharacter lattice. -/
def cocharacterAut (σ : T ≅ T) : cocharacterLattice T ≃ₗ[ℤ] cocharacterLattice T :=
  AddEquiv.toIntLinearEquiv
    { toFun := fun ν => ν ≫ σ.hom
      invFun := fun ν => ν ≫ σ.inv
      left_inv := fun ν => by simp
      right_inv := fun ν => by simp
      map_add' := fun ν μ => Preadditive.add_comp _ _ _ _ _ _ }

@[simp] theorem cocharacterAut_apply (σ : T ≅ T) (ν : cocharacterLattice T) :
    cocharacterAut σ ν = ν ≫ σ.hom := rfl

/-- The integral pairing is unchanged by the two compatible automorphisms. -/
theorem latticePairing_aut (σ : T ≅ T) (χ : characterLattice T) (ν : cocharacterLattice T) :
    latticePairing T (characterAut σ χ) (cocharacterAut σ ν) = latticePairing T χ ν := by
  simp [latticePairing_apply, Category.assoc]

end Langlands.GroupScheme.RealTorusSpace
