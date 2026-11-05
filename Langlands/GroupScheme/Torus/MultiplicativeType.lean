import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Langlands.GroupScheme.Torus.Lattice

/-! # Finite-type groups of multiplicative type over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A finite-type group of multiplicative type becomes an actual diagonalizable
group with finitely generated character group over some field extension. -/
def IsMultiplicativeType (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
    (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
    Nonempty (((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) ≅
        (Diagonalizable.groupScheme (CommRingCat.of K) Λ).toGrp)

/-- Every torus is of multiplicative type, using its given splitting extension. -/
theorem IsTorus.isMultiplicativeType {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T) : IsMultiplicativeType T := by
  classical
  obtain ⟨K, hK, aK, I, hI, ⟨e⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  exact ⟨K, hK, aK, I → ℤ, inferInstance, inferInstance,
    ⟨e ≪≫ (Diagonalizable.splitIso (CommRingCat.of K)
      (AddEquiv.refl (I → ℤ))).symm⟩⟩

end Langlands.GroupScheme
