import Langlands.GroupScheme.Rational.TorusActionCoordinates
import Langlands.GroupScheme.Lie.BaseChange

/-! # Points of a torus that splits over an extension field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {T : GroupScheme (Spec (CommRingCat.of k))} {I : Type u} [Finite I]
    (s : (GroupScheme.baseChange (algebraBaseMap k K)).obj T ≅
      splitTorus (Spec (CommRingCat.of K)) I)

/-- The point of `T` over an algebra `C` over the splitting field `K` with unit
coordinates `τ` in the splitting `s`. -/
def splitPoint {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]
    (τ : I → Cˣ) : Lie.AffinePoints T C :=
  Lie.affineBaseChangeEquiv k K T C
    (AutomorphicAction.torusPoint s (A := CommAlgCat.of K C) τ)

variable {C : Type u} [CommRing C] [Algebra k C] [Algebra K C] [IsScalarTower k K C]

@[simp] theorem splitPoint_one : splitPoint s (1 : I → Cˣ) = 1 := by
  simp only [splitPoint, AutomorphicAction.torusPoint_one]
  exact map_one _

theorem splitPoint_mul (τ τ' : I → Cˣ) :
    splitPoint s (τ * τ') = splitPoint s τ * splitPoint s τ' := by
  simp only [splitPoint]
  rw [AutomorphicAction.torusPoint_mul]
  exact map_mul _ _ _

/-- Every point of `T` over an algebra over the splitting field has unit coordinates. -/
theorem splitPoint_surjective (t : Lie.AffinePoints T C) :
    ∃ τ : I → Cˣ, splitPoint s τ = t := by
  let x := (Lie.affineBaseChangeEquiv k K T C).symm t
  refine ⟨splitTorus.algebraPointsEquiv I C (x ≫ s.hom.hom.hom), ?_⟩
  simp only [splitPoint, AutomorphicAction.torusPoint]
  rw [MulEquiv.symm_apply_apply, Category.assoc, ← Grp.comp_hom_hom, s.hom_inv_id,
    Grp.id_hom_hom, Category.comp_id]
  exact MulEquiv.apply_symm_apply _ t

variable {D : Type u} [CommRing D] [Algebra k D] [Algebra K D] [IsScalarTower k K D]

/-- Unit coordinates of split points commute with every map of algebras over the
splitting field. -/
theorem splitPoint_naturality (f : C →ₐ[K] D) (τ : I → Cˣ) :
    Lie.affineMap T (f.restrictScalars k) (splitPoint s τ) =
      splitPoint s (fun i => Units.map f.toMonoidHom (τ i)) := by
  simp only [splitPoint]
  rw [← Lie.affineBaseChangeEquiv_naturality]
  congr 1
  exact AutomorphicAction.torusPoint_naturality s
    (A := CommAlgCat.of K C) (A' := CommAlgCat.of K D) (CommAlgCat.ofHom f) τ

end Langlands.GroupScheme.RelativeRoot
