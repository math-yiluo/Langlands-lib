import Langlands.GroupScheme.Unipotent.CoordinateBialgebra
import Langlands.GroupScheme.Chevalley.CoordinateRestriction
import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.Rational.SplitUnipotentTransport

/-! # Homomorphisms from split tori to unipotent group schemes are trivial -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding Chevalley

variable {k : Type u} [Field k]

section Diagonalizable

variable (Λ : Type u) [AddCommGroup Λ]

/-- The monomials form a basis of grouplike elements of the coordinate bialgebra of a
diagonalizable group. -/
theorem diagonalizable_comul_basis (γ : Λ) :
    letI := bialgebra (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ)
    comul (R := k) (AddMonoidAlgebra.basis Λ k γ) =
      AddMonoidAlgebra.basis Λ k γ ⊗ₜ[k] AddMonoidAlgebra.basis Λ k γ := by
  rw [AddMonoidAlgebra.basis_apply]
  exact Diagonalizable.comul_single (CommRingCat.of k) Λ γ 1

variable {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)

/-- A homomorphism from a diagonalizable group to a corepresented group whose coordinate
bialgebra satisfies `OneMemStable` sends every algebra point to the identity. -/
theorem pointsTrans_diagonalizable_eq_one (hB : letI := bialgebra e; OneMemStable k B)
    (φ : Corepresented.groupScheme (Diagonalizable.functor (CommRingCat.of k) Λ)
        (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ) ⟶
      Corepresented.groupScheme F e)
    (A : CommAlgCat.{u} (CommRingCat.of k))
    (x : (Diagonalizable.functor (CommRingCat.of k) Λ).obj A) :
    (Corepresented.pointsTrans (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ) e
      φ).app A x = 1 := by
  let d := Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ
  let α := Corepresented.pointsTrans d e φ
  let := bialgebra e
  let := bialgebra d
  have hr : coordinateRestriction e d α =
      (Algebra.ofId k (AddMonoidAlgebra k Λ)).comp (AffineLinearEmbedding.counit e) := by
    apply AlgHom.ext
    intro f
    exact bialgHom_eq_algebraMap_counit hB (coordinateRestrictionBialgHom e d α)
      (AddMonoidAlgebra.basis Λ k) (diagonalizable_comul_basis Λ) f
  have h := pt_comp_coordinateRestriction e d α (A := A) (d.homEquiv.symm x).hom
  rw [pt_homEquiv_symm, hr, ← AlgHom.comp_assoc, pt_comp_counit] at h
  exact h.symm

/-- A homomorphism from a diagonalizable group to a corepresented group whose coordinate
bialgebra satisfies `OneMemStable` is trivial. -/
theorem diagonalizable_hom_eq_zero (hB : letI := bialgebra e; OneMemStable k B)
    (φ : Corepresented.groupScheme (Diagonalizable.functor (CommRingCat.of k) Λ)
        (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ) ⟶
      Corepresented.groupScheme F e) :
    φ = 0 := by
  apply Corepresented.hom_ext_affinePoints
  intro S f
  have h1 := Corepresented.pointsTrans_app
    (Diagonalizable.grpCorepresentation (CommRingCat.of k) Λ) e φ
    (Corepresented.affinePointsEquiv _ _ S f)
  rw [MulEquiv.symm_apply_apply] at h1
  rw [← h1, pointsTrans_diagonalizable_eq_one Λ e hB φ]
  change 1 = Corepresented.affinePointsEquiv F e S (f ≫ (1 : _ ⟶ _))
  rw [MonObj.comp_one, map_one]

end Diagonalizable

end Langlands.GroupScheme.Unipotent

namespace Langlands.GroupScheme

/-- The trivial homomorphism has trivial image on every test scheme. -/
theorem SubgroupFunctor.range_zero {S : Scheme.{u}} {G H : GroupScheme S} :
    SubgroupFunctor.range (0 : H ⟶ G) = ⊥ := by
  ext T x
  constructor
  · rintro ⟨y, rfl⟩
    exact (Subgroup.mem_bot).2 (by
      change y ≫ (1 : H.X ⟶ G.X) = 1
      exact MonObj.comp_one y)
  · intro hx
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    subst hx
    exact Subgroup.one_mem ((SubgroupFunctor.range (0 : H ⟶ G)).carrier T)

variable {k : Type u} [Field k] {S U : GroupScheme (Spec (CommRingCat.of k))}

/-- Every homomorphism from a split torus to an affine unipotent group scheme over a field is
trivial. -/
theorem IsSplitTorus.hom_eq_zero_of_isUnipotent [IsAffine U.X.left] (hS : IsSplitTorus S)
    (hU : IsUnipotent U) (j : S ⟶ U) : j = 0 := by
  classical
  obtain ⟨I, hI, ⟨eS⟩⟩ := hS
  have := Fintype.ofFinite I
  let eD : (Diagonalizable.groupScheme (CommRingCat.of k) (I → ℤ)).toGrp ≅ S :=
    Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ)) ≪≫ eS.symm
  let eU := AffineCoordinates.groupSchemeIso U
  have hU' : IsUnipotent (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)) := IsUnipotent.of_iso eU hU
  have h0 := Unipotent.diagonalizable_hom_eq_zero (I → ℤ) (AffineCoordinates.corepresentation U)
    (Unipotent.oneMemStable_of_isUnipotent _ hU') (eD.hom ≫ j ≫ eU.inv)
  calc j = eD.inv ≫ (eD.hom ≫ j ≫ eU.inv) ≫ eU.hom := by simp
    _ = 0 := by erw [h0, Limits.zero_comp, Limits.comp_zero]

/-- The image of a homomorphism from a split torus to an affine unipotent group scheme over a
field is trivial on every test scheme. -/
theorem IsSplitTorus.range_eq_bot_of_isUnipotent [IsAffine U.X.left] (hS : IsSplitTorus S)
    (hU : IsUnipotent U) (j : S ⟶ U) : SubgroupFunctor.range j = ⊥ := by
  rw [hS.hom_eq_zero_of_isUnipotent hU j, SubgroupFunctor.range_zero]

end Langlands.GroupScheme
