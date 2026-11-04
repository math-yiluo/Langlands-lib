import Langlands.AbelianScheme.Multiplication
import Langlands.GroupScheme.Torus.DiagonalizableFaithfullyFlat

/-! # Multiplication by a nonzero integer on a split torus is flat and surjective -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace Diagonalizable

variable (R : CommRingCat.{u}) {Λ : Type u} [AddCommGroup Λ]

/-- On `D(Λ)`, multiplication by `n` is the restriction along `n • id : Λ → Λ`. -/
theorem restrictMap_smul_id (n : ℤ) :
    restrictMap R (n • AddMonoidHom.id Λ) = multiplication (groupScheme R Λ).toGrp n := by
  apply Grp.hom_ext
  let P := Corepresented.pointsEquiv (functor R Λ) (grpCorepresentation R Λ) (groupScheme R Λ).X
  have h1 : 𝟙 (groupScheme R Λ).X ≫ (multiplication (groupScheme R Λ).toGrp n).hom.hom =
      (𝟙 (groupScheme R Λ).X) ^ n := points_multiplication _ _ _ _
  have h2 : P (𝟙 _ ≫ (restrictMap R (n • AddMonoidHom.id Λ)).hom.hom) = P (𝟙 _) ^ n := by
    apply MonoidHom.ext
    intro l
    refine (pointsEquiv_restrictMap R (n • AddMonoidHom.id Λ) (𝟙 _) l.toAdd).trans ?_
    rw [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, ofAdd_zsmul]
    exact map_zpow (F := Multiplicative Λ →* ((algΓ R).obj (groupScheme R Λ).X).unopˣ)
      (P (𝟙 _)) _ n
  have h3 : P (𝟙 _ ^ n) = P (𝟙 _) ^ n := map_zpow P _ n
  have h := P.injective (h2.trans h3.symm)
  exact (Category.id_comp _).symm.trans (h.trans (h1.symm.trans (Category.id_comp _)))

/-- For `n ≠ 0` on the torsion-free lattice `I → ℤ`, multiplication by `n` is injective. -/
theorem smul_id_injective {I : Type u} {n : ℤ} (hn : n ≠ 0) :
    Function.Injective (n • AddMonoidHom.id (I → ℤ)) := by
  intro x y hxy
  funext a
  have := congrFun hxy a
  simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hn this

end Diagonalizable

/-- Multiplication by a nonzero integer on a split torus over a nonzero ring is flat and
surjective on underlying schemes. -/
theorem IsSplitTorus.flat_and_surjective_multiplication {R : CommRingCat.{u}} [Nontrivial R]
    {S : CommGroupScheme (Spec R)} (hS : IsSplitTorus S.toGrp) {n : ℤ} (hn : n ≠ 0) :
    Flat (multiplication S.toGrp n).hom.hom.left ∧
      Surjective (multiplication S.toGrp n).hom.hom.left := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  have := Fintype.ofFinite I
  classical
  let D := Diagonalizable.groupScheme R (I → ℤ)
  let E : S.toGrp ≅ D.toGrp := e ≪≫ (Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ))).symm
  have hm : multiplication S.toGrp n = E.hom ≫ multiplication D.toGrp n ≫ E.inv := by
    rw [← Category.assoc, ← multiplication_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hleft : (multiplication S.toGrp n).hom.hom.left = E.hom.hom.hom.left ≫
      (Diagonalizable.restrictMap R (n • AddMonoidHom.id (I → ℤ))).hom.hom.left ≫
        E.inv.hom.hom.left := by
    rw [hm, Diagonalizable.restrictMap_smul_id]
    rfl
  have : IsIso E.hom.hom.hom.left := Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E.hom
  have : IsIso E.inv.hom.hom.left := Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) E.inv
  obtain ⟨hflat, hsurj⟩ := Diagonalizable.flat_and_surjective_restrictMap R
    (n • AddMonoidHom.id (I → ℤ)) (Diagonalizable.smul_id_injective hn)
  rw [hleft]
  exact ⟨inferInstance, inferInstance⟩

end Langlands.GroupScheme
