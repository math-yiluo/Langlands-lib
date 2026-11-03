import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Selected conjugacy witnesses through a common target -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {B B' C G : GroupScheme S}
variable {i : B ⟶ G} {i' : B' ⟶ G} {j : C ⟶ G}

/-- Two conjugacies to the same target compose with point `h⁻¹ * g`. -/
theorem comp_innerIso_hom_of_common_target
    {g h : Over.mk (𝟙 S) ⟶ G.X} {φ : B ≅ C} {ψ : B' ≅ C}
    (hg : i ≫ (G.innerIso g).hom = φ.hom ≫ j)
    (hh : i' ≫ (G.innerIso h).hom = ψ.hom ≫ j) :
    i ≫ (G.innerIso (h⁻¹ * g)).hom = (φ ≪≫ ψ.symm).hom ≫ i' := by
  have hj : j ≫ (G.innerIso h).inv = ψ.inv ≫ i' := by
    calc
      j ≫ (G.innerIso h).inv =
          (ψ.inv ≫ (ψ.hom ≫ j)) ≫ (G.innerIso h).inv := by
        rw [Iso.inv_hom_id_assoc]
      _ = (ψ.inv ≫ (i' ≫ (G.innerIso h).hom)) ≫ (G.innerIso h).inv := by
        rw [hh]
      _ = ψ.inv ≫ i' := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [innerIso_mul_hom, innerIso_inv_hom, reassoc_of% hg, hj,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]

/-- Compose two selected conjugacies to a common target, retaining the point,
source isomorphism and exact embedding equation. -/
def conjugatingDataOfCommonTarget
    (d : Σ (g : Over.mk (𝟙 S) ⟶ G.X),
      {φ : B ≅ C // i ≫ (G.innerIso g).hom = φ.hom ≫ j})
    (d' : Σ (h : Over.mk (𝟙 S) ⟶ G.X),
      {ψ : B' ≅ C // i' ≫ (G.innerIso h).hom = ψ.hom ≫ j}) :
    Σ (g : Over.mk (𝟙 S) ⟶ G.X),
      {φ : B ≅ B' // i ≫ (G.innerIso g).hom = φ.hom ≫ i'} :=
  ⟨d'.1⁻¹ * d.1, d.2.1 ≪≫ d'.2.1.symm,
    comp_innerIso_hom_of_common_target d.2.2 d'.2.2⟩

variable
    (d : Σ (g : Over.mk (𝟙 S) ⟶ G.X),
      {φ : B ≅ C // i ≫ (G.innerIso g).hom = φ.hom ≫ j})
    (d' : Σ (h : Over.mk (𝟙 S) ⟶ G.X),
      {ψ : B' ≅ C // i' ≫ (G.innerIso h).hom = ψ.hom ≫ j})

@[simp]
theorem conjugatingDataOfCommonTarget_point :
    (conjugatingDataOfCommonTarget d d').1 = d'.1⁻¹ * d.1 := rfl

@[simp]
theorem conjugatingDataOfCommonTarget_iso :
    (conjugatingDataOfCommonTarget d d').2.1 = d.2.1 ≪≫ d'.2.1.symm := rfl

theorem conjugatingDataOfCommonTarget_spec :
    i ≫ (G.innerIso (conjugatingDataOfCommonTarget d d').1).hom =
      (conjugatingDataOfCommonTarget d d').2.1.hom ≫ i' :=
  (conjugatingDataOfCommonTarget d d').2.2

end Langlands.GroupScheme
