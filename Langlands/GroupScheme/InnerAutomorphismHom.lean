import Langlands.GroupScheme.InnerAutomorphism

/-! # Inner automorphisms form a group homomorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} (G : GroupScheme S)

theorem constantPoint_mul (g h : Over.mk (𝟙 S) ⟶ G.X) (T : Over S) :
    G.constantPoint (g * h) T = G.constantPoint g T * G.constantPoint h T :=
  MonObj.comp_mul _ _ _

theorem constantPoint_inv (g : Over.mk (𝟙 S) ⟶ G.X) (T : Over S) :
    G.constantPoint g⁻¹ T = (G.constantPoint g T)⁻¹ :=
  GrpObj.comp_inv _ _

theorem constantPoint_one (T : Over S) : G.constantPoint 1 T = 1 :=
  MonObj.comp_one _

theorem innerIso_mul_hom (g h : Over.mk (𝟙 S) ⟶ G.X) :
    (G.innerIso (g * h)).hom = (G.innerIso h).hom ≫ (G.innerIso g).hom := by
  refine hom_ext_points fun T x => ?_
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, comp_innerIso_hom,
    comp_innerIso_hom, constantPoint_mul, mul_inv_rev]
  simp only [mul_assoc]

theorem innerIso_one_hom : (G.innerIso 1).hom = 𝟙 G := by
  refine hom_ext_points fun T x => ?_
  rw [Grp.id_hom_hom, comp_innerIso_hom, constantPoint_one, one_mul, inv_one, mul_one,
    Category.comp_id]

theorem innerIso_inv_hom (g : Over.mk (𝟙 S) ⟶ G.X) :
    (G.innerIso g⁻¹).hom = (G.innerIso g).inv := by
  rw [← cancel_epi (G.innerIso g).hom, Iso.hom_inv_id, ← innerIso_mul_hom, inv_mul_cancel,
    innerIso_one_hom]

/-- Inner automorphisms as a group homomorphism from base points to automorphisms. -/
@[simps]
def innerAut : (Over.mk (𝟙 S) ⟶ G.X) →* Aut G where
  toFun g := G.innerIso g
  map_one' := Aut.ext G.innerIso_one_hom
  map_mul' g h := Aut.ext (G.innerIso_mul_hom g h)

variable {G} {H : GroupScheme S}

/-- If `Int(n)` restricts along `i` to `σ`, then `Int(n⁻¹)` restricts to `σ⁻¹`. -/
theorem comp_innerIso_inv_hom {i : H ⟶ G} {n : Over.mk (𝟙 S) ⟶ G.X} {σ : H ≅ H}
    (h : i ≫ (G.innerIso n).hom = σ.hom ≫ i) :
    i ≫ (G.innerIso n⁻¹).hom = σ.inv ≫ i := by
  rw [innerIso_inv_hom, Iso.eq_inv_comp, ← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

/-- If `Int(n)` and `Int(m)` restrict along `i` to `σ` and `τ`, then `Int(n * m)`
restricts to `τ ≪≫ σ`. -/
theorem comp_innerIso_mul_hom {i : H ⟶ G} {n m : Over.mk (𝟙 S) ⟶ G.X} {σ τ : H ≅ H}
    (hn : i ≫ (G.innerIso n).hom = σ.hom ≫ i) (hm : i ≫ (G.innerIso m).hom = τ.hom ≫ i) :
    i ≫ (G.innerIso (n * m)).hom = (τ ≪≫ σ).hom ≫ i := by
  rw [innerIso_mul_hom, reassoc_of% hm, hn, Iso.trans_hom, Category.assoc]

/-- Conjugating a point centralizing `i` by a point normalizing `i` gives a point
centralizing `i`. -/
theorem comp_innerIso_conj_hom {i : H ⟶ G} {n z : Over.mk (𝟙 S) ⟶ G.X} {σ : H ≅ H}
    (hn : i ≫ (G.innerIso n).hom = σ.hom ≫ i) (hz : i ≫ (G.innerIso z).hom = i) :
    i ≫ (G.innerIso (n * z * n⁻¹)).hom = i := by
  rw [innerIso_mul_hom, innerIso_mul_hom, reassoc_of% (comp_innerIso_inv_hom hn),
    reassoc_of% hz, hn, Iso.inv_hom_id_assoc]

end Langlands.GroupScheme
