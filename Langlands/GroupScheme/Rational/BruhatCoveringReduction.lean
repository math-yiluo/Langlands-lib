import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Common maximal split tori and rational Bruhat covering -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Scheme

variable {S : Scheme.{u}} {G H : GroupScheme S}
  {T T' : CommGroupScheme S}

/-- Inner automorphisms commute with group-scheme homomorphisms. -/
theorem innerIso_hom_comp (j : H ⟶ G) (p : Over.mk (𝟙 S) ⟶ H.X) :
    (H.innerIso p).hom ≫ j = j ≫ (G.innerIso (p ≫ j.hom.hom)).hom := by
  apply hom_ext_points
  intro U x
  change (x ≫ (H.innerIso p).hom.hom.hom) ≫ j.hom.hom =
    (x ≫ j.hom.hom) ≫ (G.innerIso (p ≫ j.hom.hom)).hom.hom.hom
  rw [comp_innerIso_hom, comp_innerIso_hom, MonObj.mul_comp, MonObj.mul_comp,
    GrpObj.inv_comp, constantPoint_comp]

/-- Two conjugacies from the same torus to a common torus construct a point of
its actual scheme normalizer, including the source automorphism. -/
def normalizerPointOfConjugacySquare
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G)
    (g p q : Over.mk (𝟙 S) ⟶ G.X) (e e' : T.toGrp ≅ T'.toGrp)
    (hp : i ≫ (G.innerIso p).hom = e.hom ≫ i')
    (hq : i ≫ (G.innerIso q).hom ≫ (G.innerIso g).hom = e'.hom ≫ i') :
    normalizerPoints i := by
  let a : T.toGrp ≅ T.toGrp := e' ≪≫ e.symm
  let σ : T ≅ T :=
    { hom := Additive.ofMul a.hom
      inv := Additive.ofMul a.inv
      hom_inv_id := congrArg Additive.ofMul a.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul a.inv_hom_id }
  refine ⟨p⁻¹ * g * q, σ, ?_⟩
  change i ≫ (G.innerIso (p⁻¹ * g * q)).hom = e'.hom ≫ e.inv ≫ i
  have hpi : i' ≫ (G.innerIso p).inv = e.inv ≫ i := by
    calc
      _ = (e.inv ≫ (i ≫ (G.innerIso p).hom)) ≫ (G.innerIso p).inv := by
        rw [hp, Iso.inv_hom_id_assoc]
      _ = e.inv ≫ i := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = (i ≫ (G.innerIso q).hom ≫ (G.innerIso g).hom) ≫
        (G.innerIso p).inv := by
          simp only [innerIso_mul_hom, innerIso_inv_hom, Category.assoc]
    _ = (e'.hom ≫ i') ≫ (G.innerIso p).inv := by rw [hq]
    _ = e'.hom ≫ e.inv ≫ i := by rw [Category.assoc, hpi]

@[simp] theorem normalizerPointOfConjugacySquare_val
    (i : T.toGrp ⟶ G) (i' : T'.toGrp ⟶ G)
    (g p q : Over.mk (𝟙 S) ⟶ G.X) (e e' : T.toGrp ≅ T'.toGrp)
    (hp : i ≫ (G.innerIso p).hom = e.hom ≫ i')
    (hq : i ≫ (G.innerIso q).hom ≫ (G.innerIso g).hom = e'.hom ≫ i') :
    (normalizerPointOfConjugacySquare i i' g p q e e' hp hq).val = p⁻¹ * g * q := rfl

end Scheme

end Langlands.GroupScheme
