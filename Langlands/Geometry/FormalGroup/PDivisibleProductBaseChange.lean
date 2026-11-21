import Langlands.Geometry.FormalGroup.PDivisibleBaseChange
import Langlands.Geometry.FormalGroup.PDivisibleRationalProduct

/-! # Pullback of actual products of p-divisible groups -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.PDivisibleGroup

variable {p : ℕ} [Fact p.Prime]

/-- The actual integral projections distinguish all maps into the product tower. -/
theorem Hom.prod_hom_ext {R : CommRingCat.{u}} {G H J : PDivisibleGroup R p} {f g : J ⟶ G.prod H}
    (hf : f ≫ prodFst G H = g ≫ prodFst G H) (hg : f ≫ prodSnd G H = g ≫ prodSnd G H) : f = g := by
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id f).symm
    _ = g ≫ 𝟙 _ := by
      rw [← prod_decomposition G H, Preadditive.comp_add, Preadditive.comp_add]
      simp only [← Category.assoc, hf, hg]
    _ = g := Category.comp_id g

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (G H : PDivisibleGroup (CommRingCat.of R) p)

local notation "F" => (baseChangeFunctor R S p)

private def productPullbackHom : (F).obj (G.prod H) ⟶ ((F).obj G).prod ((F).obj H) :=
  (F).map (prodFst G H) ≫ prodInl ((F).obj G) ((F).obj H) +
    (F).map (prodSnd G H) ≫ prodInr ((F).obj G) ((F).obj H)

private def productPullbackInv : ((F).obj G).prod ((F).obj H) ⟶ (F).obj (G.prod H) :=
  prodFst ((F).obj G) ((F).obj H) ≫ (F).map (prodInl G H) +
    prodSnd ((F).obj G) ((F).obj H) ≫ (F).map (prodInr G H)

private theorem productPullbackHom_fst :
    productPullbackHom (S := S) G H ≫ prodFst ((F).obj G) ((F).obj H) = (F).map (prodFst G H) := by
  simp only [productPullbackHom, Preadditive.add_comp, Category.assoc, prodInl_fst,
    prodInr_fst, Category.comp_id, comp_zero, add_zero]

private theorem productPullbackHom_snd :
    productPullbackHom (S := S) G H ≫ prodSnd ((F).obj G) ((F).obj H) = (F).map (prodSnd G H) := by
  simp only [productPullbackHom, Preadditive.add_comp, Category.assoc, prodInl_snd,
    prodInr_snd, Category.comp_id, comp_zero, zero_add]

private theorem productPullbackInv_fst :
    productPullbackInv (S := S) G H ≫ (F).map (prodFst G H) = prodFst ((F).obj G) ((F).obj H) := by
  have hz : (F).map (0 : H ⟶ G) = 0 := ((F).mapAddHom (X := H) (Y := G)).map_zero
  have hi : (F).map (𝟙 G) = 𝟙 ((F).obj G) := (F).map_id G
  simp only [productPullbackInv, Preadditive.add_comp, Category.assoc, ← Functor.map_comp,
    prodInl_fst, prodInr_fst, hi, hz, Category.comp_id, comp_zero, add_zero]

private theorem productPullbackInv_snd :
    productPullbackInv (S := S) G H ≫ (F).map (prodSnd G H) = prodSnd ((F).obj G) ((F).obj H) := by
  have hz : (F).map (0 : G ⟶ H) = 0 := ((F).mapAddHom (X := G) (Y := H)).map_zero
  have hi : (F).map (𝟙 H) = 𝟙 ((F).obj H) := (F).map_id H
  simp only [productPullbackInv, Preadditive.add_comp, Category.assoc, ← Functor.map_comp,
    prodInl_snd, prodInr_snd, hi, hz, Category.comp_id, comp_zero, zero_add]

/-- The actual pullback of a product is canonically the product of the pullbacks. -/
def baseChangeProdIso : ((F).obj (G.prod H)) ≅ ((F).obj G).prod ((F).obj H) where
  hom := productPullbackHom G H
  inv := productPullbackInv G H
  hom_inv_id := by
    change productPullbackHom (S := S) G H ≫
      (prodFst ((F).obj G) ((F).obj H) ≫ (F).map (prodInl G H) +
        prodSnd ((F).obj G) ((F).obj H) ≫ (F).map (prodInr G H)) = _
    simp only [Preadditive.comp_add, ← Category.assoc, productPullbackHom_fst, productPullbackHom_snd,
      ← Functor.map_comp, ← Functor.map_add, prod_decomposition]
    exact (F).map_id (G.prod H)
  inv_hom_id := by
    change productPullbackInv (S := S) G H ≫
      ((F).map (prodFst G H) ≫ prodInl ((F).obj G) ((F).obj H) +
        (F).map (prodSnd G H) ≫ prodInr ((F).obj G) ((F).obj H)) = _
    simp only [Preadditive.comp_add, ← Category.assoc, productPullbackInv_fst, productPullbackInv_snd,
      prod_decomposition]

@[simp] theorem baseChangeProdIso_hom_fst :
    (baseChangeProdIso (S := S) G H).hom ≫ prodFst ((F).obj G) ((F).obj H) = (F).map (prodFst G H) :=
  productPullbackHom_fst G H

@[simp] theorem baseChangeProdIso_hom_snd :
    (baseChangeProdIso (S := S) G H).hom ≫ prodSnd ((F).obj G) ((F).obj H) = (F).map (prodSnd G H) :=
  productPullbackHom_snd G H

variable {G H} {G' H' : PDivisibleGroup (CommRingCat.of R) p}

/-- The product comparison is natural for actual tower maps on both factors. -/
theorem baseChangeProdIso_naturality (f : G ⟶ G') (g : H ⟶ H') :
    (F).map (Hom.prodMap f g) ≫ (baseChangeProdIso (S := S) G' H').hom =
      (baseChangeProdIso (S := S) G H).hom ≫ Hom.prodMap ((F).map f) ((F).map g) := by
  apply Hom.prod_hom_ext
  · simp only [Category.assoc, baseChangeProdIso_hom_fst, Hom.prodMap_fst]
    rw [← Category.assoc, baseChangeProdIso_hom_fst, ← (F).map_comp, ← (F).map_comp, Hom.prodMap_fst]
  · simp only [Category.assoc, baseChangeProdIso_hom_snd, Hom.prodMap_snd]
    rw [← Category.assoc, baseChangeProdIso_hom_snd, ← (F).map_comp, ← (F).map_comp, Hom.prodMap_snd]

end Langlands.PDivisibleGroup
