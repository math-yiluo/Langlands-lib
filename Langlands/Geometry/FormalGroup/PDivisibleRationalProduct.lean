import Langlands.Geometry.FormalGroup.PDivisibleRationalHom
import Langlands.Geometry.FormalGroup.PDivisibleSplitOrderAction

/-! # Actual products and their rational morphisms -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.CommGroupScheme

variable {S : Scheme.{u}} {G H G' H' : CommGroupScheme S}

theorem prodInl_prodMap (f : G ⟶ G') (g : H ⟶ H') :
    prodInl G H ≫ prodMap f g = f ≫ prodInl G' H' := by
  apply prod_hom_ext
  · simp only [Category.assoc, prodMap_fst, prodInl_fst, Category.comp_id]
    rw [← Category.assoc, prodInl_fst, Category.id_comp]
  · simp only [Category.assoc, prodMap_snd, prodInl_snd, CategoryTheory.Limits.comp_zero]
    rw [← Category.assoc, prodInl_snd, CategoryTheory.Limits.zero_comp]

theorem prodInr_prodMap (f : G ⟶ G') (g : H ⟶ H') :
    prodInr G H ≫ prodMap f g = g ≫ prodInr G' H' := by
  apply prod_hom_ext
  · simp only [Category.assoc, prodMap_fst, prodInr_fst, CategoryTheory.Limits.comp_zero]
    rw [← Category.assoc, prodInr_fst, CategoryTheory.Limits.zero_comp]
  · simp only [Category.assoc, prodMap_snd, prodInr_snd, Category.comp_id]
    rw [← Category.assoc, prodInr_snd, Category.id_comp]

end Langlands.CommGroupScheme

namespace Langlands.PDivisibleGroup

variable {R : CommRingCat.{u}} {p : ℕ} [Fact p.Prime]
variable (G H : PDivisibleGroup R p)

/-- First projection of the actual product tower. -/
def prodFst : G.prod H ⟶ G :=
  Hom.ofNaturalTransformation {
    app n := CommGroupScheme.prodFst (G.inclusions.obj n) (H.inclusions.obj n)
    naturality _ _ i := CommGroupScheme.prodMap_fst (G.inclusions.map i) (H.inclusions.map i) }

/-- Second projection of the actual product tower. -/
def prodSnd : G.prod H ⟶ H :=
  Hom.ofNaturalTransformation {
    app n := CommGroupScheme.prodSnd (G.inclusions.obj n) (H.inclusions.obj n)
    naturality _ _ i := CommGroupScheme.prodMap_snd (G.inclusions.map i) (H.inclusions.map i) }

/-- First factor in the actual product tower. -/
def prodInl : G ⟶ G.prod H :=
  Hom.ofNaturalTransformation {
    app n := CommGroupScheme.prodInl (G.inclusions.obj n) (H.inclusions.obj n)
    naturality _ _ i := (CommGroupScheme.prodInl_prodMap (G.inclusions.map i) (H.inclusions.map i)).symm }

/-- Second factor in the actual product tower. -/
def prodInr : H ⟶ G.prod H :=
  Hom.ofNaturalTransformation {
    app n := CommGroupScheme.prodInr (G.inclusions.obj n) (H.inclusions.obj n)
    naturality _ _ i := (CommGroupScheme.prodInr_prodMap (G.inclusions.map i) (H.inclusions.map i)).symm }

@[simp] theorem prodInl_fst : prodInl G H ≫ prodFst G H = 𝟙 G :=
  Hom.ext fun n => CommGroupScheme.prodInl_fst (G.inclusions.obj n) (H.inclusions.obj n)

@[simp] theorem prodInl_snd : prodInl G H ≫ prodSnd G H = 0 :=
  Hom.ext fun n => CommGroupScheme.prodInl_snd (G.inclusions.obj n) (H.inclusions.obj n)

@[simp] theorem prodInr_fst : prodInr G H ≫ prodFst G H = 0 :=
  Hom.ext fun n => CommGroupScheme.prodInr_fst (G.inclusions.obj n) (H.inclusions.obj n)

@[simp] theorem prodInr_snd : prodInr G H ≫ prodSnd G H = 𝟙 H :=
  Hom.ext fun n => CommGroupScheme.prodInr_snd (G.inclusions.obj n) (H.inclusions.obj n)

theorem prod_decomposition : prodFst G H ≫ prodInl G H + prodSnd G H ≫ prodInr G H = 𝟙 (G.prod H) :=
  Hom.ext fun n => CommGroupScheme.prod_decomposition (G.inclusions.obj n) (H.inclusions.obj n)

variable {G H} {G' H' G'' H'' W : PDivisibleGroup R p}

@[simp] theorem Hom.prodMap_fst (f : G ⟶ G') (g : H ⟶ H') :
    Hom.prodMap f g ≫ prodFst G' H' = prodFst G H ≫ f :=
  Hom.ext fun n => CommGroupScheme.prodMap_fst (f.app n) (g.app n)

@[simp] theorem Hom.prodMap_snd (f : G ⟶ G') (g : H ⟶ H') :
    Hom.prodMap f g ≫ prodSnd G' H' = prodSnd G H ≫ g :=
  Hom.ext fun n => CommGroupScheme.prodMap_snd (f.app n) (g.app n)

namespace RationalHom

theorem prod_decomposition (G H : PDivisibleGroup R p) :
    comp (ofHom (prodFst G H)) (ofHom (prodInl G H)) +
      comp (ofHom (prodSnd G H)) (ofHom (prodInr G H)) = id (G.prod H) := by
  rw [← ofHom_comp, ← ofHom_comp, ← map_add, PDivisibleGroup.prod_decomposition, ofHom_id]

/-- The projections of the actual product still distinguish rational maps. -/
theorem prod_hom_ext {f g : RationalHom W (G.prod H)}
    (hf : comp f (ofHom (prodFst G H)) = comp g (ofHom (prodFst G H)))
    (hg : comp f (ofHom (prodSnd G H)) = comp g (ofHom (prodSnd G H))) : f = g := by
  calc
    f = comp f (id (G.prod H)) := (comp_id f).symm
    _ = comp g (id (G.prod H)) := by
      rw [← prod_decomposition, comp_add, comp_add]
      simp only [← comp_assoc, hf, hg]
    _ = g := comp_id g

/-- The block diagonal map with the specified two rational components. -/
def prodMap (f : RationalHom G G') (g : RationalHom H H') : RationalHom (G.prod H) (G'.prod H') :=
  comp (ofHom (prodFst G H)) (comp f (ofHom (prodInl G' H'))) +
    comp (ofHom (prodSnd G H)) (comp g (ofHom (prodInr G' H')))

@[simp] theorem prodMap_fst (f : RationalHom G G') (g : RationalHom H H') :
    comp (prodMap f g) (ofHom (prodFst G' H')) = comp (ofHom (prodFst G H)) f := by
  simp only [prodMap, add_comp, comp_assoc, ← ofHom_comp, prodInl_fst, prodInr_fst,
    ofHom_id, map_zero, comp_id, comp_zero, add_zero]

@[simp] theorem prodMap_snd (f : RationalHom G G') (g : RationalHom H H') :
    comp (prodMap f g) (ofHom (prodSnd G' H')) = comp (ofHom (prodSnd G H)) g := by
  simp only [prodMap, add_comp, comp_assoc, ← ofHom_comp, prodInl_snd, prodInr_snd,
    ofHom_id, map_zero, comp_id, comp_zero, zero_add]

@[simp] theorem prodMap_id (G H : PDivisibleGroup R p) : prodMap (id G) (id H) = id (G.prod H) := by
  apply prod_hom_ext
  · rw [prodMap_fst, comp_id, id_comp]
  · rw [prodMap_snd, comp_id, id_comp]

@[simp] theorem prodMap_comp (f : RationalHom G G') (g : RationalHom H H')
    (f' : RationalHom G' G'') (g' : RationalHom H' H'') :
    comp (prodMap f g) (prodMap f' g') = prodMap (comp f f') (comp g g') := by
  apply prod_hom_ext
  · rw [comp_assoc, prodMap_fst, ← comp_assoc, prodMap_fst, comp_assoc, prodMap_fst]
  · rw [comp_assoc, prodMap_snd, ← comp_assoc, prodMap_snd, comp_assoc, prodMap_snd]

@[simp] theorem prodMap_ofHom (f : G ⟶ G') (g : H ⟶ H') :
    prodMap (ofHom f) (ofHom g) = ofHom (Hom.prodMap f g) := by
  apply prod_hom_ext
  · rw [prodMap_fst, ← ofHom_comp, ← ofHom_comp, Hom.prodMap_fst]
  · rw [prodMap_snd, ← ofHom_comp, ← ofHom_comp, Hom.prodMap_snd]

end RationalHom

end Langlands.PDivisibleGroup
