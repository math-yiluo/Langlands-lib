import Langlands.AbelianScheme.Kernel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry
open scoped CategoryTheory.MonObj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme
universe u
variable {S : Scheme.{u}} {G H : Grp (Over S)}

private lemma comp_mulRight_hom {T : Over S} (a : T ⟶ G.X)
    (x : 𝟙_ (Over S) ⟶ G.X) :
    a ≫ (GrpObj.mulRight x).hom = a * (toUnit T ≫ x) := by
  change a ≫ ((𝟙 G.X) * (toUnit G.X ≫ x)) = _
  rw [comp_mul]
  simp

private lemma comp_mulRight_inv {T : Over S} (a : T ⟶ G.X)
    (x : 𝟙_ (Over S) ⟶ G.X) :
    a ≫ (GrpObj.mulRight x).inv = a * (toUnit T ≫ x)⁻¹ := by
  change a ≫ ((𝟙 G.X) * (toUnit G.X ≫ x ≫ GrpObj.inv)) = _
  rw [comp_mul]
  simp only [Category.comp_id, ← Category.assoc, comp_toUnit]
  rfl

private def kernelFiberHom (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    (kernel f).X ⟶ pullback f.hom.hom (x ≫ f.hom.hom) :=
  pullback.lift ((kernelι f).hom.hom ≫ (GrpObj.mulRight x).hom)
    (toUnit (kernel f).X) (by
      rw [comp_mulRight_hom, mul_comp, (kernel_isPullback f).w]
      change (1 : (kernel f).X ⟶ H.X) *
        ((toUnit (kernel f).X ≫ x) ≫ f.hom.hom) = _
      simp)

private def kernelFiberInv (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    pullback f.hom.hom (x ≫ f.hom.hom) ⟶ (kernel f).X :=
  (kernel_isPullback f).lift
    (pullback.fst f.hom.hom (x ≫ f.hom.hom) ≫ (GrpObj.mulRight x).inv)
    (toUnit _) (by
      rw [comp_mulRight_inv, mul_comp, GrpObj.inv_comp, pullback.condition]
      rw [toUnit_unique (pullback.snd f.hom.hom (x ≫ f.hom.hom)) (toUnit _)]
      rw [Category.assoc, mul_inv_cancel]
      rfl)

private lemma kernelFiberHom_fst (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    kernelFiberHom f x ≫ pullback.fst f.hom.hom (x ≫ f.hom.hom) =
      (kernelι f).hom.hom ≫ (GrpObj.mulRight x).hom :=
  pullback.lift_fst _ _ _

private lemma kernelFiberInv_ι (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    kernelFiberInv f x ≫ (kernelι f).hom.hom =
      pullback.fst f.hom.hom (x ≫ f.hom.hom) ≫ (GrpObj.mulRight x).inv :=
  (kernel_isPullback f).lift_fst _ _ _

/-- Right translation by a source section identifies the kernel with the fibre over its image. -/
def kernelFiberIso (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    (kernel f).X ≅ pullback f.hom.hom (x ≫ f.hom.hom) where
  hom := kernelFiberHom f x
  inv := kernelFiberInv f x
  hom_inv_id := by
    apply (cancel_mono (kernelι f).hom.hom).mp
    rw [Category.assoc, kernelFiberInv_ι, ← Category.assoc, kernelFiberHom_fst,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · rw [Category.assoc, kernelFiberHom_fst, ← Category.assoc, kernelFiberInv_ι,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · exact Subsingleton.elim _ _

/-- The first projection of the split-fibre identification is right translation. -/
@[reassoc (attr := simp)]
lemma kernelFiberIso_hom_fst (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    (kernelFiberIso f x).hom ≫ pullback.fst f.hom.hom (x ≫ f.hom.hom) =
      (kernelι f).hom.hom ≫ (GrpObj.mulRight x).hom :=
  kernelFiberHom_fst f x

/-- The second projection is the unique map to the terminal object. -/
@[reassoc (attr := simp)]
lemma kernelFiberIso_hom_snd (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    (kernelFiberIso f x).hom ≫ pullback.snd f.hom.hom (x ≫ f.hom.hom) =
      toUnit (kernel f).X :=
  Subsingleton.elim _ _

/-- The inverse first translates a fibre point by the inverse source section. -/
@[reassoc (attr := simp)]
lemma kernelFiberIso_inv_ι (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    (kernelFiberIso f x).inv ≫ (kernelι f).hom.hom =
      pullback.fst f.hom.hom (x ≫ f.hom.hom) ≫ (GrpObj.mulRight x).inv :=
  kernelFiberInv_ι f x

/-- The underlying scheme isomorphism respects the structure morphisms to the base. -/
@[reassoc (attr := simp)]
lemma kernelFiberIso_hom_structure (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    (kernelFiberIso f x).hom.left ≫
        (pullback f.hom.hom (x ≫ f.hom.hom)).hom = (kernel f).X.hom :=
  (kernelFiberIso f x).hom.w

/-- The inverse scheme map also respects the structure morphisms to the base. -/
@[reassoc (attr := simp)]
lemma kernelFiberIso_inv_structure (f : G ⟶ H) (x : 𝟙_ (Over S) ⟶ G.X) :
    (kernelFiberIso f x).inv.left ≫ (kernel f).X.hom =
      (pullback f.hom.hom (x ≫ f.hom.hom)).hom :=
  (kernelFiberIso f x).inv.w

end Langlands.GroupScheme
