import Langlands.Representation.Category.DecompositionCentralProjectors

/-! # Central elements over a decomposition of a smooth category

* `catCenterRestrict`: an element of the centre of a category restricts to an element of the
  centre of every full subcategory.
* `catCenter_ext_of_everyObjectIsCoproduct`: if every object is a coproduct of objects of the
  full subcategories `P i`, two central elements agreeing on all objects of all `P i` are equal.
* `SmoothRep.assembledCenter`: for a decomposition (in the sense of Renard A.IX) of a category of
  smooth representations into full subcategories `P i`, a family of endomorphisms of the objects
  of each `P i`, natural with respect to the morphisms inside each `P i`, extends to a central
  element of the whole category (`SmoothRep.assembledCenter_app_of_mem`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe uG uV uI w w'

namespace Langlands

section Restrict

variable {C : Type w} [Category.{w'} C]

/-- The restriction of an element of the centre of a category to a full subcategory. -/
def catCenterRestrict (P : ObjectProperty C) (z : CatCenter C) :
    CatCenter P.FullSubcategory where
  app X := ObjectProperty.homMk (z.app X.obj)
  naturality X Y f := by
    apply ObjectProperty.hom_ext
    exact z.naturality f.hom

@[simp] theorem catCenterRestrict_app_hom (P : ObjectProperty C) (z : CatCenter C)
    (X : P.FullSubcategory) : ((catCenterRestrict P z).app X).hom = z.app X.obj := rfl

/-- Two central elements with equal restrictions to a full subcategory agree on its objects. -/
theorem catCenterRestrict_app_eq {P : ObjectProperty C} {z z' : CatCenter C}
    (h : catCenterRestrict P z = catCenterRestrict P z') {X : C} (hX : P X) :
    z.app X = z'.app X := by
  have h3 := congrArg (fun w : CatCenter P.FullSubcategory => (w.app ⟨X, hX⟩).hom) h
  simpa only [catCenterRestrict_app_hom] using h3

/-- If every object is the vertex of a coproduct of objects of the full subcategories `P i`,
two central elements that agree on every object of every `P i` are equal. -/
theorem catCenter_ext_of_everyObjectIsCoproduct {I : Type uI} {P : I → ObjectProperty C}
    (hP : Renard.EveryObjectIsCoproductOfComponents P) (z z' : CatCenter C)
    (h : ∀ i X, P i X → z.app X = z'.app X) : z = z' := by
  apply CatCenter.ext
  intro X
  obtain ⟨A, ι, hA, ⟨hc⟩⟩ := hP X
  apply Cofan.IsColimit.hom_ext hc
  intro j
  change ι j ≫ z.app X = ι j ≫ z'.app X
  rw [CatCenter.naturality z (ι j), CatCenter.naturality z' (ι j), h j (A j) (hA j)]

end Restrict

namespace SmoothRep

variable {G : Type uG} [Group G] [TopologicalSpace G] {I : Type uI}
  {P : I → ObjectProperty (SmoothRep.{0, uG, uV} ℂ G)}

/-- On a given coproduct presentation `(A j ⟶ Y)_j` of `Y` by objects `A j` of `P j`, the
endomorphism of `Y` acting by `w j (A j)` on the `j`-th summand. -/
def coproductDesc {Y : SmoothRep.{0, uG, uV} ℂ G}
    (w : ∀ i (X : SmoothRep.{0, uG, uV} ℂ G), P i X → (X ⟶ X))
    {A : I → SmoothRep.{0, uG, uV} ℂ G} {ι : ∀ j, A j ⟶ Y} (hA : ∀ j, P j (A j))
    (hc : IsColimit (Cofan.mk Y ι)) : Y ⟶ Y :=
  Cofan.IsColimit.desc hc (fun j => w j (A j) (hA j) ≫ ι j)

/-- For a decomposition and a family `w` natural inside each block, the endomorphism
`coproductDesc` of `Y` is compatible with every morphism from an object of a block to `Y`. -/
theorem comp_coproductDesc (hP : Renard.OffDiagonalHomsZero P)
    (w : ∀ i (X : SmoothRep.{0, uG, uV} ℂ G), P i X → (X ⟶ X))
    (hw : ∀ i (X Y : SmoothRep.{0, uG, uV} ℂ G) (hX : P i X) (hY : P i Y) (f : X ⟶ Y),
      f ≫ w i Y hY = w i X hX ≫ f)
    {Y : SmoothRep.{0, uG, uV} ℂ G}
    {A : I → SmoothRep.{0, uG, uV} ℂ G} {ι : ∀ j, A j ⟶ Y} (hA : ∀ j, P j (A j))
    (hc : IsColimit (Cofan.mk Y ι))
    {W : SmoothRep.{0, uG, uV} ℂ G} (j : I) (hW : P j W) (g : W ⟶ Y) :
    g ≫ coproductDesc w hA hc = w j W hW ≫ g := by
  classical
  have hg := comp_cofanComponent hP hA hc g j hW
  have hd : ι j ≫ coproductDesc w hA hc = w j (A j) (hA j) ≫ ι j :=
    Cofan.IsColimit.fac hc _ j
  have hwj := hw j W (A j) hW (hA j) (g ≫ cofanProjection hc j)
  calc g ≫ coproductDesc w hA hc
      = (g ≫ cofanProjection hc j ≫ ι j) ≫ coproductDesc w hA hc := by rw [hg]
    _ = (g ≫ cofanProjection hc j) ≫ (ι j ≫ coproductDesc w hA hc) := by
        simp only [Category.assoc]
    _ = ((g ≫ cofanProjection hc j) ≫ w j (A j) (hA j)) ≫ ι j := by
        rw [hd]; simp only [Category.assoc]
    _ = (w j W hW ≫ g ≫ cofanProjection hc j) ≫ ι j := by rw [hwj]
    _ = w j W hW ≫ g ≫ cofanProjection hc j ≫ ι j := by simp only [Category.assoc]
    _ = w j W hW ≫ g := by rw [hg]

variable (hP : Renard.IsCategoryDecomposition P)
  (w : ∀ i (X : SmoothRep.{0, uG, uV} ℂ G), P i X → (X ⟶ X))
  (hw : ∀ i (X Y : SmoothRep.{0, uG, uV} ℂ G) (hX : P i X) (hY : P i Y) (f : X ⟶ Y),
    f ≫ w i Y hY = w i X hX ≫ f)

/-- The component at `X` of the central element assembled from `w`, computed on the chosen
coproduct presentation of `X`. -/
def assembledCenterApp (X : SmoothRep.{0, uG, uV} ℂ G) : X ⟶ X :=
  coproductDesc w (hP.1 X).choose_spec.choose_spec.1 (hP.1 X).choose_spec.choose_spec.2.some

include hw in
theorem comp_assembledCenterApp {W Y : SmoothRep.{0, uG, uV} ℂ G} (j : I) (hW : P j W)
    (g : W ⟶ Y) : g ≫ assembledCenterApp hP w Y = w j W hW ≫ g :=
  comp_coproductDesc hP.2 w hw _ _ j hW g

include hw in
/-- The central element of the category of smooth representations assembled from a family of
endomorphisms of the objects of the blocks of a decomposition, natural inside each block. -/
def assembledCenter : CatCenter (SmoothRep.{0, uG, uV} ℂ G) where
  app X := assembledCenterApp hP w X
  naturality X Y f := by
    obtain ⟨A, ι, hA, ⟨hc⟩⟩ := hP.1 X
    apply Cofan.IsColimit.hom_ext hc
    intro j
    change ι j ≫ f ≫ assembledCenterApp hP w Y = ι j ≫ assembledCenterApp hP w X ≫ f
    have h1 := comp_assembledCenterApp hP w hw j (hA j) (ι j ≫ f)
    have h2 := comp_assembledCenterApp hP w hw j (hA j) (ι j)
    rw [Category.assoc] at h1
    rw [h1, ← Category.assoc (ι j), h2, Category.assoc]

include hw in
/-- On an object of the block `P i`, the assembled central element acts by `w i`. -/
theorem assembledCenter_app_of_mem (i : I) (X : SmoothRep.{0, uG, uV} ℂ G) (hX : P i X) :
    (assembledCenter hP w hw).app X = w i X hX := by
  have h := comp_assembledCenterApp hP w hw i hX (𝟙 X)
  rw [Category.id_comp, Category.comp_id] at h
  exact h

end SmoothRep

end Langlands
