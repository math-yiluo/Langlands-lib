import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Yoneda

/-! # Total presheaves for a map of slice bases -/

noncomputable section

universe v u w

open CategoryTheory Opposite

namespace Langlands.CategoryTheory.SlicePresheafTotal

variable {C : Type u} [Category.{v} C] {T : C}

/-- A section over `Z` consists of a map from `Z` to the new base and
a section over that map. -/
abbrev Points (Q : Over T) (G : (Over Q.left)ᵒᵖ ⥤ Type w) (Z : Over T) :=
  Σ a : Z ⟶ Q, G.obj (op (Over.mk a.left))

private def restrictVia (Q : Over T) (G : (Over Q.left)ᵒᵖ ⥤ Type w)
    {Z Z' : Over T} (g : Z' ⟶ Z) (x : Points Q G Z)
    (b : Z' ⟶ Q) (hb : g ≫ x.1 = b) : Points Q G Z' :=
  ⟨b, G.map (Over.homMk (U := Over.mk b.left) (V := Over.mk x.1.left)
    g.left (congrArg Over.Hom.left hb)).op x.2⟩

/-- Restriction retains the actual map to the new base. -/
def restrict (Q : Over T) (G : (Over Q.left)ᵒᵖ ⥤ Type w)
    {Z Z' : Over T} (g : Z' ⟶ Z) (x : Points Q G Z) : Points Q G Z' :=
  restrictVia Q G g x (g ≫ x.1) rfl

private lemma restrictVia_eq (Q : Over T) (G : (Over Q.left)ᵒᵖ ⥤ Type w)
    {Z Z' : Over T} (g : Z' ⟶ Z) (x : Points Q G Z)
    (b : Z' ⟶ Q) (hb : g ≫ x.1 = b) :
    restrictVia Q G g x b hb = restrict Q G g x := by
  subst b
  rfl

@[simp]
lemma restrict_id (Q : Over T) (G : (Over Q.left)ᵒᵖ ⥤ Type w)
    (Z : Over T) (x : Points Q G Z) :
    restrict Q G (𝟙 Z) x = x := by
  rcases x with ⟨a, s⟩
  rw [← restrictVia_eq Q G (𝟙 Z) ⟨a, s⟩ a (Category.id_comp a)]
  dsimp only [restrictVia]
  congr 1
  exact G.map_id_apply _ s

@[simp]
lemma restrict_comp (Q : Over T) (G : (Over Q.left)ᵒᵖ ⥤ Type w)
    {Z Z' Z'' : Over T} (g : Z' ⟶ Z) (h : Z'' ⟶ Z') (x : Points Q G Z) :
    restrict Q G (h ≫ g) x = restrict Q G h (restrict Q G g x) := by
  rcases x with ⟨a, s⟩
  rw [← restrictVia_eq Q G (h ≫ g) ⟨a, s⟩ (h ≫ g ≫ a) (Category.assoc h g a)]
  dsimp only [restrict, restrictVia]
  congr 1
  exact G.map_comp_apply
    (Over.homMk (U := Over.mk (g.left ≫ a.left))
      (V := Over.mk a.left) g.left rfl).op
    (Over.homMk (U := Over.mk (h.left ≫ g.left ≫ a.left))
      (V := Over.mk (g.left ≫ a.left)) h.left rfl).op s

/-- The total presheaf over the old base. -/
def total (Q : Over T) (G : (Over Q.left)ᵒᵖ ⥤ Type w) :
    (Over T)ᵒᵖ ⥤ Type (max v w) where
  obj Z := Points Q G Z.unop
  map g := ↾(restrict Q G g.unop)
  map_id Z := by
    apply ConcreteCategory.hom_ext
    intro x
    exact restrict_id Q G Z.unop x
  map_comp g h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact restrict_comp Q G g.unop h.unop x

/-- A natural isomorphism over the new base induces one over the old base. -/
def totalIso (Q : Over T) {G H : (Over Q.left)ᵒᵖ ⥤ Type w} (e : G ≅ H) :
    total Q G ≅ total Q H :=
  NatIso.ofComponents (fun Z ↦ (Equiv.sigmaCongrRight
    (fun a : Z.unop ⟶ Q ↦ (e.app (op (Over.mk a.left))).toEquiv)).toIso) (by
      intro Z Z' g
      apply ConcreteCategory.hom_ext
      rintro ⟨a, s⟩
      change (⟨g.unop ≫ a, (e.hom.app _)
        (G.map (Over.homMk (U := Over.mk (g.unop.left ≫ a.left))
          (V := Over.mk a.left) g.unop.left rfl).op s)⟩ : Points Q H Z'.unop) =
        ⟨g.unop ≫ a, H.map (Over.homMk (U := Over.mk (g.unop.left ≫ a.left))
          (V := Over.mk a.left) g.unop.left rfl).op ((e.hom.app _) s)⟩
      congr 1
      exact ConcreteCategory.congr_hom (e.hom.naturality
        (Over.homMk (U := Over.mk (g.unop.left ≫ a.left))
          (V := Over.mk a.left) g.unop.left rfl).op) s)

/-- The representing object is composed with the original map to `T`. -/
abbrev composite (Q : Over T) (R : Over Q.left) : Over T :=
  Over.mk (R.hom ≫ Q.hom)

private lemma yonedaPoints_ext (Q : Over T) (R : Over Q.left) {Z : Over T}
    {x y : Points Q (uliftYoneda.{w}.obj R) Z}
    (ha : x.1 = y.1) (hs : x.2.down.left = y.2.down.left) : x = y := by
  rcases x with ⟨a, s⟩
  rcases y with ⟨b, t⟩
  dsimp only at ha hs
  subst b
  apply congrArg (Sigma.mk a)
  apply ULift.ext
  exact Over.OverMorphism.ext hs

/-- Maps to the composed representing object retain both the base map and
the actual map into its original representing object. -/
def yonedaPointsEquiv (Q : Over T) (R : Over Q.left) (Z : Over T) :
    ULift.{w} (Z ⟶ composite Q R) ≃
      Points Q (uliftYoneda.{w}.obj R) Z where
  toFun b :=
    ⟨Over.homMk (U := Z) (V := Q) (b.down.left ≫ R.hom)
      (by simpa only [composite, Over.mk_hom, Category.assoc] using b.down.w),
      ULift.up (Over.homMk (U := Over.mk (b.down.left ≫ R.hom))
        (V := R) b.down.left rfl)⟩
  invFun x := ULift.up (Over.homMk (U := Z) (V := composite Q R) x.2.down.left
    (by
      change x.2.down.left ≫ (R.hom ≫ Q.hom) = Z.hom
      rw [← Category.assoc, x.2.down.w]
      exact x.1.w))
  left_inv b := by
    apply ULift.ext
    apply Over.OverMorphism.ext
    rfl
  right_inv x := by
    apply yonedaPoints_ext
    · apply Over.OverMorphism.ext
      exact x.2.down.w
    · rfl

/-- Totalization of a represented presheaf is represented by composition
of its actual representing object with the map to the original base. -/
def totalYonedaIso (Q : Over T) (R : Over Q.left) :
    uliftYoneda.{w}.obj (composite Q R) ≅
      total Q (uliftYoneda.{w}.obj R) :=
  NatIso.ofComponents (fun Z ↦ (yonedaPointsEquiv Q R Z.unop).toIso) (by
    intro Z Z' g
    apply ConcreteCategory.hom_ext
    intro b
    apply yonedaPoints_ext
    · apply Over.OverMorphism.ext
      exact Category.assoc g.unop.left b.down.left R.hom
    · rfl)

/-- A full natural representation over the new base yields one over the
original base, on every test object and every restriction map. -/
def representationIso (Q : Over T) {G : (Over Q.left)ᵒᵖ ⥤ Type (max v w)}
    (R : Over Q.left) (e : uliftYoneda.{w}.obj R ≅ G) :
    uliftYoneda.{w}.obj (composite Q R) ≅ total Q G :=
  totalYonedaIso Q R ≪≫ totalIso Q e

end Langlands.CategoryTheory.SlicePresheafTotal
