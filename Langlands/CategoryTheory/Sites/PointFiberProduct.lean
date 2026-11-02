import Langlands.CategoryTheory.Sites.PseudofunctorPointFiber
import Langlands.CategoryTheory.Sites.SlicePresheafTotal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.ProdComparison
import Mathlib.CategoryTheory.Groupoid

/-! # Point fibres as total Hom presheaves over a product -/

noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits Opposite

namespace Langlands.CategoryTheory.PointFiberProduct

open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {U T : C} [HasBinaryProduct U T]

/-- The product base, as an actual object over the test base. -/
abbrev productOver (U T : C) [HasBinaryProduct U T] : Over T :=
  Over.mk (prod.snd : U ⨯ T ⟶ T)

/-- A map into the product retains the specified map to the test base. -/
def mapsToProductEquiv (Z : Over T) :
    (Z.left ⟶ U) ≃ (Z ⟶ productOver U T) where
  toFun a := Over.homMk (prod.lift a Z.hom) (by simp)
  invFun b := b.left ≫ prod.fst
  left_inv a := by simp
  right_inv b := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · simp
    · simpa using b.w.symm

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  [∀ A : C, IsGroupoid (F.obj (.mk (op A)))]
  (ξ : F.obj (.mk (op U))) (η : F.obj (.mk (op T)))

private def isoHomEquiv {A : C} {M N : F.obj (.mk (op A))} :
    (M ≅ N) ≃ (M ⟶ N) where
  toFun e := e.hom
  invFun f := asIso f
  left_inv e := by apply Iso.ext; rfl
  right_inv f := rfl

/-- Composition comparison for an actual pullback along a composite. -/
def compIso {A B D : C} (p : A ⟶ B) (q : B ⟶ D)
    (r : A ⟶ D) (h : p ≫ q = r) (M : F.obj (.mk (op D))) :
    (F.map r.op.toLoc).toFunctor.obj M ≅
      (F.map p.op.toLoc).toFunctor.obj ((F.map q.op.toLoc).toFunctor.obj M) :=
  (Cat.Hom.toNatIso (F.mapComp' q.op.toLoc p.op.toLoc r.op.toLoc (by
    rw [← Quiver.Hom.comp_toLoc, ← op_comp, h]))).app M

/-- The fixed two pullbacks on the product give the Hom presheaf there. -/
abbrev productHom : (Over (U ⨯ T))ᵒᵖ ⥤ Type v' :=
  F.presheafHom ((F.map (prod.fst : U ⨯ T ⟶ U).op.toLoc).toFunctor.obj ξ)
    ((F.map (prod.snd : U ⨯ T ⟶ T).op.toLoc).toFunctor.obj η)

private def homEquiv (Z : Over T) (a : Z.left ⟶ U) :
    ((F.map a.op.toLoc).toFunctor.obj ξ ⟶
      (F.map Z.hom.op.toLoc).toFunctor.obj η) ≃
        (productHom F ξ η).obj
          (op (Over.mk (mapsToProductEquiv Z a).left)) :=
  (Iso.homFromEquiv (compIso F (prod.lift a Z.hom) prod.fst a
    (by simp) ξ)).trans
      (Iso.homToEquiv (compIso F (prod.lift a Z.hom) prod.snd Z.hom
        (by simp) η))

/-- Retain the actual product map and transport the actual isomorphism
through the pseudofunctor composition comparisons. -/
def pointsEquiv (Z : Over T) :
    PseudofunctorPointFiber.Points F ξ η Z ≃
      SlicePresheafTotal.Points (productOver U T) (productHom F ξ η) Z :=
  Equiv.sigmaCongr (mapsToProductEquiv Z) (fun a ↦
    (isoHomEquiv F).trans (homEquiv F ξ η Z a))

private lemma restrict_eq_mk {B : C} (Q : Over B)
    (G : (Over Q.left)ᵒᵖ ⥤ Type v') {Z Z' : Over B}
    (g : Z' ⟶ Z) (b : Z ⟶ Q)
    (s : G.obj (op (Over.mk b.left))) (b' : Z' ⟶ Q)
    (hb : g ≫ b = b') :
    SlicePresheafTotal.restrict Q G g ⟨b, s⟩ =
      ⟨b', G.map (Over.homMk (U := Over.mk b'.left)
        (V := Over.mk b.left) g.left (congrArg Over.Hom.left hb)).op s⟩ := by
  subst b'
  rfl

lemma pointsEquiv_restrict {Z Z' : Over T} (g : Z' ⟶ Z)
    (x : PseudofunctorPointFiber.Points F ξ η Z) :
    pointsEquiv F ξ η Z' (PseudofunctorPointFiber.restrict F ξ η g x) =
      SlicePresheafTotal.restrict (productOver U T) (productHom F ξ η) g
        (pointsEquiv F ξ η Z x) := by
  rcases x with ⟨a, e⟩
  change (⟨mapsToProductEquiv Z' (g.left ≫ a),
    homEquiv F ξ η Z' (g.left ≫ a)
      (PseudofunctorPointFiber.pullIso e g.left (g.left ≫ a) Z'.hom rfl g.w).hom⟩ :
      SlicePresheafTotal.Points (productOver U T) (productHom F ξ η) Z') =
    SlicePresheafTotal.restrict (productOver U T) (productHom F ξ η) g
      ⟨mapsToProductEquiv Z a, homEquiv F ξ η Z a e.hom⟩
  have hb : g ≫ mapsToProductEquiv Z a = mapsToProductEquiv Z' (g.left ≫ a) := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext
    · simp [mapsToProductEquiv]
    · simp [mapsToProductEquiv, g.w]
  rw [restrict_eq_mk _ _ g _ _ _ hb]
  congr 1
  dsimp [homEquiv, compIso, mapsToProductEquiv, PseudofunctorPointFiber.pullIso, pullHom]
  simp only [Category.assoc, Functor.map_comp]
  rw [F.mapComp'₀₁₃_inv_comp_mapComp'₀₂₃_hom_app_assoc _ _ _ _ _ _ _ _ (by
      simp only [← Quiver.Hom.comp_toLoc, ← op_comp]
      congr 1
      simp),
    F.mapComp'₀₂₃_inv_comp_mapComp'₀₁₃_hom_app _ _ _ _ _ _ _ _ (by
      simp only [← Quiver.Hom.comp_toLoc, ← op_comp]
      congr 1
      simp [g.w])]

/-- The comparison is natural on the full slice, with actual maps and arrows. -/
def presheafIso :
    PseudofunctorPointFiber.presheaf F ξ η ≅
      SlicePresheafTotal.total (productOver U T) (productHom F ξ η) :=
  NatIso.ofComponents (fun Z ↦ (pointsEquiv F ξ η Z.unop).toIso) (by
    intro Z Z' g
    apply ConcreteCategory.hom_ext
    intro x
    exact pointsEquiv_restrict F ξ η g.unop x)

end Langlands.CategoryTheory.PointFiberProduct
