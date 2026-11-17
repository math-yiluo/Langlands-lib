import Langlands.GroupScheme.IsomorphismPresheaf
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.SubcanonicalOver
import Mathlib.Algebra.Category.Grp.Limits

/-! # The sheaf of natural local group isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalGroupIso

variable {S : Scheme.{u}} {G H : GroupScheme S} {U : Over S}

/-- Regard a natural local group-isomorphism family as a morphism of the
restricted group-valued point functors. -/
def toHom (e : LocalGroupIso G H U) :
    (presheafHom G.points H.points).obj (op U) where
  app V := GrpCat.ofHom (e.toFun V.unop.hom).toMonoidHom
  naturality V W t := by
    ext g
    change e.toFun W.unop.hom (t.unop.left ≫ g) =
      t.unop.left ≫ e.toFun V.unop.hom g
    rw [← Over.w t.unop]
    exact e.naturality t.unop.left _ g

/-- Recover a local family from an isomorphism of the restricted point functors. -/
def ofNatIso
    (e : (Over.forget U).op ⋙ G.points ≅ (Over.forget U).op ⋙ H.points) :
    LocalGroupIso G H U where
  toFun a := (e.app (op (Over.mk a))).groupIsoToMulEquiv
  naturality t a g := by
    let r : Over.mk (t ≫ a) ⟶ Over.mk a := Over.homMk t rfl
    exact ConcreteCategory.congr_hom (e.hom.naturality r.op) g

@[simp] theorem toHom_refine (e : LocalGroupIso G H U) {V : Over S} (r : V ⟶ U) :
    (e.refine r).toHom = (presheafHom G.points H.points).map r.op e.toHom := rfl

@[simp] theorem symm_refine (e : LocalGroupIso G H U) {V : Over S} (r : V ⟶ U) :
    (e.refine r).symm = e.symm.refine r := rfl

@[simp] theorem toHom_comp_symm (e : LocalGroupIso G H U) :
    e.toHom ≫ e.symm.toHom = 𝟙 ((Over.forget U).op ⋙ G.points) := by
  ext V g
  exact (e.toFun V.unop.hom).symm_apply_apply g

@[simp] theorem symm_toHom_comp (e : LocalGroupIso G H U) :
    e.symm.toHom ≫ e.toHom = 𝟙 ((Over.forget U).op ⋙ H.points) := by
  ext V g
  exact (e.toFun V.unop.hom).apply_symm_apply g

/-- Forgetting the inverses of local families is injective. -/
theorem toHom_injective : Function.Injective (toHom (G := G) (H := H) (U := U)) := by
  intro e e' h
  apply ext_toFun
  intro V a g
  exact ConcreteCategory.congr_hom (congr_app h (op (Over.mk a))) g

/-- The point functor of any group scheme is a sheaf for every subcanonical
Grothendieck topology on the category of relative schemes. -/
theorem points_isSheaf (J : GrothendieckTopology (Over S)) [J.Subcanonical]
    (G : GroupScheme S) : Presheaf.IsSheaf J G.points := by
  apply Presheaf.isSheaf_of_isSheaf_comp J G.points (forget GrpCat)
  let := G.pointsRepresentableBy.isRepresentable
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/-- Natural local group-isomorphism families glue uniquely for every
subcanonical topology, on all relative scheme tests. -/
theorem isSheaf (J : GrothendieckTopology (Over S)) [J.Subcanonical] :
    Presheaf.IsSheaf J (presheaf G H) := by
  let FH := presheafHom G.points H.points
  let HF := presheafHom H.points G.points
  have hFH : Presieve.IsSheaf J FH :=
    (isSheaf_iff_isSheaf_of_type _ _).mp ((points_isSheaf J H).hom G.points)
  have hHF : Presieve.IsSheaf J HF :=
    (isSheaf_iff_isSheaf_of_type _ _).mp ((points_isSheaf J G).hom H.points)
  rw [isSheaf_iff_isSheaf_of_type]
  intro U R hR x hx
  let xh : Presieve.FamilyOfElements FH R.arrows := fun V f hf => (x f hf).toHom
  let xi : Presieve.FamilyOfElements HF R.arrows := fun V f hf => (x f hf).symm.toHom
  have hxh : xh.Compatible := by
    intro V W Z a b f g hf hg hab
    exact congrArg toHom (hx a b hf hg hab)
  have hxi : xi.Compatible := by
    intro V W Z a b f g hf hg hab
    exact congrArg (fun e => e.symm.toHom) (hx a b hf hg hab)
  let α := (hFH R hR).amalgamate xh hxh
  let β := (hHF R hR).amalgamate xi hxi
  have ha : ∀ (V : Over S) (f : V ⟶ U) (hf : R f),
      FH.map f.op α = (x f hf).toHom := by
    intro V f hf
    exact (hFH R hR).valid_glue hxh f hf
  have hb : ∀ (V : Over S) (f : V ⟶ U) (hf : R f),
      HF.map f.op β = (x f hf).symm.toHom := by
    intro V f hf
    exact (hHF R hR).valid_glue hxi f hf
  have hFG : α ≫ β = 𝟙 ((Over.forget U).op ⋙ G.points) := by
    have hGG := (isSheaf_iff_isSheaf_of_type _ _).mp
      ((points_isSheaf J G).hom G.points)
    apply (hGG R hR).isSeparatedFor.ext
    intro V f hf
    change Functor.whiskerLeft (Over.map f).op α ≫
        Functor.whiskerLeft (Over.map f).op β = 𝟙 _
    rw [show Functor.whiskerLeft (Over.map f).op α = (x f hf).toHom from ha V f hf,
      show Functor.whiskerLeft (Over.map f).op β = (x f hf).symm.toHom from hb V f hf]
    exact toHom_comp_symm _
  have hGF : β ≫ α = 𝟙 ((Over.forget U).op ⋙ H.points) := by
    have hHH := (isSheaf_iff_isSheaf_of_type _ _).mp
      ((points_isSheaf J H).hom H.points)
    apply (hHH R hR).isSeparatedFor.ext
    intro V f hf
    change Functor.whiskerLeft (Over.map f).op β ≫
        Functor.whiskerLeft (Over.map f).op α = 𝟙 _
    rw [show Functor.whiskerLeft (Over.map f).op β = (x f hf).symm.toHom from hb V f hf,
      show Functor.whiskerLeft (Over.map f).op α = (x f hf).toHom from ha V f hf]
    exact symm_toHom_comp _
  let e : (Over.forget U).op ⋙ G.points ≅ (Over.forget U).op ⋙ H.points :=
    ⟨α, β, hFG, hGF⟩
  have he : (ofNatIso e).toHom = α := rfl
  refine ⟨ofNatIso e, ?_, ?_⟩
  · intro V f hf
    apply toHom_injective
    change ((ofNatIso e).refine f).toHom = (x f hf).toHom
    rw [toHom_refine, he]
    exact ha V f hf
  · intro e' he'
    apply toHom_injective
    change e'.toHom = α
    apply (hFH R hR).isSeparatedFor.ext
    intro V f hf
    rw [ha V f hf, ← toHom_refine]
    exact congrArg toHom (he' f hf)

/-- The sheaf of natural local isomorphisms, with every relative scheme as a test. -/
def sheaf (G H : GroupScheme S) (J : GrothendieckTopology (Over S)) [J.Subcanonical] :
    Sheaf J (Type (u + 1)) :=
  ⟨presheaf G H, isSheaf J⟩

end Langlands.GroupScheme.LocalGroupIso
