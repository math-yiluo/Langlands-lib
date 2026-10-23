import Langlands.AbelianScheme.Rational
import Langlands.CategoryTheory.RationalizationLift

/-! # Base change of actual rational homomorphisms of abelian schemes -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj CategoryTheory.Obj
universe u

namespace Langlands.CommGroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- Actual pullback preserves the pointwise additive law on homomorphisms. -/
instance baseChange_additive : (baseChange b).Additive where
  map_add {G H f g} := by
    let : IsCommMonObj ((GroupScheme.baseChange b).obj H.toGrp).X :=
      Functor.isCommMonObj_obj (F := Over.pullback b) (M := H.X)
    change Additive.ofMul ((GroupScheme.baseChange b).map (f.toMul * g.toMul)) =
      Additive.ofMul ((GroupScheme.baseChange b).map f.toMul *
        (GroupScheme.baseChange b).map g.toMul)
    congr 1
    apply Grp.hom_ext
    change (Over.pullback b).map (f.toMul.hom.hom * g.toMul.hom.hom) =
      (Over.pullback b).map f.toMul.hom.hom * (Over.pullback b).map g.toMul.hom.hom
    exact Functor.map_mul _ _ _

end Langlands.CommGroupScheme

namespace Langlands.AbelianScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)

/-- The bundled abelian-scheme pullback is additive on actual homomorphisms. -/
instance baseChange_additive : (baseChange b).Additive where
  map_add {_A _B f g} :=
    (CommGroupScheme.baseChange b).map_add (f := commHom f) (g := commHom g)

/-- Pullback extends to the category of actual rational homomorphisms. -/
def rationalBaseChange : RationalCategory S ⥤ RationalCategory S' :=
  Rationalization.lift (baseChange b ⋙ Rationalization.inclusion)

instance : (rationalBaseChange b).Additive := inferInstanceAs
  (Rationalization.lift (baseChange b ⋙ Rationalization.inclusion)).Additive

/-- The rational-linear map on the actual rationalized Hom groups. -/
def rationalBaseChangeHom {A B : AbelianScheme S} :
    Hom0 A B →ₗ[ℚ] Hom0 ((baseChange b).obj A) ((baseChange b).obj B) :=
  Rationalization.liftHom (baseChange b ⋙ Rationalization.inclusion)

@[simp] theorem rationalBaseChangeHom_tmul {A B : AbelianScheme S}
    (q : ℚ) (f : A ⟶ B) :
    rationalBaseChangeHom b (q ⊗ₜ[ℤ] f) = q ⊗ₜ[ℤ] (baseChange b).map f := by
  change q • ((1 : ℚ) ⊗ₜ[ℤ] (baseChange b).map f) = _
  simp [TensorProduct.smul_tmul']

@[simp] theorem rationalBaseChangeHom_ofHom {A B : AbelianScheme S} (f : A ⟶ B) :
    rationalBaseChangeHom b (Rationalization.ofHom f) =
      Rationalization.ofHom ((baseChange b).map f) :=
  Rationalization.liftHom_ofHom _ f

@[simp] theorem rationalBaseChange_map {A B : AbelianScheme S} (f : Hom0 A B) :
    (rationalBaseChange b).map (f : Rationalization.of A ⟶ Rationalization.of B) =
      rationalBaseChangeHom b f := rfl

@[simp] theorem rationalBaseChangeHom_identity (A : AbelianScheme S) :
    rationalBaseChangeHom b (Rationalization.identity A) =
      Rationalization.identity ((baseChange b).obj A) :=
  (rationalBaseChange b).map_id (Rationalization.of A)

theorem rationalBaseChangeHom_comp {A B C : AbelianScheme S}
    (f : Hom0 A B) (g : Hom0 B C) :
    rationalBaseChangeHom b (Rationalization.comp A B C f g) =
      Rationalization.comp _ _ _ (rationalBaseChangeHom b f) (rationalBaseChangeHom b g) :=
  Rationalization.liftHom_comp _ f g

/-- Restricting rational pullback to integral morphisms recovers ordinary pullback. -/
def rationalBaseChangeInclusionIso :
    Rationalization.inclusion ⋙ rationalBaseChange b ≅
      baseChange b ⋙ Rationalization.inclusion :=
  Rationalization.inclusionLiftIso (baseChange b ⋙ Rationalization.inclusion)

/-- The induced unital rational algebra homomorphism on actual endomorphisms. -/
def rationalBaseChangeEnd (A : AbelianScheme S) :
    End0 A →ₐ[ℚ] End0 ((baseChange b).obj A) :=
  Rationalization.liftEnd (baseChange b ⋙ Rationalization.inclusion) A

@[simp] theorem rationalBaseChangeEnd_apply (A : AbelianScheme S) (f : End0 A) :
    rationalBaseChangeEnd b A f = rationalBaseChangeHom b f := rfl

@[simp] theorem rationalBaseChangeEnd_ofEnd (A : AbelianScheme S) (f : CategoryTheory.End A) :
    rationalBaseChangeEnd b A (Rationalization.ofEnd A f) =
      Rationalization.ofEnd ((baseChange b).obj A) ((baseChange b).map f) :=
  Rationalization.liftEnd_ofEnd _ A f

/-- Actual rational isogenies remain invertible after arbitrary base change. -/
def rationalBaseChangeIso {A B : AbelianScheme S}
    (e : Rationalization.of A ≅ Rationalization.of B) :
    Rationalization.of ((baseChange b).obj A) ≅ Rationalization.of ((baseChange b).obj B) :=
  (rationalBaseChange b).mapIso e

@[simp] theorem rationalBaseChangeIso_hom {A B : AbelianScheme S}
    (e : Rationalization.of A ≅ Rationalization.of B) :
    (rationalBaseChangeIso b e).hom = rationalBaseChangeHom b e.hom := rfl

@[simp] theorem rationalBaseChangeIso_inv {A B : AbelianScheme S}
    (e : Rationalization.of A ≅ Rationalization.of B) :
    (rationalBaseChangeIso b e).inv = rationalBaseChangeHom b e.inv := rfl

end Langlands.AbelianScheme
