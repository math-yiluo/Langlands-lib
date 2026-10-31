import Langlands.AbelianScheme.LieAction

/-! # The relative Lie functor on rational homomorphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}} {R : CommRingCat.{u}}
    [Algebra ℚ R] (p : S ⟶ Spec R)

/-- Extend the actual additive Lie functor using the rational scalars from the base. -/
def rationalLieFunctor : RationalCategory S ⥤ S.Modules := by
  letI := Langlands.Scheme.Modules.rationalLinearOverBase p
  exact Langlands.Rationalization.lift (lieFunctor S)

instance rationalLieFunctor_additive : (rationalLieFunctor p).Additive := by
  let := Langlands.Scheme.Modules.rationalLinearOverBase p
  exact inferInstanceAs (Langlands.Rationalization.lift (lieFunctor S)).Additive

/-- The differential of an actual rational homomorphism of abelian schemes. -/
def lieMap0 {A B : AbelianScheme S} (f : Hom0 A B) : A.Lie ⟶ B.Lie :=
  (rationalLieFunctor p).map
    (X := Langlands.Rationalization.of A) (Y := Langlands.Rationalization.of B) f

@[simp]
theorem lieMap0_ofHom {A B : AbelianScheme S} (f : A ⟶ B) :
    lieMap0 p (homToHom0 f) = lieMap f := by
  let := Langlands.Scheme.Modules.rationalLinearOverBase p
  exact Langlands.Rationalization.liftHom_ofHom (lieFunctor S) f

@[simp]
theorem lieMap0_tmul {A B : AbelianScheme S} (q : ℚ) (f : A ⟶ B) :
    letI := Langlands.Scheme.Modules.rationalLinearOverBase p
    lieMap0 p (q ⊗ₜ[ℤ] f) = q • lieMap f := by
  let := Langlands.Scheme.Modules.rationalLinearOverBase p
  rfl

@[simp]
theorem lieMap0_id (A : AbelianScheme S) :
    lieMap0 p (id0 A) = 𝟙 A.Lie :=
  (rationalLieFunctor p).map_id (Langlands.Rationalization.of A)

@[simp]
theorem lieMap0_comp {A B C : AbelianScheme S} (f : Hom0 A B) (g : Hom0 B C) :
    lieMap0 p (comp0 A B C f g) = lieMap0 p f ≫ lieMap0 p g :=
  (rationalLieFunctor p).map_comp f g

@[simp]
theorem lieMap0_add {A B : AbelianScheme S} (f g : Hom0 A B) :
    lieMap0 p (f + g) = lieMap0 p f + lieMap0 p g :=
  (rationalLieFunctor p).map_add

/-- The map on rational Hom is linear for the actual rational base scalars. -/
def lieMap0Linear (A B : AbelianScheme S) :
    letI := Langlands.Scheme.Modules.rationalLinearOverBase p
    Hom0 A B →ₗ[ℚ] (A.Lie ⟶ B.Lie) := by
  letI := Langlands.Scheme.Modules.rationalLinearOverBase p
  exact Langlands.Rationalization.liftHom (lieFunctor S)

@[simp]
theorem lieMap0Linear_apply {A B : AbelianScheme S} (f : Hom0 A B) :
    lieMap0Linear p A B f = lieMap0 p f := rfl

@[simp]
theorem lieMap0_end (A : AbelianScheme S) (f : End0 A) :
    lieMap0 p f = lieEnd0Action p A f := rfl

/-- Restriction along the integral inclusion recovers the actual Lie functor. -/
def rationalLieInclusionIso : rationalization S ⋙ rationalLieFunctor p ≅ lieFunctor S := by
  letI := Langlands.Scheme.Modules.rationalLinearOverBase p
  exact Langlands.Rationalization.inclusionLiftIso (lieFunctor S)

/-- A rational isomorphism gives an actual isomorphism of relative Lie sheaves. -/
def lieIso0 {A B : AbelianScheme S}
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B) :
    A.Lie ≅ B.Lie :=
  (rationalLieFunctor p).mapIso e

@[simp]
theorem lieIso0_hom {A B : AbelianScheme S}
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B) :
    (lieIso0 p e).hom = lieMap0 p e.hom := rfl

@[simp]
theorem lieIso0_inv {A B : AbelianScheme S}
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B) :
    (lieIso0 p e).inv = lieMap0 p e.inv := rfl

@[simp]
theorem lieIso0_refl (A : AbelianScheme S) :
    lieIso0 p (Iso.refl (Langlands.Rationalization.of A)) = Iso.refl A.Lie :=
  (rationalLieFunctor p).mapIso_refl _

@[simp]
theorem lieIso0_symm {A B : AbelianScheme S}
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B) :
    lieIso0 p e.symm = (lieIso0 p e).symm := rfl

theorem lieIso0_trans {A B C : AbelianScheme S}
    (e : Langlands.Rationalization.of A ≅ Langlands.Rationalization.of B)
    (f : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of C) :
    lieIso0 p (e ≪≫ f) = lieIso0 p e ≪≫ lieIso0 p f :=
  (rationalLieFunctor p).mapIso_trans e f

/-- Compose an actual rational endomorphism action with its constructed Lie action. -/
def lieRationalOrderAction (A : AbelianScheme S) {O : Type v} [Ring O]
    (α : O →+* End0 A) : O →+* CategoryTheory.End A.Lie := by
  letI := Langlands.Scheme.Modules.rationalLinearOverBase p
  exact (lieEnd0Action p A).toRingHom.comp α

@[simp]
theorem lieRationalOrderAction_apply (A : AbelianScheme S) {O : Type v} [Ring O]
    (α : O →+* End0 A) (a : O) :
    lieRationalOrderAction p A α a = lieMap0 p (α a) := rfl

/-- The rational Lie action specializes to the integral differential action. -/
theorem lieRationalOrderAction_integral (A : AbelianScheme S) {O : Type v} [Ring O]
    (α : O →+* CategoryTheory.End A) :
    lieRationalOrderAction p A ((endToEnd0 A).comp α) =
      (lieEndAction A).comp α := by
  ext a
  exact lieEnd0Action_ofEnd p A (α a)

/-- Rational intertwining implies intertwining by the actual Lie differential. -/
theorem lieMap0_intertwines {A B : AbelianScheme S} {O : Type v} [Ring O]
    (α : O →+* End0 A) (β : O →+* End0 B) (f : Hom0 A B)
    (hf : ∀ a, comp0 A A B (α a) f = comp0 A B B f (β a)) (a : O) :
    lieRationalOrderAction p A α a ≫ lieMap0 p f =
      lieMap0 p f ≫ lieRationalOrderAction p B β a := by
  have h := congrArg (lieMap0 p) (hf a)
  simpa only [lieMap0_comp, lieRationalOrderAction_apply] using h

end Langlands.AbelianScheme
