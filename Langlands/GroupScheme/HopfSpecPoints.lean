import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Points of the spectrum of a Hopf algebra over affine tests

For a commutative Hopf algebra `A` over `R` and an `R`-algebra `Y`, every `R`-algebra map
`A → Y` gives a point of `Spec A` over `Spec Y`, and every such point arises this way. Products
of points correspond to convolution of algebra maps, the identity point to the counit, and
composition with the morphism induced by a Hopf algebra map to precomposition. -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HopfSpecPoints

variable {R : CommRingCat.{u}} {A : CommHopfAlgCat.{u} R} {Y : CommAlgCat.{u} R}

/-- The cogroup object of algebras attached to `A`. -/
abbrev cogroup (A : CommHopfAlgCat.{u} R) : Grp (CommAlgCat.{u} R)ᵒᵖ :=
  ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.obj A).unop

/-- The point of the cogroup of `A` with values in `Y` classified by an algebra map `A → Y`. -/
def cogroupPoint (f : A →ₐ[R] Y) : op Y ⟶ (cogroup A).X :=
  (CommAlgCat.ofHom f).op

@[simp]
theorem cogroupPoint_unop_hom (f : A →ₐ[R] Y) : (cogroupPoint f).unop.hom = f := rfl

theorem cogroupPoint_mul (f g : A →ₐ[R] Y) :
    cogroupPoint f * cogroupPoint g =
      cogroupPoint ((Algebra.TensorProduct.lift f g fun _ _ => .all _ _).comp
        (Bialgebra.comulAlgHom R A)) := by
  rw [CategoryTheory.Hom.mul_def]
  rfl

theorem cogroupPoint_one :
    (1 : op Y ⟶ (cogroup A).X) =
      cogroupPoint ((Algebra.ofId R Y).comp (Bialgebra.counitAlgHom R A)) := by
  rw [CategoryTheory.Hom.one_def]
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  rfl

/-- The point of `Spec A` over `Spec Y` classified by an algebra map `A → Y`. -/
def specPoint (f : A →ₐ[R] Y) : (algSpec R).obj (op Y) ⟶ ((hopfSpec R).obj (op A)).X :=
  (algSpec R).map (cogroupPoint f)

theorem specPoint_injective : Function.Injective (specPoint (A := A) (Y := Y)) := by
  intro f g h
  have h1 := (algSpec R).map_injective h
  exact (cogroupPoint_unop_hom f).symm.trans
    ((congrArg (fun x => x.unop.hom) h1).trans (cogroupPoint_unop_hom g))

theorem exists_specPoint (x : (algSpec R).obj (op Y) ⟶ ((hopfSpec R).obj (op A)).X) :
    ∃ f, specPoint f = x :=
  ⟨((algSpec R).preimage x).unop.hom, (algSpec R).map_preimage x⟩

theorem specPoint_mul (f g : A →ₐ[R] Y) :
    specPoint f * specPoint g = specPoint
      ((Algebra.TensorProduct.lift f g fun _ _ => .all _ _).comp (Bialgebra.comulAlgHom R A)) := by
  unfold specPoint
  rw [← cogroupPoint_mul, Functor.map_mul]
  rfl

theorem specPoint_one :
    (1 : (algSpec R).obj (op Y) ⟶ ((hopfSpec R).obj (op A)).X) =
      specPoint ((Algebra.ofId R Y).comp (Bialgebra.counitAlgHom R A)) := by
  unfold specPoint
  rw [← cogroupPoint_one, Functor.map_one]
  rfl

theorem cogroupPoint_comp_map {B : CommHopfAlgCat.{u} R} (ψ : B ⟶ A) (f : A →ₐ[R] Y) :
    cogroupPoint f ≫ ((commHopfAlgCatEquivCogrpCommAlgCat R).functor.leftOp.map ψ.op).hom.hom =
      cogroupPoint (f.comp (ψ.hom : B →ₐ[R] A)) := by
  apply Quiver.Hom.unop_inj
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro a
  rfl

theorem specPoint_comp_map {B : CommHopfAlgCat.{u} R} (ψ : B ⟶ A) (f : A →ₐ[R] Y) :
    specPoint f ≫ ((hopfSpec R).map ψ.op).hom.hom =
      specPoint (f.comp (ψ.hom : B →ₐ[R] A)) := by
  unfold specPoint
  rw [← cogroupPoint_comp_map, Functor.map_comp]
  rfl

end Langlands.GroupScheme.HopfSpecPoints
