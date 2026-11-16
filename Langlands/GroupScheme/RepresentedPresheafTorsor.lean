import Langlands.GroupScheme.PresheafTorsor
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationZariski
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties

/-! # Actions and gluing for represented torsor presheaves -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.PresheafTorsor

variable {S : Scheme.{u}} {G : GroupScheme S} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)}

namespace Action

variable (A : Action G F) {X : Over S} (R : F.RepresentableBy X)

/-- The action morphism obtained by applying representability to the
universal group point and universal point of the representing scheme. -/
def representedActionHom : G.X ⊗ X ⟶ X :=
  R.homEquiv.symm (A.act (fst G.X X) (R.homEquiv (snd G.X X)))

theorem representedActionHom_eval {Z : Over S} (g : Z ⟶ G.X) (f : Z ⟶ X) :
    R.homEquiv (lift g f ≫ A.representedActionHom R) = A.act g (R.homEquiv f) := by
  rw [R.homEquiv_comp]
  change F.map (lift g f).op
    (R.homEquiv (R.homEquiv.symm (A.act (fst G.X X) (R.homEquiv (snd G.X X))))) = _
  rw [Equiv.apply_symm_apply, A.naturality, lift_fst,
    ← R.homEquiv_comp, lift_snd]

/-- A represented natural action gives the actual categorical group action. -/
@[instance_reducible]
def representedAction : ModObj G.X X :=
  schemeActionOfPointLaws (A.representedActionHom R)
    (fun f => R.homEquiv.injective (by
      rw [A.representedActionHom_eval, A.one_act]))
    (fun g h f => R.homEquiv.injective (by
      rw [A.representedActionHom_eval, A.representedActionHom_eval,
        A.representedActionHom_eval, A.mul_act]))

/-- The representing correspondence is equivariant for the actual action. -/
theorem representedAction_equivariant {Z : Over S} (g : Z ⟶ G.X) (f : Z ⟶ X) :
    letI := A.representedAction R
    R.homEquiv (g • f) = A.act g (R.homEquiv f) :=
  A.representedActionHom_eval R g f

/-- Simple transitivity on all test points is exactly the actual torsor
isomorphism for the representing scheme. -/
theorem representedAction_leftSMul_isIso :
    letI := A.representedAction R
    IsIso (ModObj.leftSMul G.X X) := by
  let := A.representedAction R
  apply ModObj.isIso_leftSMul_iff.mpr
  intro Z f g
  obtain ⟨d, hd, huniq⟩ := A.simplyTransitive (R.homEquiv f) (R.homEquiv g)
  refine ⟨d, R.homEquiv.injective ?_, ?_⟩
  · rw [A.representedAction_equivariant]
    exact hd
  · intro e he
    apply huniq
    rw [← A.representedAction_equivariant, he]

end Action

/-- A smooth affine surjective scheme model of a presheaf. The action is
reconstructed canonically from a supplied natural action on the presheaf. -/
structure SmoothAffineModel (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) where
  scheme : Over S
  represents : F.RepresentableBy scheme
  affine : IsAffineHom scheme.hom
  smooth : Smooth scheme.hom
  surjective : Surjective scheme.hom

namespace SmoothAffineModel

/-- Models of the restricted presheaf on a base open cover glue to a
smooth affine surjective model over the arbitrary base. -/
theorem nonempty_of_openCover
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
    (𝒰 : Scheme.OpenCover.{u} S)
    (d : ∀ i, SmoothAffineModel ((Over.map (𝒰.f i)).op ⋙ F)) :
    Nonempty (SmoothAffineModel F) := by
  let H := fun i => (d i).scheme
  let e := fun i =>
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _)
      (d i).represents
  obtain ⟨V, ⟨eV⟩⟩ := LocalRepresentation.exists_representation_zariski hF 𝒰 H e
  exact ⟨⟨V, (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} _ _).symm eV,
    LocalRepresentation.property_of_local_representations @IsAffineHom V eV 𝒰 H e
      (fun i => (d i).affine),
    LocalRepresentation.property_of_local_representations @Smooth V eV 𝒰 H e
      (fun i => (d i).smooth),
    LocalRepresentation.property_of_local_representations @Surjective V eV 𝒰 H e
      (fun i => (d i).surjective)⟩⟩

/-- Choose the model obtained by gluing supplied open local models. -/
def zariskiGlue
    (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)
    (𝒰 : Scheme.OpenCover.{u} S)
    (d : ∀ i, SmoothAffineModel ((Over.map (𝒰.f i)).op ⋙ F)) :
    SmoothAffineModel F :=
  Classical.choice (nonempty_of_openCover hF 𝒰 d)

end SmoothAffineModel

namespace Action

variable (A : Action G F)

/-- The affine cocycle construction yields a smooth affine model when the
group is smooth and a section exists on the supplied affine etale cover. -/
def affineModel [IsAffine S] [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {U : Over S} [IsAffine U.left] [Etale U.hom] [Surjective U.hom]
    (x : F.obj (op U))
    (hF : ∀ {V W : Over S} (p : V ⟶ W) [Etale p.left] [Surjective p.left],
      Presieve.IsSheafFor F (.singleton p)) :
    SmoothAffineModel F :=
  ⟨A.model x, A.representation x hF, A.model_affineHom x,
    A.model_smooth x, A.model_surjective x⟩

end Action
end Langlands.GroupScheme.PresheafTorsor
