/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# The pro-étale sheaf of continuous maps to a topological abelian group

For a topological abelian group `A` and a scheme `S`, the presheaf `U ↦ C(U, A)` on the small
pro-étale site of `S` is a sheaf of abelian groups (Bhatt–Scholze, §4.2.12), since
`U ↦ C(U, A)` is an fpqc sheaf on schemes
(`AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheafAb`).
For `A` discrete this is the constant sheaf `A_S`; for `A = ℤ_ℓ` it is the sheaf `ℤ_ℓ,S`,
the limit of the constant sheaves `ℤ/ℓⁿ`.

## Main definitions

- `AlgebraicGeometry.ProEtale.continuousSheaf S A`: the sheaf `U ↦ C(U, A)` of abelian groups on
  `S_proét`, lifted to the universe `u + 1` of the sheaf categories on `S_proét`.
- `AlgebraicGeometry.ProEtale.continuousSheafMap`: the morphism induced by a continuous
  homomorphism `A →+ B`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (S : Scheme.{u}) (A : Type) [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A]

/-- The presheaf of abelian groups `U ↦ C(U, A)` on all schemes, lifted to `Type (u + 1)`. -/
noncomputable abbrev continuousMapPresheafAbULift : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  continuousMapPresheafAb.{0, u} A ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}

lemma isSheaf_proetaleTopology_continuousMapPresheafAbULift :
    Presheaf.IsSheaf Scheme.proetaleTopology (continuousMapPresheafAbULift.{u} A) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _
    (Presheaf.IsSheaf.of_le Scheme.proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheafAb A))

/-- The sheaf `U ↦ C(U, A)` of continuous maps to the topological abelian group `A` on the small
pro-étale site of `S`, with values in abelian groups of the universe `u + 1`. -/
noncomputable def continuousSheaf : Sheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} :=
  ((Scheme.ProEt.forget S ⋙ Over.forget _).sheafPushforwardContinuous _ _
    Scheme.proetaleTopology).obj
    ⟨continuousMapPresheafAbULift A, isSheaf_proetaleTopology_continuousMapPresheafAbULift A⟩

/-- The sections of `continuousSheaf S A` over `U` are the continuous maps `U → A`. -/
lemma continuousSheaf_obj_obj (U : S.ProEt) :
    (continuousSheaf S A).obj.obj (op U) =
      AddCommGrpCat.of (ULift.{u + 1} C(U.left, A)) :=
  rfl


variable {A} {B : Type} [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]

/-- The morphism of presheaves `C(-, A) ⟶ C(-, B)` given by postcomposition with a continuous
homomorphism. -/
noncomputable def continuousMapPresheafAbULiftMap (φ : ContinuousAddMonoidHom A B) :
    continuousMapPresheafAbULift.{u} A ⟶ continuousMapPresheafAbULift.{u} B where
  app U := AddCommGrpCat.ofHom
    { toFun f := ULift.up ((φ : C(A, B)).comp f.down)
      map_zero' := by ext; simp
      map_add' f g := by
        let f' : C(U.unop, A) := f.down
        let g' : C(U.unop, A) := g.down
        change ULift.up ((φ : C(A, B)).comp (f' + g')) =
          ULift.up ((φ : C(A, B)).comp f' + (φ : C(A, B)).comp g')
        congr 1
        ext x
        exact map_add φ (f' x) (g' x) }
  naturality _ _ _ := rfl

/-- The morphism of sheaves `C(-, A) ⟶ C(-, B)` on `S_proét` given by postcomposition with a
continuous homomorphism `φ : A → B`. -/
noncomputable def continuousSheafMap (φ : ContinuousAddMonoidHom A B) :
    continuousSheaf S A ⟶ continuousSheaf S B :=
  ((Scheme.ProEt.forget S ⋙ Over.forget _).sheafPushforwardContinuous _ _
    Scheme.proetaleTopology).map ⟨continuousMapPresheafAbULiftMap φ⟩

lemma continuousSheafMap_app_apply (φ : ContinuousAddMonoidHom A B) (U : S.ProEt)
    (f : ULift.{u + 1} C(U.left, A)) :
    (continuousSheafMap S φ).hom.app (op U) f = ULift.up ((φ : C(A, B)).comp f.down) :=
  rfl


lemma continuousSheafMap_id :
    continuousSheafMap S (ContinuousAddMonoidHom.id A) = 𝟙 _ :=
  rfl

lemma continuousSheafMap_comp {C : Type} [TopologicalSpace C] [AddCommGroup C]
    [IsTopologicalAddGroup C] (φ : ContinuousAddMonoidHom A B) (ψ : ContinuousAddMonoidHom B C) :
    continuousSheafMap S (ψ.comp φ) = continuousSheafMap S φ ≫ continuousSheafMap S ψ :=
  rfl

end AlgebraicGeometry.ProEtale
