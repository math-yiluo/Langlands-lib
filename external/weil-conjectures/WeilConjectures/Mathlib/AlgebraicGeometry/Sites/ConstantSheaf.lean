/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# The constant sheaf on the small étale site as a sheaf of continuous maps

For a topological abelian group `A`, the presheaf `U ↦ C(U, A)` on the small étale site of a
scheme `X` is a sheaf, being the restriction of the fpqc sheaf
`AlgebraicGeometry.continuousMapPresheafAb`. When `A` is discrete, it is the constant sheaf with
value `A`: a section of the constant sheaf over `U` is a locally constant function on `U`.

## Main definitions

- `AlgebraicGeometry.Scheme.Etale.continuousMapSheaf`: the sheaf `U ↦ C(U, A)` on the small
  étale site.
- `AlgebraicGeometry.Scheme.Etale.constantSheafIsoContinuousMapSheaf`: for discrete `A`, the
  isomorphism between the constant sheaf with value `A` and `U ↦ C(U, A)`, which sends the
  constant section `a` to the constant function `a`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (A : Type (u + 1)) [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A]

/-- The forgetful functor from the small étale site of `X` to schemes is continuous for the
étale topology and the pro-étale topology, through the small pro-étale site. -/
instance : (toProEt X ⋙ ProEt.forget X ⋙ Over.forget X).IsContinuous (smallEtaleTopology X)
    proetaleTopology :=
  Functor.isContinuous_comp _ _ _ (ProEt.topology X) _

/-- The sheaf `U ↦ C(U, A)` of continuous functions with values in a topological abelian group
`A`, on the small étale site of `X`. It is the restriction of the fpqc sheaf
`AlgebraicGeometry.continuousMapPresheafAb`. -/
noncomputable def Etale.continuousMapSheaf : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ((toProEt X ⋙ ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous _ _
    proetaleTopology).obj
    ⟨continuousMapPresheafAb.{u + 1, u} A,
      .of_le proetaleTopology_le_fpqcTopology (isSheaf_fpqcTopology_continuousMapPresheafAb A)⟩

lemma Etale.continuousMapSheaf_obj_obj (U : X.Etale) :
    (Etale.continuousMapSheaf X A).obj.obj (op U) = AddCommGrpCat.of C(U.left, A) :=
  rfl

lemma Etale.continuousMapSheaf_obj_map_apply {U V : X.Etale} (f : U ⟶ V)
    (s : C(V.left, A)) :
    (Etale.continuousMapSheaf X A).obj.map f.op s = s.comp f.left.base.hom :=
  rfl


section Discrete

variable [DiscreteTopology A]

/-- The constant functions, as a map from the constant presheaf with value `A` to the sheaf of
continuous functions `U ↦ C(U, A)`. -/
noncomputable def Etale.constToContinuousMap :
    (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of A) ⟶ (Etale.continuousMapSheaf X A).obj where
  app _ := AddCommGrpCat.ofHom
    { toFun a := ContinuousMap.const _ a
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

omit [DiscreteTopology A] in
lemma Etale.constToContinuousMap_app_apply (U : X.Etaleᵒᵖ) (a : A) :
    (Etale.constToContinuousMap X A).app U a = ContinuousMap.const _ a :=
  rfl


/-- A continuous function to a discrete group is locally constant: it is constant on the open
fibres, which cover. -/
instance : Presheaf.IsLocallySurjective X.smallEtaleTopology (Etale.constToContinuousMap X A) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, A) := s₀
    let V (m : A) : X.Etale := Etale.mk ((U.left.fiberOpens s m).ι ≫ U.hom)
    let ι (m : A) : V m ⟶ U := MorphismProperty.Over.homMk (U.left.fiberOpens s m).ι rfl
    refine X.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨m⟩
      refine ⟨m, ContinuousMap.ext fun x ↦ ?_⟩
      exact x.2.symm
    · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨s x, ⟨x, rfl⟩, ?_⟩
      exact Scheme.Opens.ι_apply _ _

/-- Two constant sections agreeing on `U` agree locally: either they are equal, or `U` is empty
and is covered by the empty family. -/
instance : Presheaf.IsLocallyInjective X.smallEtaleTopology (Etale.constToContinuousMap X A) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact X.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (X.smallEtaleTopology.top_mem _)
    · have : IsEmpty U.unop.left := ⟨fun x ↦ hab (congr_arg (fun f : C(U.unop.left, A) ↦ f x) h)⟩
      refine X.smallEtaleTopology.superset_covering ?_
        ((ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := U.unop)
          (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim

/-- The map from the constant sheaf with value `A` to the sheaf of continuous functions
`U ↦ C(U, A)` sending the constant section `a` to the constant function `a`. -/
noncomputable def Etale.constantSheafToContinuousMapSheaf :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of A) ⟶
      Etale.continuousMapSheaf X A :=
  ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (Etale.constToContinuousMap X A)

omit [DiscreteTopology A] in
lemma Etale.toSheafify_constantSheafToContinuousMapSheaf :
    toSheafify X.smallEtaleTopology _ ≫ (Etale.constantSheafToContinuousMapSheaf X A).hom =
      Etale.constToContinuousMap X A := by
  have h := ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of A))
      (Etale.continuousMapSheaf X A)).apply_symm_apply (Etale.constToContinuousMap X A)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

instance : IsIso (Etale.constantSheafToContinuousMapSheaf X A) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  have h := Etale.toSheafify_constantSheafToContinuousMapSheaf X A
  refine (Sheaf.isLocallyBijective_iff_isIso (Etale.constantSheafToContinuousMapSheaf X A)).1
    ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify X.smallEtaleTopology _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify X.smallEtaleTopology _), h]
    infer_instance

/-- **The constant sheaf is the sheaf of continuous functions.** For a discrete abelian group
`A`, the constant sheaf with value `A` on the small étale site of `X` is isomorphic to the sheaf
`U ↦ C(U, A)` of locally constant functions, by the map sending the constant section `a` to the
constant function `a`. -/
noncomputable def Etale.constantSheafIsoContinuousMapSheaf :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of A) ≅
      Etale.continuousMapSheaf X A :=
  asIso (Etale.constantSheafToContinuousMapSheaf X A)

end Discrete

end AlgebraicGeometry.Scheme
