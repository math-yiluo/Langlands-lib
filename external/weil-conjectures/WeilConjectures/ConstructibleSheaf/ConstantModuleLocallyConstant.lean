/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Topology.LocallyConstant.Algebra
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf

/-!
# Locally constant functions with module coefficients on the small etale site

Source: Stacks Project, Tags 0A3R, 04TR and 04TS.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.Etale

/-- The presheaf of locally constant functions with values in a module. -/
noncomputable def locallyConstantModulePresheaf (X : Scheme.{u})
    (R : Type (u + 1)) [Ring R] (M : ModuleCat.{u + 1} R) :
    X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R where
  obj W := ModuleCat.of R (LocallyConstant W.unop.left M)
  map f := ModuleCat.ofHom (LocallyConstant.comapₗ R
    ⟨f.unop.left, f.unop.left.continuous⟩)
  map_id W := by ext s x; rfl
  map_comp f g := by ext s x; rfl

/-- The locally constant presheaf is functorial in the coefficient module. -/
noncomputable def locallyConstantModulePresheafFunctor (X : Scheme.{u})
    (R : Type (u + 1)) [Ring R] :
    ModuleCat.{u + 1} R ⥤ (X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} R) where
  obj := locallyConstantModulePresheaf X R
  map f :=
    { app W := ModuleCat.ofHom (LocallyConstant.mapₗ R f.hom)
      naturality W W' g := by ext s; rfl }
  map_id M := by ext W s; rfl
  map_comp f g := by ext W s; rfl

private theorem locallyConstantModulePresheaf_isSheaf (X : Scheme.{u})
    (R : Type (u + 1)) [Ring R] (M : ModuleCat.{u + 1} R) :
    Presheaf.IsSheaf X.smallEtaleTopology (locallyConstantModulePresheaf X R M) := by
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let e : locallyConstantModulePresheaf X R M ⋙ CategoryTheory.forget (ModuleCat.{u + 1} R) ≅
      (continuousMapSheaf X M).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1} :=
    NatIso.ofComponents (fun W ↦ equivEquivIso
      { toFun := fun s ↦ s.toContinuousMap
        invFun := fun t ↦
          let t₀ : C(W.unop.left, M) := t
          ⟨t₀, (IsLocallyConstant.iff_continuous _).2 t₀.continuous⟩
        left_inv := fun s ↦ rfl
        right_inv := fun t ↦ rfl }) (by intros; rfl)
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} R) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  have : ReflectsLimitsOfSize.{u, u + 1} (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget (ModuleCat.{u + 1} R))
  rw [Presheaf.isSheaf_of_iso_iff e]
  exact ((sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
    (continuousMapSheaf X M)).property

private noncomputable def constToLocallyConstant (X : Scheme.{u})
    (R : Type (u + 1)) [Ring R] (M : ModuleCat.{u + 1} R) :
    (Functor.const X.Etaleᵒᵖ).obj M ⟶ locallyConstantModulePresheaf X R M where
  app W := ModuleCat.ofHom
    { toFun := LocallyConstant.const W.unop.left
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  naturality _ _ _ := rfl

private theorem constToLocallyConstant_surjective (X : Scheme.{u})
    (R : Type (u + 1)) [Ring R] (M : ModuleCat.{u + 1} R) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (constToLocallyConstant X R M) where
  imageSieve_mem {U} s₀ := by
    let : TopologicalSpace M := ⊥
    let : DiscreteTopology M := ⟨rfl⟩
    let s : C(U.left, M) := s₀.toContinuousMap
    let V (m : M) : X.Etale := Etale.mk ((U.left.fiberOpens s m).ι ≫ U.hom)
    let ι (m : M) : V m ⟶ U := MorphismProperty.Over.homMk (U.left.fiberOpens s m).ι rfl
    refine X.smallEtaleTopology.superset_covering ?_
      ((ofArrows_mem_smallEtaleTopology_iff ι).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨m⟩
      refine ⟨m, LocallyConstant.ext fun x ↦ ?_⟩
      exact x.2.symm
    · refine Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨s x, ⟨x, rfl⟩, ?_⟩
      exact Scheme.Opens.ι_apply _ _

private theorem constToLocallyConstant_injective (X : Scheme.{u})
    (R : Type (u + 1)) [Ring R] (M : ModuleCat.{u + 1} R) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (constToLocallyConstant X R M) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact X.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
        (X.smallEtaleTopology.top_mem _)
    · have : IsEmpty U.unop.left := ⟨fun x ↦ hab (congr_arg
        (fun f : LocallyConstant U.unop.left M ↦ f x) h)⟩
      refine X.smallEtaleTopology.superset_covering ?_
        ((ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := U.unop)
          (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
      rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact i.elim

private noncomputable def constantToLocallyConstantSheaf (X : Scheme.{u})
    (R : Type (u + 1)) [Ring R] (M : ModuleCat.{u + 1} R) :
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ⟶
      ⟨locallyConstantModulePresheaf X R M,
        locallyConstantModulePresheaf_isSheaf X R M⟩ :=
  ⟨sheafifyLift X.smallEtaleTopology (constToLocallyConstant X R M)
    (locallyConstantModulePresheaf_isSheaf X R M)⟩

private theorem constantToLocallyConstantSheaf_isIso (X : Scheme.{u})
    (R : Type (u + 1)) [Ring R] (M : ModuleCat.{u + 1} R) :
    IsIso (constantToLocallyConstantSheaf X R M) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have := constToLocallyConstant_injective X R M
  have := constToLocallyConstant_surjective X R M
  refine (Sheaf.isLocallyBijective_iff_isIso (constantToLocallyConstantSheaf X R M)).1
    ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify X.smallEtaleTopology _)]
    change Presheaf.IsLocallyInjective _ (_ ≫ sheafifyLift _ _ _)
    rw [toSheafify_sheafifyLift]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify X.smallEtaleTopology _)]
    change Presheaf.IsLocallySurjective _ (_ ≫ sheafifyLift _ _ _)
    rw [toSheafify_sheafifyLift]
    infer_instance

/-- Locally constant module functions give the constant module sheaf, naturally
in the coefficient module.
Source: Stacks Project, Tags 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-constant-module-locally-constant)

Proof: Give the coefficient module the discrete topology. Locally constant
functions are the same as continuous functions. Compatible continuous functions
on an etale covering glue uniquely because the covering is jointly surjective
and its maps are open; pointwise module operations commute with gluing. The map
from the constant presheaf sends a coefficient to its constant function. It is
locally surjective: restrict a locally constant function to each of its open
fibers, which are etale objects and cover the source. It is locally injective:
two constant functions agreeing on a nonempty object have equal coefficients;
on an empty object the empty family is a covering. Thus the map becomes an
isomorphism after sheafification. The comparison commutes with every linear map,
since constant functions, restriction, and sheafification are natural in the
coefficient module. This also handles the zero module and the empty scheme. -/
theorem locallyConstantModulePresheafFunctor_iso_constantSheaf
    (X : Scheme.{u}) (R : Type (u + 1)) [Ring R] :
    Nonempty (locallyConstantModulePresheafFunctor X R ≅
      constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
        sheafToPresheaf X.smallEtaleTopology _) := by
  let e (M : ModuleCat.{u + 1} R) :
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M ≅
        ⟨locallyConstantModulePresheaf X R M,
          locallyConstantModulePresheaf_isSheaf X R M⟩ := by
    have := constantToLocallyConstantSheaf_isIso X R M
    exact asIso (constantToLocallyConstantSheaf X R M)
  let i : constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⋙
      sheafToPresheaf X.smallEtaleTopology _ ≅
      locallyConstantModulePresheafFunctor X R :=
    NatIso.ofComponents (fun M ↦
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).mapIso (e M)) (by
        intro M M' f
        apply sheafify_hom_ext _ _ _ (locallyConstantModulePresheaf_isSheaf X R M')
        change toSheafify _ _ ≫ (sheafifyMap _ _ ≫ sheafifyLift _ _ _) =
          toSheafify _ _ ≫ (sheafifyLift _ _ _ ≫ _)
        rw [← Category.assoc, ← toSheafify_naturality, Category.assoc,
          toSheafify_sheafifyLift, ← Category.assoc, toSheafify_sheafifyLift]
        ext W m
        rfl)
  exact ⟨i.symm⟩

end AlgebraicGeometry.Scheme.Etale
