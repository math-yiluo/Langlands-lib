/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology
public import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.MapBijectiveAcyclic
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The comparison map from étale to pro-étale cohomology

For a scheme `S` and an abelian étale sheaf `M`, pulling back along `ν : S_proét ⟶ S_ét` gives
the explicit comparison map `Hⁿ(S_ét, M) ⟶ Hⁿ(S_proét, ν^* M)`
(`AlgebraicGeometry.ProEtale.cohomologyComparison`), an `Ext`-class being pushed forward along
the exact functor `ν^*` and precomposed with `ℤ ≅ ν^* ℤ`. It is bijective in every degree
(`AlgebraicGeometry.ProEtale.bijective_cohomologyComparison`): `ν^*` is fully faithful, and it
sends injective étale sheaves to pro-étale sheaves without higher cohomology since
`RΓ(S_proét, ν^* M) ≅ RΓ(S_ét, M)`. Being given by an exact functor, it is natural in `M`
(`AlgebraicGeometry.ProEtale.cohomologyComparison_map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (S : Scheme.{u})

/-- The identification `ℤ ≅ ν^* ℤ` of the constant pro-étale sheaf `ℤ` with the pullback of the
constant étale sheaf `ℤ`. -/
noncomputable abbrev constantIntIsoComparisonUpperStar :
    (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      (comparisonUpperStar AddCommGrpCat.{u + 1} S).obj
        ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  ((comparisonUpperStarConstantSheafIsoAddCommGrpCat S).app _).symm

/-- The comparison map `Hⁿ(S_ét, M) ⟶ Hⁿ(S_proét, ν^* M)`. -/
noncomputable def cohomologyComparison (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) : Sheaf.H M n →+ Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} S).obj M) n :=
  Sheaf.H.mapFunctor (comparisonUpperStar AddCommGrpCat.{u + 1} S)
    (constantIntIsoComparisonUpperStar S) M n

lemma cohomologyComparison_apply (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Sheaf.H M n) :
    cohomologyComparison S M n x =
      (Ext.mk₀ (constantIntIsoComparisonUpperStar S).hom).comp
        (x.mapExactFunctor (comparisonUpperStar AddCommGrpCat.{u + 1} S)) (zero_add n) :=
  rfl

/-- The comparison map is natural in the sheaf. -/
lemma cohomologyComparison_map {M M' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : M ⟶ M') (n : ℕ) (x : Sheaf.H M n) :
    cohomologyComparison S M' n (Sheaf.H.map φ n x) =
      Sheaf.H.map ((comparisonUpperStar AddCommGrpCat.{u + 1} S).map φ) n
        (cohomologyComparison S M n x) :=
  Sheaf.H.mapFunctor_map _ _ _ φ x

/-- The pullback `ν^* I` of an injective étale sheaf has no higher pro-étale cohomology. -/
theorem subsingleton_H_comparisonUpperStar_obj_of_injective
    (I : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I] (q : ℕ) :
    Subsingleton (Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} S).obj I) (q + 1)) := by
  obtain ⟨e⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    (ProEt.topology S) _ (ProEt.isTerminalMkId S)
    ((comparisonUpperStar AddCommGrpCat.{u + 1} S).obj I) q
  let e' := rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso _ S I (q + 1)
  have : Subsingleton (((Etale.sectionsFunctor AddCommGrpCat.{u + 1} S).rightDerived
      (q + 1)).obj I) :=
    AddCommGrpCat.subsingleton_of_isZero
      ((Etale.sectionsFunctor AddCommGrpCat.{u + 1} S).isZero_rightDerived_obj_injective_succ q I)
  exact (e.trans e'.addCommGroupIsoToAddEquiv).toEquiv.subsingleton

/-- **Étale and pro-étale cohomology.** The comparison map `Hⁿ(S_ét, M) ⟶ Hⁿ(S_proét, ν^* M)`
is bijective. -/
theorem bijective_cohomologyComparison (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n : ℕ) : Function.Bijective (cohomologyComparison S M n) := by
  refine (comparisonUpperStar AddCommGrpCat.{u + 1} S).bijective_mapExtComp
    (constantIntIsoComparisonUpperStar S).hom (fun M ↦ ?_)
    (fun I _ q ↦ subsingleton_H_comparisonUpperStar_obj_of_injective S I q) M n
  have hcomp : ((comparisonUpperStar AddCommGrpCat.{u + 1} S).mapExtComp
      (constantIntIsoComparisonUpperStar S).hom M 0) ∘ Ext.mk₀ = Ext.mk₀ ∘ fun f ↦
        (constantIntIsoComparisonUpperStar S).hom ≫
          (comparisonUpperStar AddCommGrpCat.{u + 1} S).map f := by
    funext f
    rw [Function.comp_apply, Functor.mapExtComp_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
    rfl
  rw [← Function.Bijective.of_comp_iff _ (Ext.mk₀_bijective _ _), hcomp]
  refine (Ext.mk₀_bijective _ _).comp (Function.Bijective.comp
    (g := fun g ↦ (constantIntIsoComparisonUpperStar S).hom ≫ g) ⟨fun a b h ↦ (cancel_epi _).1 h,
      fun g ↦ ⟨(constantIntIsoComparisonUpperStar S).inv ≫ g, by simp⟩⟩
    ((Functor.FullyFaithful.ofFullyFaithful
      (comparisonUpperStar AddCommGrpCat.{u + 1} S)).map_bijective _ _))

/-- The comparison `Hⁿ(S_ét, M) ≃ Hⁿ(S_proét, ν^* M)`, as an additive equivalence. -/
noncomputable def cohomologyComparisonAddEquiv
    (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Sheaf.H M n ≃+ Sheaf.H ((comparisonUpperStar AddCommGrpCat.{u + 1} S).obj M) n :=
  AddEquiv.ofBijective _ (bijective_cohomologyComparison S M n)

@[simp]
lemma cohomologyComparisonAddEquiv_apply
    (M : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) (x : Sheaf.H M n) :
    cohomologyComparisonAddEquiv S M n x = cohomologyComparison S M n x :=
  rfl

end AlgebraicGeometry.ProEtale
