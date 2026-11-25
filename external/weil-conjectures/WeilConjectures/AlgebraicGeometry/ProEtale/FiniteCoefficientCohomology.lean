/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ContinuousSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologicalDimension
public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections

/-!
# Pro-étale cohomology with finite discrete coefficients

Let `A` be a finite discrete abelian group and `S` a scheme. The pro-étale sheaf
`continuousSheaf S A : U ↦ C(U, A)` is the constant sheaf with value `A`
(`AlgebraicGeometry.ProEtale.constantSheafIsoContinuousSheaf`), and the comparison pullback `ν^*`
sends the constant étale sheaf to the constant pro-étale sheaf. Since `RΓ(S_proét, ν^* M) ≅
RΓ(S_ét, M)`, the pro-étale cohomology of `continuousSheaf S A` is the étale cohomology of the
constant sheaf `A`, a torsion sheaf. Hence, for `S` of finite type and dimension at most `d`
over a separably closed field, it vanishes in degrees `> 2d`
(`AlgebraicGeometry.ProEtale.subsingleton_H_continuousSheaf_of_two_mul_lt`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (S : Scheme.{u}) (A : Type) [TopologicalSpace A] [AddCommGroup A]
  [IsTopologicalAddGroup A]

/-- The constant functions, as a map from the constant presheaf with value `A` to the sheaf
`U ↦ C(U, A)` on the small pro-étale site. -/
noncomputable def constToContinuousSheaf :
    (Functor.const S.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶
      (continuousSheaf S A).obj where
  app _ := AddCommGrpCat.ofHom
    { toFun a := ULift.up (ContinuousMap.const _ a.down)
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ _ := rfl

section Discrete

variable [DiscreteTopology A]

/-- A continuous function to a discrete group is locally constant: it is constant on the open
fibres, which form a Zariski cover. -/
instance : Presheaf.IsLocallySurjective (ProEt.topology S) (constToContinuousSheaf S A) where
  imageSieve_mem {U} s₀ := by
    let s : C(U.left, A) := s₀.down
    refine ProEt.mem_topology_of_openImmersion _ (fun x : U.left ↦ (U.left.fiberOpens s (s x)).ι)
      (fun x ↦ ⟨x, ⟨x, rfl⟩, Scheme.Opens.ι_apply _ _⟩) fun x ↦ ⟨ULift.up (s x), ?_⟩
    exact congrArg ULift.up (ContinuousMap.ext fun y ↦ y.2.symm)

/-- Two constant sections agreeing on `U` agree locally: either they are equal, or `U` is empty
and is covered by the empty sieve. -/
instance : Presheaf.IsLocallyInjective (ProEt.topology S) (constToContinuousSheaf S A) where
  equalizerSieve_mem {U} a b h := by
    by_cases hab : a = b
    · subst hab
      exact (ProEt.topology S).superset_covering (fun _ _ _ ↦ rfl)
        ((ProEt.topology S).top_mem _)
    · have : IsEmpty U.unop.left := ⟨fun x ↦ hab (ULift.ext
        (congr_arg (fun f : ULift.{u + 1} C(U.unop.left, A) ↦ f.down x) h))⟩
      exact (ProEt.topology S).superset_covering bot_le (ProEt.bot_mem_topology _)

/-- The map from the constant sheaf with value `A` to the sheaf `U ↦ C(U, A)` on the small
pro-étale site, sending the constant section `a` to the constant function `a`. -/
noncomputable def constantSheafToContinuousSheaf :
    (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ continuousSheaf S A :=
  ((sheafificationAdjunction (ProEt.topology S) AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (constToContinuousSheaf S A)

omit [DiscreteTopology A] in
lemma toSheafify_constantSheafToContinuousSheaf :
    toSheafify (ProEt.topology S) _ ≫ (constantSheafToContinuousSheaf S A).hom =
      constToContinuousSheaf S A := by
  have h := ((sheafificationAdjunction (ProEt.topology S) AddCommGrpCat.{u + 1}).homEquiv
    ((Functor.const S.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
      (continuousSheaf S A)).apply_symm_apply (constToContinuousSheaf S A)
  rw [Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app] at h
  exact h

instance : IsIso (constantSheafToContinuousSheaf S A) := by
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : (ProEt.topology S).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  have h := toSheafify_constantSheafToContinuousSheaf S A
  refine (Sheaf.isLocallyBijective_iff_isIso (constantSheafToContinuousSheaf S A)).1 ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective _ _
    rw [← Presheaf.comp_isLocallyInjective_iff _ (toSheafify (ProEt.topology S) _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective _ _
    rw [← Presheaf.comp_isLocallySurjective_iff _ (toSheafify (ProEt.topology S) _), h]
    infer_instance

/-- **The constant pro-étale sheaf is the sheaf of continuous functions.** For a discrete
abelian group `A`, the constant sheaf with value `A` on the small pro-étale site of `S` is
isomorphic to `continuousSheaf S A : U ↦ C(U, A)`, by the map sending the constant section `a`
to the constant function `a`. -/
noncomputable def constantSheafIsoContinuousSheaf :
    (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)) ≅ continuousSheaf S A :=
  asIso (constantSheafToContinuousSheaf S A)

end Discrete

/-- The comparison pullback `ν^*` sends constant étale sheaves of abelian groups to constant
pro-étale sheaves: `constantSheaf ⋙ ν^*` and `constantSheaf` are both left adjoint to the global
sections, as the inclusion of sites sends the terminal object of `S_ét` to the terminal object of
`S_proét`. -/
noncomputable def comparisonUpperStarConstantSheafIsoAddCommGrpCat :
    constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ ν^*(S)[AddCommGrpCat.{u + 1}] ≅
      constantSheaf (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} :=
  (((constantSheafAdj S.smallEtaleTopology AddCommGrpCat.{u + 1} (Etale.isTerminalMkId S)).comp
      (comparisonAdjunction AddCommGrpCat.{u + 1} S)).ofNatIsoRight
    ((toProEt S).sheafPushforwardContinuousCompSheafSectionsObjIso AddCommGrpCat.{u + 1}
      S.smallEtaleTopology (Scheme.ProEt.topology S)
        (op (Scheme.Etale.mk (𝟙 S))))).leftAdjointUniq
    (constantSheafAdj (Scheme.ProEt.topology S) AddCommGrpCat.{u + 1} (ProEt.isTerminalMkId S))

/-- **Pro-étale cohomology with finite coefficients in high degrees.** Let `S` be a scheme of
finite type and of dimension at most `d` over a separably closed field `K`, and `A` a finite
discrete abelian group. Then `Hᵠ(S_proét, A) = 0` for `q > 2d`. -/
theorem subsingleton_H_continuousSheaf_of_two_mul_lt
    {K : Type u} [Field K] [IsSepClosed K] {S : Scheme.{u}} (a : S ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a] (d : ℕ)
    (hS : topologicalKrullDim S ≤ (d : WithBot ℕ∞))
    (A : Type) [TopologicalSpace A] [DiscreteTopology A] [AddCommGroup A] [Finite A]
    (q : ℕ) (hq : 2 * d < q) :
    Subsingleton (Sheaf.H (ProEtale.continuousSheaf S A) q) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  let M := AddCommGrpCat.of (ULift.{u + 1} A)
  let Cet := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  let Cproet := (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj M
  -- the constant étale sheaf `A` is torsion, so its cohomology vanishes above `2d`
  have hC : Subsingleton (Sheaf.H Cet (q + 1)) := by
    have := Scheme.subsingleton_H_of_two_mul_lt_of_isSepClosed d a hS
      (Etale.continuousMapSheaf S (ULift.{u + 1} A))
      (Sheaf.IsTorsion.of_forall_isAddTorsion fun U f ↦ isOfFinAddOrder_iff_nsmul_eq_zero.2
        ⟨Nat.card (ULift.{u + 1} A), Nat.card_pos, ContinuousMap.ext fun x ↦ ?_⟩) (q + 1) hq
    · exact ((Sheaf.functorH S.smallEtaleTopology (q + 1)).mapIso
        (Etale.constantSheafIsoContinuousMapSheaf S (ULift.{u + 1} A))).addCommGroupIsoToAddEquiv
        |>.toEquiv.subsingleton_congr.2 this
    · exact card_nsmul_eq_zero'
  obtain ⟨e₁⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    (ProEt.topology S) _ (ProEt.isTerminalMkId S) Cproet q
  obtain ⟨e₂⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation_succ
    S.smallEtaleTopology _ (Etale.isTerminalMkId S) Cet q
  let e₃ : ((globalSectionsFunctor AddCommGrpCat.{u + 1} S).rightDerived (q + 1)).obj Cproet ≅
      ((Etale.sectionsFunctor AddCommGrpCat.{u + 1} S).rightDerived (q + 1)).obj Cet :=
    (((globalSectionsFunctor _ S).rightDerived (q + 1)).mapIso
      ((comparisonUpperStarConstantSheafIsoAddCommGrpCat S).app M)).symm ≪≫
      rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso _ S Cet (q + 1)
  let e₄ := (Sheaf.functorH (ProEt.topology S) (q + 1)).mapIso
    (constantSheafIsoContinuousSheaf S A)
  exact (e₄.addCommGroupIsoToAddEquiv.symm.trans (e₁.trans
    (e₃.addCommGroupIsoToAddEquiv.trans e₂.symm))).toEquiv.subsingleton

end AlgebraicGeometry.ProEtale
