/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
import all WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget

/-!
# Direct sums and finite cohomological dimension

Source: the blueprint of the Weil conjectures, chapter `chap-Smooth-purity`, unit
`proposition-ordinary-external-kunneth--1`, node `proposition-open-direct-image-preserves-finite`,
order 1732; Stacks Project, Etale Cohomology, Tag 0F11 (`lemma-finite-cd-mod-n-direct-sums`)
(blueprint: proposition-open-direct-image-preserves-finite).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If `n ≥ 1` and `f` is quasi-compact, quasi-separated and of finite torsion étale
cohomological dimension, derived direct image on `ZMod n`-module étale sheaves commutes
with every set-indexed coproduct; for every qcqs scheme of finite torsion étale
cohomological dimension, derived global sections has the same property. The coefficient
ring is lifted by the canonical ring equivalence `ULift.ringEquiv` to the universe used
by the existing six-functor and derived-category interfaces.

Source: Stacks Project, Etale Cohomology, Tag 0F11, `lemma-finite-cd-mod-n-direct-sums`,
assertions (1) and (2) (blueprint: proposition-open-direct-image-preserves-finite).

Proof:
1. Put A = Z/nZ. Its module sheaves are torsion. The coefficient-forgetting
   comparison (lem-sbc-higher-direct-image-forget-comparison) identifies their higher
   images with abelian higher images, so definition-cohomological-dimension gives a uniform bound.
   Express sums as filtered colimits of finite partial sums, including the empty partial sum.
   Forgetting preserves these colimits (situation-conventions).
   Apply lemma-weil-pbc-direct-image-filtered-colimit and finite-sum additivity
   (def-sp-left-exact-additive). Exact faithful forgetting reflects the resulting
   canonical higher-image coproduct isomorphisms, also in degree zero.
2. The module-sheaf categories are Grothendieck abelian
   (lem-weil-pbc-module-sheaves-grothendieck-abelian). Choose degreewise injective
   K-injective representatives I_i (lem-pur-kinjective-degreewise-existence).
   Their termwise sum L represents the derived coproduct, with its coprojections
   (lem-kun-grothendieck-derived-coproducts). There is no common lower bound.
3. The degree-zero injective resolution of an injective term makes every positive
   higher direct image zero. Step 1 therefore makes each term of L acyclic.
   Direct image is additive and left exact (def-weil-pbc-direct-image).
   Apply lem-kun-finite-cd-acyclic-complex with the uniform bound to I_i and L.
   Its natural comparison computes derived images and identifies their coprojections.
4. Step 1 in degree zero gives an isomorphism from the termwise sum of f_*I_i to f_*L.
   It commutes with differentials because its restriction to each summand is f_* of
   the coprojection. Localize; lem-kun-grothendieck-derived-coproducts identifies the
   source as the derived coproduct. Naturality from Step 3 identifies the result
   with the canonical comparison, proving (1).
5. For (2), use sections at the terminal object (def-weil-pbc-global-sections-functor),
   which is additive and left exact since kernels are sectionwise.
   The coefficient comparison (lem-weil-pbc-etale-module-cohomology-forget) and
   definition-cohomological-dimension give a uniform bound. On a qcqs scheme, apply
   lemma-finiteness-small-etale-topoi--2 to finite partial sums and use additivity
   on their injective resolutions. This gives the canonical coproduct isomorphisms
   for every higher derived sections functor, including degree zero.
6. Choose representatives I_i and their termwise sum L as in Step 2. Step 5 makes
   the terms of L acyclic for sections. Apply lem-kun-finite-cd-acyclic-complex to
   sections on I_i and L. The degree-zero comparisons commute with differentials
   by checking on each coprojection. They give an isomorphism of section complexes.
   By lem-pc-derived-module-direct-sums its localization is precisely the canonical
   comparison in D(A), proving (2). For the empty family all the complexes and their
   images are zero, so the same construction applies. -/
theorem derivedDirectImage_and_globalSections_preserveCoproducts
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
      f.torsionEtaleCohomologicalDimension < ⊤ →
        ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
          (rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) f)) ∧
      (∀ (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X],
        X.torsionEtaleCohomologicalDimension < ⊤ →
          ∀ I : Type w, PreservesColimitsOfShape (Discrete I)
            (rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) X)) := by
  have : NeZero n := ⟨by omega⟩
  let Λ := ULift.{u + 1} (ZMod n)
  constructor
  · intro X Y f _ _ hf I
    have hdim : HasFiniteCohomologicalDimensionMorphism Λ f := by
      obtain ⟨a, ⟨d, rfl, hd⟩, _⟩ := sInf_lt_iff.mp hf
      refine ⟨d, fun F q hq ↦ ?_⟩
      obtain ⟨q, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) := ⟨q.toNat, by omega⟩
      let S := sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      have hF : (S.obj F).IsTorsion :=
        (Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance
      have hz := hd (S.obj F) hF q hq
      obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso Λ f q F
      have hz' := hz.of_iso e
      let T := sheafCompose Y.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      have hM : IsZero (higherDirectImage Λ f q F) := by
        rw [IsZero.iff_id_eq_zero] at hz' ⊢
        exact T.map_injective (by simpa using hz')
      exact hM.of_iso (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ f F q)
    exact CategoryTheory.preservesCoproducts_of_small _
      (preservesCoproducts_rightDerivedLowerStar Λ f hdim) I
  · intro X _ _ hX I
    have hdim : HasFiniteCohomologicalDimension Λ X := by
      obtain ⟨a, ⟨d, rfl, hd⟩, _⟩ := sInf_lt_iff.mp hX
      refine ⟨d, fun F q hq ↦ ?_⟩
      obtain ⟨q, rfl⟩ : ∃ k : ℕ, q = (k : ℤ) := ⟨q.toNat, by omega⟩
      let S := sheafCompose X.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
      have hF : (S.obj F).IsTorsion :=
        (Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance
      have hz : Subsingleton ((cohomology AddCommGrpCat.{u + 1} X q).obj
          ((DerivedCategory.singleFunctor _ 0).obj (S.obj F))) :=
        hd (S.obj F) hF q (by exact_mod_cast hq)
      obtain ⟨e⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso X Λ q
      have : Subsingleton ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
          ((cohomology (ModuleCat.{u + 1} Λ) X q).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) :=
        @Function.Injective.subsingleton _ _ _
          (e.app F).addCommGroupIsoToAddEquiv.injective hz
      exact ModuleCat.isZero_of_subsingleton _
    exact CategoryTheory.preservesCoproducts_of_small _
      (preservesCoproducts_rightDerivedGlobalSections Λ X hdim) I

end AlgebraicGeometry.Etale
