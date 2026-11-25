/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived

/-!
# Right derived functors using arbitrary K-injective resolutions

Source: blueprint `def-sfb-right-derived-functor`, order 1609; Stacks Project,
Derived Categories, Tags 070K and 070Y (blueprint: def-sfb-right-derived-functor).

The upstream `Functor.rightDerivedFunctor` requires monomorphic resolutions. Here the
hypothesis is precisely that of Tag 070K. We choose a universal pair supplied by
`exists_rightDerived_of_enough_isKInjective`; its universal property determines it up to
unique isomorphism compatible with its unit.
-/

@[expose] public section

set_option autoImplicit false

universe wC wD vC vD uC uD

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [Abelian C] [Abelian D] [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]
  (F : C ⥤ D) [F.Additive]
  (h : ∀ K : CochainComplex C ℤ,
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

/-- The functor of the universal right-derived pair. Source: blueprint order 1609,
Stacks Tags 070K and 070Y (blueprint: def-sfb-right-derived-functor).
The pair is determined up to unique isomorphism by its universal property. -/
noncomputable def rightDerivedFunctorOfQuasiIsoResolutions :
    DerivedCategory C ⥤ DerivedCategory D :=
  Classical.choose (exists_rightDerived_of_enough_isKInjective h
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh))

/-- The unit of the chosen universal pair. Source: blueprint order 1609,
Stacks Tags 070K and 070Y (blueprint: def-sfb-right-derived-functor). -/
noncomputable def rightDerivedFunctorOfQuasiIsoResolutionsUnit :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h :=
  Classical.choose (Classical.choose_spec (exists_rightDerived_of_enough_isKInjective h
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)))

/-- Universal property of the pair, for every functor G. Source: blueprint order 1609,
Stacks Tags 070K and 070Y (blueprint: def-sfb-right-derived-functor).

Proof plan:
1. Additivity of F preserves zero maps, sums, negatives, shifts and the cone differential,
   hence its homotopy-category functor is triangulated; Qh is triangulated too
   (lem-pur-homotopy-category-triangulated, def-weil-abstract-derived-category).
2. Apply lem-weil-pbc-kinjective-total-derived to this composite and h. The definitions
   choose its universal pair; its bijection on natural transformations is the assertion.
3. That lemma constructs maps by the Hom bijection into K-injectives, so naturality of
   the unit and uniqueness of the lifts give precisely this factorization map. -/
theorem rightDerivedFunctorOfQuasiIsoResolutions_universal
    (G : DerivedCategory C ⥤ DerivedCategory D) :
    Function.Bijective
      (fun β : F.rightDerivedFunctorOfQuasiIsoResolutions h ⟶ G ↦
        F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h ≫
          Functor.whiskerLeft DerivedCategory.Qh β) := by
  exact (Classical.choose_spec (Classical.choose_spec
    (exists_rightDerived_of_enough_isKInjective h
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)))).1 G

/-- Uniqueness of the universal pair, including compatibility with its unit.
Source: blueprint order 1609, Stacks Tag 070K
(blueprint: def-sfb-right-derived-functor).

Proof plan: use the two universal bijections to obtain comparison transformations in
both directions preserving the units. Their composites preserve the units, so injectivity
makes them identities. The bijection also gives uniqueness of the resulting isomorphism,
as in step 2 of the node's proof. -/
theorem rightDerivedFunctorOfQuasiIsoResolutions_unique
    (G : DerivedCategory C ⥤ DerivedCategory D)
    (θ : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ G)
    (hθ : ∀ H : DerivedCategory C ⥤ DerivedCategory D,
      Function.Bijective (fun β : G ⟶ H ↦ θ ≫ Functor.whiskerLeft DerivedCategory.Qh β)) :
    ∃! e : F.rightDerivedFunctorOfQuasiIsoResolutions h ≅ G,
      F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h ≫
        Functor.whiskerLeft DerivedCategory.Qh e.hom = θ := by
  obtain ⟨a, ha⟩ := (F.rightDerivedFunctorOfQuasiIsoResolutions_universal h G).surjective θ
  obtain ⟨b, hb⟩ := (hθ (F.rightDerivedFunctorOfQuasiIsoResolutions h)).surjective
    (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h)
  dsimp only at ha hb
  have hab : a ≫ b = 𝟙 _ := by
    apply (F.rightDerivedFunctorOfQuasiIsoResolutions_universal h _).injective
    dsimp only
    rw [Functor.whiskerLeft_comp, ← Category.assoc, ha, hb]
    simp
  have hba : b ≫ a = 𝟙 _ := by
    apply (hθ G).injective
    dsimp only
    rw [Functor.whiskerLeft_comp, ← Category.assoc, hb, ha]
    simp
  refine ⟨⟨a, b, hab, hba⟩, ha, ?_⟩
  intro e he
  apply Iso.ext
  exact (F.rightDerivedFunctorOfQuasiIsoResolutions_universal h G).injective
    (he.trans ha.symm)

/-- The unit is invertible on every K-injective complex. Source: blueprint order 1609,
Stacks Tags 070K and 070Y (blueprint: def-sfb-right-derived-functor).

Proof plan: step 1 of the node's proof verifies exactness of the degreewise composite.
Step 2 applies lem-weil-pbc-kinjective-total-derived, whose final clause gives this
invertibility for the chosen pair: a quasi-isomorphism between K-injectives is a homotopy
equivalence and the composite functor therefore sends it to an isomorphism. -/
theorem rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    IsIso ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) := by
  exact (Classical.choose_spec (Classical.choose_spec
    (exists_rightDerived_of_enough_isKInjective h
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)))).2 I inferInstance

/-- The canonical comparison for any resolution s, without a monomorphism assumption.
Source: blueprint order 1609, Stacks Tags 070K and 070Y
(blueprint: def-sfb-right-derived-functor).
It is RF(Qs) followed by the inverse unit at I, transported between Q and quotient ⋙ Qh,
as in step 3 of the node's proof. -/
noncomputable def rightDerivedFunctorOfQuasiIsoResolutionsObjIso
    {K I : CochainComplex C ℤ} [I.IsKInjective] (s : K ⟶ I) [QuasiIso s] :
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  letI := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  (F.rightDerivedFunctorOfQuasiIsoResolutions h).mapIso (asIso (DerivedCategory.Q.map s)) ≪≫
    (F.rightDerivedFunctorOfQuasiIsoResolutions h).mapIso
      ((DerivedCategory.quotientCompQhIso C).app I).symm ≪≫
    (asIso ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))).symm ≪≫
    (DerivedCategory.quotientCompQhIso D).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)

end CategoryTheory.Functor
