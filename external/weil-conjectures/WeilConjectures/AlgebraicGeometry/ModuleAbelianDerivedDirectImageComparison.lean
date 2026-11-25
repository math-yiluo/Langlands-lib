/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison


public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
import WeilConjectures.AlgebraicGeometry.ModuleAbelianInverseImageComparison

/-! # Canonical derived direct image comparison for module coefficients

Source: Stacks Project, Tags 03FD and 072W.
(blueprint: lem-weil-pbc-module-abelian-derived-direct-image-comparison)
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true









/-- Direct image commutes definitionally with forgetting coefficients. -/
noncomputable def moduleAbelianLowerStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)_*[ModuleCat.{u + 1} Λ] ⋙ moduleAbelianForget Λ Y ≅
      moduleAbelianForget Λ X ⋙ (f)_*[AddCommGrpCat.{u + 1}] := Iso.refl _

/-- The canonical comparison determined by the units of right derived direct image. -/
noncomputable def moduleAbelianDerivedLowerStarComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R+((f)_*[ModuleCat.{u + 1} Λ]) ⋙ D+(moduleAbelianForget Λ Y) ⟶
      D+(moduleAbelianForget Λ X) ⋙ R+((f)_*[AddCommGrpCat.{u + 1}]) :=
  Functor.rightDerivedFunctorPlusBaseChange (moduleAbelianLowerStarIso Λ f).hom

/-- The Cech criterion on all etale objects gives abelian evaluation acyclicity.
Source: Stacks 03FD, second proof paragraph, via 03FC and 03F9. 
(blueprint: lem-sbc-injective-module-forget-evaluation-acyclic)
-/
private theorem moduleAbelianForget_injective_evaluation_acyclic
    (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G]
    (W : X.Etale) (n : ℕ) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).obj ((moduleAbelianForget Λ X).obj G)) := by
  obtain ⟨e, ⟨eAb⟩⟩ := moduleSheaf_constantRing_equivalence Λ X
  let O := (sheafCompose X.smallEtaleTopology
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ))
  let I : SheafOfModules.{u + 1} O := e.functor.obj G
  have : Injective I := (e.map_injective_iff G).mpr inferInstance
  have htop : X.smallEtaleTopology.toPrecoverage.toGrothendieck =
      X.smallEtaleTopology := by
    apply le_antisymm
    · exact X.smallEtaleTopology.toGrothendieck_toPrecoverage_le
    · intro U S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  let J := X.smallEtaleTopology.toPrecoverage
  have hcech (U : X.Etale) (T : Type (u + 1)) (V : T → X.Etale)
      (f : ∀ t : T, V t ⟶ U) (hf : Sieve.ofArrows V f ∈ X.smallEtaleTopology U)
      (p : ℕ) (hp : 0 < p) :
      IsZero (((cechComplexFunctor fun t : T ↦ Over.mk (f t)).obj
        ((Over.forget U).op ⋙ ((SheafOfModules.toSheaf O).obj I).obj)).homology p) := by
    have hcover : Presieve.ofArrows V f ∈ J U := hf
    obtain ⟨S⟩ := CategoryTheory.SiteCechComplex.exists_of_covering J hcover
    have hzero : IsZero ((S.cohomologyFunctor p).obj I.val.presheaf) := by
      have : Injective I.val := injective_module_sheaf_injective_presheaf O I
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
      change IsZero ((S.complex I.val.presheaf).homology (q + 1))
      apply HomologicalComplex.ExactAt.isZero_homology
      apply (HomologicalComplex.exactAt_iff' (S.complex I.val.presheaf)
        q (q + 1) (q + 2) (by simp) (by simp)).2
      rw [ShortComplex.ab_exact_iff]
      intro c hc
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) (q + 1) ((q + 1) + 1)) c = 0 at hc
      rw [CochainComplex.of_d] at hc
      obtain ⟨b, hb⟩ := injective_presheaf_module_cech_cocycle_lift_max.{u + 1, u, u + 1}
        O.obj I.val V f S q c hc
      refine ⟨b, ?_⟩
      change (CochainComplex.of.d (S.cochains I.val.presheaf)
        (S.differential I.val.presheaf) q (q + 1)) b = c
      rw [CochainComplex.of_d]
      exact hb
    obtain ⟨c⟩ := Scheme.nonempty_etale_siteCech_complex_iso X U V f S I.val.presheaf
    exact hzero.of_iso ((HomologicalComplex.homologyFunctor _ _ p).mapIso c.symm)
  have hvan := Scheme.isZero_rightDerived_etale_of_cech_vanishing X Set.univ
    (fun W _ V f ↦ Sieve.ofArrows V f ∈ X.smallEtaleTopology W)
    ((SheafOfModules.toSheaf O).obj I)
    (fun _ _ _ _ h ↦ h)
    (fun _ _ _ _ _ ↦ ⟨Set.mem_univ _, fun _ ↦ Set.mem_univ _,
      fun _ _ ↦ Set.mem_univ _⟩)
    (fun _ _ T V f hf ↦ ⟨T, V, f, hf, fun t ↦ ⟨t, 𝟙 _, by simp⟩⟩)
    hcech W (Set.mem_univ _) (n + 1) (Nat.zero_lt_succ n)
  exact hvan.of_iso
    (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).mapIso (eAb.app G).symm)

/-- The canonical derived direct-image coefficient comparison is invertible.

Source: Stacks Project, Tag 03FD, second paragraph of its proof, and Tag 072W.
(blueprint: lem-weil-pbc-module-abelian-derived-direct-image-comparison)

Proof: Identify a ModuleCat-valued sheaf with a module over the constant ring
sheaf, preserving its underlying abelian sheaf and injectivity. Tag 03FD gives
vanishing of positive abelian derived evaluation on every etale object for an
injective module sheaf I. By Tag 072W, the higher direct images of I_ab are the
sheafifications of V ↦ H^n(X ×_Y V, I_ab). Each value vanishes for n > 0, so
I_ab is acyclic for f_* on abelian sheaves. The coefficient forgetful sheaf
functors are exact, and f_* commutes with them by evaluation. Apply
Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic to this square.
Its hypothesis is precisely the preceding acyclicity. This proves invertibility
of the canonical unit-compatible comparison on all bounded below complexes,
without asserting that the underlying abelian sheaf of I is injective. -/
theorem isIso_moduleAbelianDerivedLowerStarComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (moduleAbelianDerivedLowerStarComparison Λ f) := by
  apply Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (moduleAbelianLowerStarIso Λ f)
  intro I hI n
  let G := (moduleAbelianForget Λ X).obj I
  let c := higherDirectImageSheafifiedPresheaf f G (n + 1)
  have hz : IsZero ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ f).op ⋙
        { obj := fun W ↦
            ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
              (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj W).rightDerived
                (n + 1)).obj G
          map := fun h ↦ (NatTrans.rightDerived
            (Functor.whiskerLeft (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
              ((evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).map h)) (n + 1)).app G
          map_id := fun W ↦ by
            simp only [CategoryTheory.Functor.map_id, Functor.whiskerLeft_id',
              NatTrans.rightDerived_id, NatTrans.id_app]
          map_comp := fun h k ↦ by
            simp only [CategoryTheory.Functor.map_comp, Functor.whiskerLeft_comp,
              NatTrans.rightDerived_comp, NatTrans.comp_app] })) := by
    apply Functor.map_isZero
    apply Functor.isZero
    intro W
    exact moduleAbelianForget_injective_evaluation_acyclic Λ X I _ n
  have hH := hz.of_iso c.symm
  exact hH.of_iso
    ((((f)_*[AddCommGrpCat.{u + 1}]).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      (n + 1)).app G).symm

attribute [instance] isIso_moduleAbelianDerivedLowerStarComparison







/-- Applying exact functors to complexes lifts the inverse-image coefficient comparison. -/
noncomputable def moduleAbelianDerivedUpperStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    D+(moduleAbelianForget Λ Y) ⋙ D+((g)^*[AddCommGrpCat.{u + 1}]) ≅
      D+((g)^*[ModuleCat.{u + 1} Λ]) ⋙ D+(moduleAbelianForget Λ X) :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (moduleAbelianUpperStarIso Λ g) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical isomorphism for derived direct image after forgetting coefficients. -/
noncomputable def moduleAbelianDerivedLowerStarIso
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  asIso (moduleAbelianDerivedLowerStarComparison Λ f)

end AlgebraicGeometry.Etale
