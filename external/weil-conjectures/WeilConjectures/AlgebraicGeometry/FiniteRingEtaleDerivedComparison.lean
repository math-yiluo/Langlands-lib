/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.FiniteRingCoefficientComparison.FiniteRingEtaleCoefficientComparison
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.CategoryTheory.Sites.InjectivePresheafModuleCechCocycleLiftMax
import WeilConjectures.CategoryTheory.InjectiveModulePresheaf
import Mathlib.Algebra.Homology.ShortComplex.Ab
import WeilConjectures.AlgebraicGeometry.EtaleCechVanishingCriterion
import WeilConjectures.AlgebraicGeometry.EtaleSiteCechComplexComparison
import WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf

/-! # Bounded direct image and arbitrary ring coefficients

Source: Stacks Project, Tags 03FD and 072W.
(blueprint: lem-sfb-ring-bounded-derived-forget-comparison)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Forget the scalar action on an etale sheaf.
Source: Stacks 03FD (blueprint: lem-sfb-ring-bounded-derived-forget-comparison). -/
abbrev ringAbelianForget (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :=
  sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- Scalar forgetting preserves addition on morphisms, sectionwise.
Source: Stacks 03FD (blueprint: lem-sfb-ring-bounded-derived-forget-comparison). -/
instance ringAbelianForget_additive (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :
    (ringAbelianForget Λ X).Additive where
  map_add := by intro F G α β; ext W; rfl

/-- Scalar forgetting preserves finite limits, since presheaf inclusion reflects them.
Source: Stacks 03DA (blueprint: lem-sfb-ring-bounded-derived-forget-comparison). -/
instance ringAbelianForget_preservesFiniteLimits
    (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :
    PreservesFiniteLimits (ringAbelianForget Λ X) := by
  let U := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : PreservesLimitsOfSize.{0, 0}
      (ringAbelianForget Λ X ⋙ sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    inferInstanceAs (PreservesLimitsOfSize.{0, 0}
      (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        (Functor.whiskeringRight _ _ _).obj U))
  exact ⟨fun J _ ↦ preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})⟩

/-- Scalar forgetting preserves colimits via its coefficient coextension right adjoint.
Source: Stacks 03DB (blueprint: lem-sfb-ring-bounded-derived-forget-comparison). -/
instance ringAbelianForget_preservesColimits
    (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u}) :
    PreservesColimitsOfSize.{u + 1, u + 1} (ringAbelianForget Λ X) := by
  let f : ℤ →+* Λ := Int.castRingHom Λ
  let U := ModuleCat.restrictScalars.{u + 1} f
  let V := forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u + 1} f).isLeftAdjoint
  have : (U ⋙ V).IsLeftAdjoint := inferInstance
  have : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint :=
    inferInstanceAs (U ⋙ V).IsLeftAdjoint
  let J := X.smallEtaleTopology
  let G := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
    Functor.isoWhiskerLeft (sheafCompose J G)
      (sheafificationNatIso J AddCommGrpCat.{u + 1}).symm ≪≫
      Functor.rightUnitor (sheafCompose J G)
  have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
  have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  infer_instance

set_option backward.defeqAttrib.useBackward true

/-- Direct image commutes definitionally with forgetting coefficients.
Source: Stacks 072W (blueprint: lem-sfb-ring-bounded-derived-forget-comparison). -/
noncomputable def ringAbelianLowerStarIso
    (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (f)_*[ModuleCat.{u + 1} Λ] ⋙ ringAbelianForget Λ Y ≅
      ringAbelianForget Λ X ⋙ (f)_*[AddCommGrpCat.{u + 1}] := Iso.refl _

/-- The canonical comparison determined by the units of right derived direct image.
Source: Stacks 03FD (blueprint: lem-sfb-ring-bounded-derived-forget-comparison). -/
noncomputable def ringAbelianDerivedLowerStarComparison
    (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R+((f)_*[ModuleCat.{u + 1} Λ]) ⋙ D+(ringAbelianForget Λ Y) ⟶
      D+(ringAbelianForget Λ X) ⋙ R+((f)_*[AddCommGrpCat.{u + 1}]) :=
  Functor.rightDerivedFunctorPlusBaseChange (ringAbelianLowerStarIso Λ f).hom

/-- The Cech criterion on all etale objects gives abelian evaluation acyclicity.
Source: Stacks 03FD, second proof paragraph, via 03FC and 03F9.
(blueprint: lem-sfb-ring-bounded-derived-forget-comparison)
-/
private theorem ringAbelianForget_injective_evaluation_acyclic
    (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective G]
    (W : X.Etale) (n : ℕ) :
    IsZero (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
      (evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj (Opposite.op W)).rightDerived
        (n + 1)).obj ((ringAbelianForget Λ X).obj G)) := by
  let e := Scheme.FiniteRingCoefficientComparison.constantModuleEquivalence X Λ
  let eAb := Scheme.FiniteRingCoefficientComparison.constantModuleEquivalenceToSheafIso X Λ
  let O := (constantSheaf X.smallEtaleTopology RingCat.{u + 1}).obj (RingCat.of Λ)
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
(blueprint: lem-sfb-ring-bounded-derived-forget-comparison)

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
theorem isIso_ringAbelianDerivedLowerStarComparison
    (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (ringAbelianDerivedLowerStarComparison Λ f) := by
  apply Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic
    (ringAbelianLowerStarIso Λ f)
  intro I hI n
  let G := (ringAbelianForget Λ X).obj I
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
    exact ringAbelianForget_injective_evaluation_acyclic Λ X I _ n
  have hH := hz.of_iso c.symm
  exact hH.of_iso
    ((((f)_*[AddCommGrpCat.{u + 1}]).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
      (n + 1)).app G).symm

attribute [instance] isIso_ringAbelianDerivedLowerStarComparison

/-- Classical higher direct images commute with forgetting the scalar action.
Source: Stacks 03FD and 072W.
(blueprint: lem-sfb-ring-bounded-derived-forget-comparison)

Proof: apply homology to the proved bounded derived comparison, using exactness of
forgetting and its compatibility with single complexes. -/
noncomputable def ringAbelianHigherDirectImageIso
    (Λ : Type (u + 1)) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    (lowerStar (ModuleCat.{u + 1} Λ) f).rightDerived q ⋙ ringAbelianForget Λ Y ≅
      ringAbelianForget Λ X ⋙ (lowerStar AddCommGrpCat.{u + 1} f).rightDerived q := by
  have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
      (ringAbelianLowerStarIso Λ f).hom) :=
    isIso_ringAbelianDerivedLowerStarComparison Λ f
  have : IsIso (Functor.rightDerivedBaseChange (ringAbelianLowerStarIso Λ f).hom q) := by
    unfold Functor.rightDerivedBaseChange
    infer_instance
  exact asIso (Functor.rightDerivedBaseChange (ringAbelianLowerStarIso Λ f).hom q)

end AlgebraicGeometry.Etale
