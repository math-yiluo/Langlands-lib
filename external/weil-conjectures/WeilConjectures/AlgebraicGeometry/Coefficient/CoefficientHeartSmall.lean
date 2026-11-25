/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.EssentiallySmall

import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedCounit
import all WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.CategoryTheory.ObjectProperty.Small
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
/-!
# Essential smallness of the constructible coefficient heart

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-coefficient-heart,
`sk-lem-coefficient-heart-small.md` and its proof
(blueprint: lemma-constructible-sheaves--6).

The coefficient is the actual condensed ring pulled back from the point. The full
constructible category uses finite constant scalar models. This reopened stage-2
record retains the same canonical statement and proof interface. The smallness universe is
`u + 1`, containing the bounded schemes, the pro-etale site, and coefficient sections;
the ambient category of sheaves can have object universe `u + 2`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private theorem boundedByMonos {C : Type u} [Category.{v} C]
    [LocallySmall.{w} C] [WellPowered.{w} C]
    (P : ObjectProperty C) {I : Type z} [Small.{w} I] (H : I → C)
    (h : ∀ M, P M → ∃ i, ∃ f : M ⟶ H i, Mono f) :
    ObjectProperty.EssentiallySmall.{w} P := by
  let Q (i : I) : ObjectProperty C :=
    (MonoOver.forget (H i) ⋙ Over.forget (H i)).essImage
  have hQ (i : I) : ObjectProperty.EssentiallySmall.{w} (Q i) := by
    dsimp only [Q]
    infer_instance
  have (i : I) : ObjectProperty.EssentiallySmall.{w} (Q i) := hQ i
  have : ObjectProperty.EssentiallySmall.{w} (⨆ i, Q i) := inferInstance
  apply ObjectProperty.EssentiallySmall.of_le (Q := ⨆ i, Q i)
  intro M hM
  obtain ⟨i, f, hf⟩ := h M hM
  have := hf
  apply (le_iSup Q i) M
  exact ⟨MonoOver.mk f, ⟨Iso.refl M⟩⟩

universe u' v'
private theorem smallFromRestrictions {C : Type u} [Category.{v} C]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasProducts.{z} C]
    (I : Type z) [Small.{w} I] (D : I → Type u') [∀ i, Category.{v'} (D i)]
    (L : ∀ i, C ⥤ D i) (R : ∀ i, D i ⥤ C) (adj : ∀ i, L i ⊣ R i)
    (P : ∀ i, ObjectProperty (D i))
    (hP : ∀ i, ObjectProperty.EssentiallySmall.{w} (P i))
    (detect : ∀ {M N : C} (f : M ⟶ N), (∀ i, Mono ((L i).map f)) → Mono f) :
    ObjectProperty.EssentiallySmall.{w} (fun M ↦ ∀ i, P i ((L i).obj M)) := by
  classical
  have (i : I) := hP i
  choose Q hQ hPQ using fun i ↦
    ObjectProperty.EssentiallySmall.exists_small_le' (P i)
  let J := ∀ i, Shrink.{w} (Subtype (Q i))
  let H (j : J) : C := ∏ᶜ fun i ↦
    (R i).obj ((equivShrink (Subtype (Q i))).symm (j i)).val
  apply boundedByMonos _ H
  intro M hM
  choose Y hY e using fun i ↦ hPQ i _ (hM i)
  let j : J := fun i ↦ equivShrink (Subtype (Q i)) ⟨Y i, hY i⟩
  let iso (i : I) : (L i).obj M ≅
      ((equivShrink (Subtype (Q i))).symm (j i)).val := by
    simpa only [j, Equiv.symm_apply_apply] using (e i).some
  let t : M ⟶ H j := Pi.lift fun i ↦ (adj i).homEquiv _ _ (iso i).hom
  refine ⟨j, t, detect t fun i ↦ ?_⟩
  have fac : (L i).map t ≫
      ((L i).map (Pi.π _ i) ≫ (adj i).counit.app _) = (iso i).hom := by
    rw [← Category.assoc, ← Functor.map_comp, Pi.lift_comp_π]
    exact ((adj i).homEquiv_symm_apply _ _ _).symm.trans
      (((adj i).homEquiv _ _).symm_apply_apply (iso i).hom)
  exact mono_of_mono_fac fac

private theorem coverReflectsIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) (h : ∀ i, IsIso ((CondensedRing.upperStar Λ (U.f i)).map f)) :
    IsIso f := by
  have : ∀ i, WeaklyEtale (U.f i) :=
    (Scheme.ofArrows_mem_precoverage_iff (P := @WeaklyEtale)).mp U.mem₀.2 |>.2
  have : IsIso f.hom := by
    apply isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom U.f U.mem₀
    intro i
    have := h i
    have h1 : IsIso ((upperStar Ab.{u+1} (U.f i)).map f.hom) := by
      apply (NatIso.isIso_map_iff (profinitePointModuleForgetPullbackIso Λ (U.f i)) f).mp
      exact inferInstanceAs (IsIso ((Mod.forget _).map
        ((CondensedRing.upperStar Λ (U.f i)).map f)))
    exact (NatIso.isIso_map_iff (upperStarIsoLocalizationRestriction
      Ab.{u+1} (U.f i) inferInstance) f.hom).mp h1
  have : IsIso ((Mod.forget _).map f) := ‹IsIso f.hom›
  exact isIso_of_reflects_iso f (Mod.forget _)

private theorem coverReflectsMono
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (f : M ⟶ N) (h : ∀ i, Mono ((CondensedRing.upperStar Λ (U.f i)).map f)) :
    Mono f := by
  let := HasZeroObject.zero'
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj Λ X))
  have : IsIso (0 : kernel f ⟶ 0) := by
    apply coverReflectsIso Λ U
    intro i
    let L := CondensedRing.upperStar Λ (U.f i)
    have := h i
    have hz : IsZero (kernel (L.map f)) := isZero_kernel_of_mono _
    have hsrc : IsZero (L.obj (kernel f)) := hz.of_iso (PreservesKernel.iso L f)
    have htgt : IsZero (L.obj 0) := L.map_isZero (isZero_zero _)
    exact isIso_of_source_target_iso_zero _ hsrc.isoZero htgt.isoZero
  have hz : IsZero (kernel f) := (isZero_zero _).of_iso (asIso (0 : kernel f ⟶ 0))
  exact Abelian.mono_of_kernel_ι_eq_zero f (hz.eq_of_src _ _)

open CategoryTheory.MonoidalCategory
private theorem finitelyPresentedSmall {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
    [LocallySmall.{w} C] (R : C) [MonObj R]
    [PreservesFiniteColimits (tensorLeft R)] :
    ObjectProperty.EssentiallySmall.{w} (Mod.IsFinitelyPresented R) := by
  classical
  have : LocallySmall.{w} (Mod C R) := locallySmall_of_faithful (Mod.forget R)
  let I := Σ n m : ℕ, Shrink.{w} (Mod.finiteFree R m ⟶ Mod.finiteFree R n)
  let model (i : I) : Mod C R :=
    cokernel ((equivShrink (Mod.finiteFree R i.2.1 ⟶ Mod.finiteFree R i.1)).symm i.2.2)
  refine ⟨ObjectProperty.ofObj model, inferInstance, ?_⟩
  intro M hM
  obtain ⟨n, m, f, e⟩ := hM
  exact ⟨model ⟨n, m, equivShrink _ f⟩, ⟨(⟨n, m, equivShrink _ f⟩ : I)⟩, by
    simpa only [model, Equiv.symm_apply_apply] using e⟩

private theorem constantLocalModelsSmall
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    ObjectProperty.EssentiallySmall.{u + 1} (HasFiniteConstantLocalModel Λ X) := by
  classical
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj Λ X)
  have : HasLimitsOfSize.{u, u} C := hasLimitsOfSizeShrink.{u, u, u+1, u+1} C
  let P (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X) : ObjectProperty C :=
    fun M ↦ ∀ i : U.I₀, ObjectProperty.map (Mod.IsFinitelyPresented Λ)
      ((upperStarFromPoint (U.X i)).mapMod Λ)
        ((CondensedRing.upperStar Λ (U.f i)).obj M)
  have hP (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X) :
      ObjectProperty.EssentiallySmall.{u+1} (P U) := by
    have := finitelyPresentedSmall.{u + 2, u + 1, u + 1} Λ
    apply smallFromRestrictions U.I₀
      (fun i ↦ Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u+1})
        (condensedRingObj Λ (U.X i)))
      (fun i ↦ CondensedRing.upperStar Λ (U.f i))
      (fun i ↦ CondensedRing.lowerStar Λ (U.f i))
      (fun i ↦ CondensedRing.upperStarLowerStarAdjunction Λ (U.f i))
      (fun i ↦ ObjectProperty.map (Mod.IsFinitelyPresented Λ)
        ((upperStarFromPoint (U.X i)).mapMod Λ))
    · intro i
      infer_instance
    · intro M N f hf
      exact coverReflectsMono Λ U f hf
  have (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X) := hP U
  apply ObjectProperty.EssentiallySmall.of_le
    (Q := ⨆ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, P U)
  intro M hM
  obtain ⟨U, hU⟩ := hM
  apply (le_iSup P U) M
  intro i
  obtain ⟨N, hN, ⟨e⟩⟩ := hU i
  exact ⟨N, hN, ⟨e.symm⟩⟩

private theorem stratifiedModelsSmall
    (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    ObjectProperty.EssentiallySmall.{u+1}
      (IsFiniteConstantStratified A X) := by
  classical
  let C := Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj A X)
  let P (S : Scheme.Stratification X) : ObjectProperty C := fun M ↦
    ∀ i : Fin S.n, HasFiniteConstantLocalModel A (S.domain i)
      ((CondensedRing.upperStar A (S.immersion i)).obj M)
  have hP (S : Scheme.Stratification X) :
      ObjectProperty.EssentiallySmall.{u+1} (P S) := by
    have : HasLimitsOfSize.{0, 0} C := hasLimitsOfSizeShrink.{0, 0, u+1, u+1} C
    exact smallFromRestrictions (Fin S.n)
      (fun i ↦ Mod (Sheaf (Scheme.ProEt.topology (S.domain i)) Ab.{u+1})
        (condensedRingObj A (S.domain i)))
      (fun i ↦ CondensedRing.upperStar A (S.immersion i))
      (fun i ↦ CondensedRing.lowerStar A (S.immersion i))
      (fun i ↦ CondensedRing.upperStarLowerStarAdjunction A (S.immersion i))
      (fun i ↦ HasFiniteConstantLocalModel A (S.domain i))
      (fun i ↦ constantLocalModelsSmall A (S.domain i))
      (by
        intro M N f hf
        apply Preadditive.mono_of_cancel_zero
        intro Z g hg
        apply Mod.hom_ext
        have : IsNoetherian X := {}
        have : ∀ i : Fin S.n, TopologicalSpace.NoetherianSpace (S.domain i) :=
          fun i ↦ (S.immersion i).isEmbedding.noetherianSpace
        have : ∀ i : Fin S.n, QuasiCompact (S.immersion i) := fun i ↦ inferInstance
        apply AlgebraicGeometry.ProEtale.eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp
          S.immersion
        · intro x
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
            (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
          exact ⟨i, (S.range_immersion i).symm ▸ hi⟩
        · intro i
          let L := CondensedRing.upperStar A (S.immersion i)
          have := hf i
          have hzero : L.map g = 0 := by
            apply zero_of_comp_mono (L.map f)
            rw [← L.map_comp, hg, L.map_zero]
          have he := (profinitePointModuleForgetPullbackIso A (S.immersion i)).hom.naturality g
          change (L.map g).hom ≫ _ = _ ≫
            (upperStar Ab.{u + 1} (S.immersion i)).map g.hom at he
          rw [hzero, Mod.zero_hom, zero_comp] at he
          exact (cancel_epi
            ((profinitePointModuleForgetPullbackIso A (S.immersion i)).hom.app Z)).mp
              (he.symm.trans (comp_zero).symm))
  have (S : Scheme.Stratification X) := hP S
  apply ObjectProperty.EssentiallySmall.of_le
    (Q := ⨆ S : Scheme.Stratification X, P S)
  intro M hM
  obtain ⟨S, hS⟩ := hM
  exact (le_iSup P S) M hS

/-- The constructible heart for a finite subextension E of Qbar_l, or for Qbar_l itself,
has a set of isomorphism classes in the fixed larger universe.
Source: blueprint lemma-constructible-sheaves--6 and its proof, with the nine-step
DAG refinement (blueprint: lemma-constructible-sheaves--6).

Proof:
Finite presentations over the coefficient on the point form an essentially small
property: encode a presentation by two natural numbers and a morphism between the
corresponding finite free modules, and take its cokernel. Functorial images of this
property remain essentially small.

For a fixed cover, choose small representatives of the local models. Adjunction
transposes their restriction isomorphisms into a map to the product of their direct
images. Each restriction of this map is monic by the counit equation, so the map
itself is monic. Cover restrictions jointly detect this by localization of abelian
sheaves and the coefficient-forgetful comparison. The module category is well-powered,
so subobjects of these small families of products form an essentially small property.
Taking the small union over covers proves smallness of finite constant local models.

Repeat this argument over a fixed finite stratification. Joint detection for the
actual quasi-compact stratum immersions is the abelian section-detection argument
`abDetectMaps`; the coefficient-forgetful comparison transfers it to module maps.
Noetherianity makes the immersions quasi-compact. Finally take the small union over
stratifications and use the qcqs branch of the constructibility definition. Empty
covers, empty strata, the empty scheme, and rank-zero presentations are included.
The argument works for every commutative condensed coefficient ring. -/
theorem coefficientHeart_essentiallySmall (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X] :
    EssentiallySmall.{u + 1}
      (ConstantModelConstructible
        ((sheafCompose (coherentTopology Profinite.{u})
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ) X) := by
  let A := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj Λ
  have hsmall : ObjectProperty.EssentiallySmall.{u + 1}
      (IsFiniteConstantStratified A X) := stratifiedModelsSmall A X
  let : ObjectProperty.EssentiallySmall.{u + 1}
      (IsFiniteConstantStratified A X) := hsmall
  have hprop : ObjectProperty.EssentiallySmall.{u + 1}
      (IsConstantModelConstructible A X) := by
    rw [show IsConstantModelConstructible A X = IsFiniteConstantStratified A X by
      funext M
      exact ite_eq_left ⟨inferInstance, inferInstance⟩]
    exact hsmall
  let : ObjectProperty.EssentiallySmall.{u + 1}
      (IsConstantModelConstructible A X) := hprop
  cases hΛ <;> infer_instance

end AlgebraicGeometry.ProEtale
