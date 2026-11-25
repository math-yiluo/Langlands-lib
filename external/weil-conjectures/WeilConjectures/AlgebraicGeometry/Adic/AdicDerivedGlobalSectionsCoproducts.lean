/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedBelowCoproducts
import all WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleCohomologyCoproducts
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Bounded-below sums and integral derived global sections

Source: Bhatt--Scholze, Lemma 6.3.14(1); Stacks Project, Tags 09A2 and 09A3.
(blueprint: lem-weil-pbc-adic-derived-sections-bounded-below-coproducts).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.Scheme

/-- Derived sections with any specified scalar action preserve every
uniformly bounded-below coproduct. No rational algebra structure is required.
Source: Bhatt--Scholze, Lemma 6.3.14(1); Stacks Project, Tags 09A2 and 09A3.
(blueprint: lem-weil-pbc-adic-derived-sections-bounded-below-coproducts).

Proof: the affine weakly contractible hypercover calculation shows that every
classical derived evaluation functor on a qcqs object preserves sums. Exact scalar
restriction gives the same assertion with the A action. Choose injective complex
representatives with the common termwise lower bound. Their sum still has that
bound and consists of sections-acyclic objects: higher derived sections of each
term are sums of zero objects. The bounded-below acyclic comparison identifies
its derived sections with termwise sections. Naturality and the termwise coproduct
property then show that derived sections preserve the coproduct of the chosen
representatives. Transport by their isomorphisms to the original family. -/
theorem proEtale_derivedGlobalSections_boundedBelow_preservesColimit
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T]
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    {A : Type (u + 1)} [CommRing A]
    (φ : A →+* R.obj.obj (op (⊤_ T.ProEt)))
    [HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} A)]
    [HasDerivedCategory (SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
    [Abelian.HasKInjectiveResolutions (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]
    (I : Type (u + 1)) (M : I → DerivedCategory (SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)))
    (N : ℤ) (hM : ∀ i, (M i).IsGE N) :
    letI : (SheafOfModules.evaluation.{u + 1} ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
        (op (⊤_ T.ProEt))).Additive := ⟨by intros; rfl⟩
    PreservesColimit (Discrete.functor M)
      ((SheafOfModules.evaluation.{u + 1} ((sheafCompose (ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op (⊤_ T.ProEt)) ⋙
          ModuleCat.restrictScalars φ).rightDerivedFunctor) := by
  classical
  let C := SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let ev := SheafOfModules.evaluation.{u + 1}
    ((sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) (op (⊤_ T.ProEt))
  let G : ModuleCat.{u + 1} (R.obj.obj (op (⊤_ T.ProEt))) ⥤ ModuleCat.{u + 1} A :=
    ModuleCat.restrictScalars φ
  let F := ev ⋙ G
  let : IsGrothendieckAbelian.{u + 1} C :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
        (ProEt.topology T) R).1
  have : ev.Additive := ⟨by intros; rfl⟩
  have : G.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1}
      φ).isLeftAdjoint
  have : G.IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1}
      φ).isRightAdjoint
  have : PreservesFiniteColimits G := inferInstance
  have : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (ev ⋙ G)
    infer_instance
  have hT : IsTerminal (ProEt.mk (𝟙 T)) :=
    IsTerminal.ofUniqueHom
      (fun U ↦ MorphismProperty.Over.homMk U.hom (Category.comp_id _) (by trivial)) (by
      intro U f
      apply MorphismProperty.Over.Hom.ext
      have hw := MorphismProperty.Over.w f
      change f.left ≫ 𝟙 T = U.hom at hw
      exact (Category.comp_id _).symm.trans hw)
  let eT : (⊤_ T.ProEt).left ≅ T :=
    (ProEt.forget T ⋙ Over.forget T).mapIso (terminalIsTerminal.uniqueUpToIso hT)
  have : CompactSpace (⊤_ T.ProEt).left :=
    QuasiCompact.compactSpace_of_compactSpace eT.hom
  have : QuasiSeparatedSpace (⊤_ T.ProEt).left :=
    quasiSeparatedSpace_of_quasiSeparated eT.hom
  have hpres (q : ℕ) : PreservesColimitsOfShape (Discrete I) (F.rightDerived q) := by
    have : PreservesColimitsOfShape (Discrete I) (ev.rightDerived q) :=
      qcqs_evaluation_preservesCoproducts T R (⊤_ T.ProEt) I q
    exact preservesColimitsOfShape_of_natIso (rightDerivedExactCompIso ev G q).symm
  have representatives (i : I) : ∃ E : CochainComplex C ℤ,
      E.IsStrictlyGE N ∧ (∀ n, Injective (E.X n)) ∧
        Nonempty (DerivedCategory.Q.obj E ≅ M i) := by
    have : (M i).IsGE N := hM i
    obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE (M i) N
    obtain ⟨E, a, ha, hE, hEN⟩ :=
      CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L N
    have : QuasiIso a := ha
    exact ⟨E, hEN, hE, ⟨(asIso (DerivedCategory.Q.map a)).symm ≪≫ e.symm⟩⟩
  choose E hEN hE he using representatives
  have : ∀ i, (E i).IsStrictlyGE N := hEN
  have : ∀ (i : I) (n : ℤ), Injective ((E i).X n) := hE
  have : ∀ i, (E i).IsKInjective := fun i ↦
    CochainComplex.isKInjective_of_injective (E i) N
  have : PreservesColimitsOfShape (Discrete I) (F.rightDerived 0) := hpres 0
  have : PreservesColimitsOfShape (Discrete I) F :=
    preservesColimitsOfShape_of_natIso F.rightDerivedZeroIsoSelf
  have heval (n : ℤ) : (∐ E).X n ≅ ∐ (fun i ↦ (E i).X n) :=
    PreservesCoproduct.iso (HomologicalComplex.eval C (.up ℤ) n) E
  have : (∐ E).IsStrictlyGE N := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    apply IsZero.of_iso _ (heval n)
    apply (coproductIsCoproduct (fun i ↦ (E i).X n)).isZero_pt
    exact Functor.isZero _ (fun i ↦ (E i.as).isZero_of_isStrictlyGE N n hn)
  have hacyclic (n : ℤ) : F.rightAcyclic ((∐ E).X n) := by
    apply F.rightAcyclic.prop_of_iso (heval n).symm
    intro q
    have : PreservesColimitsOfShape (Discrete I) (F.rightDerived (q + 1)) := hpres _
    exact (isColimitOfPreserves (F.rightDerived (q + 1))
      (coproductIsCoproduct (fun i ↦ (E i).X n))).isZero_pt
        (Functor.isZero _ fun i ↦ F.isZero_rightDerived_obj_injective_succ q ((E i.as).X n))
  have : PreservesColimit (Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)))
      F.rightDerivedFunctor := uniformCoproduct F I E
        (unit_of_acyclic F (∐ E) N hacyclic)
  let e : Discrete.functor (fun i ↦ DerivedCategory.Q.obj (E i)) ≅ Discrete.functor M :=
    Discrete.natIso (fun i ↦ (he i.as).some)
  exact preservesColimit_of_iso_diagram F.rightDerivedFunctor e

end AlgebraicGeometry.Scheme
