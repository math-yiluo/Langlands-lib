/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.EtalePullbackForgetModules
import WeilConjectures.AlgebraicGeometry.ConstantRingModuleSheafEquivalence
import WeilConjectures.AlgebraicGeometry.InjectiveModuleDirectImageAcyclic
import WeilConjectures.AlgebraicGeometry.FieldExtensionHigherDirectImageExchange
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections

/-! # Acyclicity of extended injective torsion module sheaves

Source: Stacks Project, Tags 0F1C, 03QU and 03FD.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

private theorem subsingleton_H_of_isZero_higherDirectImage_sepClosed
    {K : Type u} [Field K] [IsSepClosed K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of K))
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (hzero : IsZero (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F)) :
    Subsingleton (Sheaf.H F q) := by
  let Γ := Sheaf.Γ (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}
  let eΓ := Sheaf.ΓNatIsoSheafSections
    (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}
    (Scheme.isTerminalEtalePoint (k := K))
  have : Γ.PreservesEpimorphisms :=
    Functor.PreservesEpimorphisms.of_iso eΓ.symm
  have : Γ.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels Γ
  have {A B} (g : A ⟶ B) : PreservesColimit (parallelPair g 0) Γ :=
    Functor.PreservesHomology.preservesCokernel Γ g
  have : PreservesFiniteColimits Γ := Functor.preservesFiniteColimits_of_preservesCokernels Γ
  let S := (DerivedCategory.singleFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F
  let D := (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj S
  have hD : IsZero ((DerivedCategory.homologyFunctor
      (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj D) :=
    hzero.of_iso ((lowerStar AddCommGrpCat.{u + 1} f).homologyRightDerivedFunctorObjSingleFunctorIso
      F q)
  have hΓD := Γ.map_isZero hD
  have hmap : IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ)).obj
      (Γ.mapDerivedCategory.obj D)) :=
    hΓD.of_iso ((Γ.mapDerivedCategoryHomologyFunctorIso (q : ℤ)).app D).symm
  have hderived : IsZero ((cohomology AddCommGrpCat.{u + 1} Y (q : ℤ)).obj S) := by
    let e := (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso
      AddCommGrpCat.{u + 1} f).app S
    let e' := (Γ.rightDerivedFunctorIsoMapDerivedCategory).app D
    exact hmap.of_iso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1}
      (q : ℤ)).mapIso (e.symm ≪≫ e'))
  obtain ⟨eH⟩ := Scheme.nonempty_sheafH_extDerivedIso Y q
  exact AddCommGrpCat.subsingleton_of_isZero (hderived.of_iso (eH.app F))

/-- The inverse image of an injective Z/n-module sheaf is acyclic after extending
algebraically closed scalars, when n is invertible in the base field.
Source: Stacks Project, Tag 0F1C (field-extension exchange), Tag 03QU (cohomology over
separably closed bases) and Tag 03FD (abelian acyclicity of injective module sheaves).
(blueprint: lem-sc-algclosed-extension-injective-acyclic)

Proof: Identify J with a module over the constant Z/n ring sheaf, preserving
injectivity and the underlying abelian sheaf. The injective-module direct-image
acyclicity theorem gives vanishing of every positive higher direct image along f.
The identity of J, and hence of its underlying abelian sheaf, is killed by n.
Apply relative field-extension exchange to identify the higher direct image after
extension with the exact inverse image of this zero sheaf. It is therefore zero.
Global sections on Spec K are exact because K is separably closed. Their total
right derived functor is their exact derived functor; Leray and the homology
comparison identify the positive cohomology on X_K with zero. The comparison
between Sheaf.H and derived cohomology, followed by the module-forgetting inverse
image isomorphism, gives precisely the group in the statement. For n = 1 every
module sheaf is zero; n = 0 is excluded by hn. Empty X causes no exception.
The field-extension comparison is proved from smooth finite-type stages and affine
inverse-limit continuity, using perfectness of k. -/
theorem subsingleton_cohomology_upperStar_injective_algClosed_extension
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) (hn : (n : k) ≠ 0)
    (J : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))
    [Injective J] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
        AddCommGrpCat.{u + 1})).obj
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj J)) q) := by
  let R := ULift.{u + 1} (ZMod n)
  let U := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
  let F := U.obj J
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst f g
  let f' := pullback.snd f g
  have hJkill : n • 𝟙 J = 0 := by
    ext V x
    change n • x = 0
    rw [← Nat.cast_smul_eq_nsmul R]
    have hnR : (n : R) = 0 := by
      change (n : ULift.{u + 1} (ZMod n)) = 0
      exact ULift.ringEquiv.injective (by simp)
    rw [hnR, zero_smul]
  have : U.Additive := ⟨by intros; ext V x; rfl⟩
  have hkill : n • 𝟙 F = 0 := by
    change n • 𝟙 (U.obj J) = 0
    rw [← U.map_id, ← U.map_nsmul, hJkill, U.map_zero]
  obtain ⟨E, ⟨e⟩⟩ := constantRing_moduleSheaf_equivalence X n
  let I := E.functor.obj J
  have : Injective I := (E.map_injective_iff J).2 inferInstance
  have hI := isZero_higherDirectImage_of_injective_module f (ULift.{u} (ZMod n)) I q hq
  have hI' : IsZero (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj
      ((SheafOfModules.toSheaf _).obj I)) :=
    hI.of_iso
      ((lowerStar AddCommGrpCat.{u + 1} f).homologyRightDerivedFunctorPlusObjSingleFunctorIso
        ((SheafOfModules.toSheaf _).obj I) q).symm
  have hsource : IsZero (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).obj F) :=
    hI'.of_iso (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived q).mapIso (e.app J))
  obtain ⟨exchange⟩ := nonempty_fieldExtension_higherDirectImage_iso (K := K) f n hn F hkill q
  have htarget : IsZero (((lowerStar AddCommGrpCat.{u + 1} f').rightDerived q).obj
      ((upperStar AddCommGrpCat.{u + 1} p).obj F)) :=
    ((upperStar AddCommGrpCat.{u + 1} g).map_isZero hsource).of_iso exchange.symm
  have hH := subsingleton_H_of_isZero_higherDirectImage_sepClosed f'
    ((upperStar AddCommGrpCat.{u + 1} p).obj F) q htarget
  obtain ⟨eU⟩ := pullback_forget_modules_iso R p J
  let eH := ((Sheaf.functorH.{u + 1} _ q).mapIso eU).addCommGroupIsoToAddEquiv
  exact ⟨fun a b ↦ eH.injective (hH.elim (eH a) (eH b))⟩

end AlgebraicGeometry.Etale
