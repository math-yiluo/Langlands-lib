/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.AffineFreeEtaleModuleFamilyModels
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite

import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldFiniteTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Compact affine étale free sheaves over a finite field

Source: Bhatt--Scholze, The pro-étale topology for schemes, Lemma 6.3.11,
Section 6.4, Lemma 6.4.5(1), Proposition 6.4.8; the finite-field bound is
`lemma-cohomological-dimension-base-field` (blueprint: lem-sfb-finite-field-etale-free-compact).

The indexing and Hom universe is `u + 1`; the ordinary derived category has
object universe `u + 2`. A chosen small skeleton of the affine étale basis is
supplied by `B`, `e` and `hB`. The sheaves and their single complexes are the
existing free Yoneda and the degree-zero `singleFunctor` construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option linter.style.haveILetI false in
set_option linter.unusedVariables false in
private theorem moduleFiniteCd_of_primeCd
    (ell : ℕ) [Fact ell.Prime] (K : Type u) [Field K] [Finite K]
    (R : Type (u + 1)) [CommRing R] [Finite R] (r : ℕ) (hr : (ell ^ r : R) = 0) :
    HasFiniteCohomologicalDimension R (Spec (.of K)) := by
  classical
  refine ⟨1, fun F q hq ↦ ?_⟩
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
  let B := (sheafCompose (Spec (.of K)).smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})).obj F
  letI : Scheme.IsTorsionModuleSheaf F :=
    Scheme.IsTorsionModuleSheaf.of_isTorsion isAddTorsion_of_finite F
  have ht : B.IsTorsion :=
    (Scheme.isTorsionModuleSheaf_iff_isTorsion F).mp inferInstance
  have hz : IsZero ((Etale.cohomology Ab.{u + 1} (Spec (.of K)) n).obj
      ((DerivedCategory.singleFunctor _ 0).obj B)) := by
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    exact Scheme.hasTorsionEtaleCohomologicalDimensionLE_one_of_finite_baseField K
      B ht n (by omega)
  obtain ⟨iso⟩ := Scheme.nonempty_etaleModuleCohomology_forgetIso
    (Spec (.of K)) R n
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero (hz.of_iso (iso.app F)))

set_option maxRecDepth 100000 in
set_option linter.style.haveILetI false in
set_option linter.unusedVariables false in
/-- The affine étale free sheaves over a finite field are canonically extensions
by zero of the constant rank-one sheaf, constructible and flat; their degree-zero
complexes are bounded constructible of Tor amplitude `[0,0]` and compact in the
whole unbounded derived category. The extension-by-zero isomorphism is normalized
by the two evaluation bijections, so it is the representing-object comparison.

Source: Bhatt--Scholze, Lemma 6.3.11, Section 6.4, Lemma 6.4.5(1),
Proposition 6.4.8; Stacks Tags 03DI, 03S8, 03EV and 0F11
(blueprint: lem-sfb-finite-field-etale-free-compact).

Proof in words:
1. The affine étale basis is essentially small.  The given equivalence and
   skeletal hypothesis provide the indexing category; the Grothendieck sheaf
   instance and the derived-coproduct theorem provide coproducts and local
   smallness.
2. The hypotheses on `f` give the required noetherian, compact and
   quasi-separated instances on `X`; the affine chart `W` has the corresponding
   instances.  Existing free-Yoneda lemmas give constructibility and flatness.
3. The single complex is bounded constructible by the degree-zero
   characterization.  Its one-term flat model, with all other terms zero,
   gives Tor amplitude `[0,0]`.
4. Choose `r` with `ell^r = 0` in `A`.  The finite-field torsion bound and the
   module/abelian cohomology comparison give finite cohomological dimension for
   `A` on `Spec k`.  This supplies the invertible-exponent instances.  The
   existing constructible-finite-Tor compactness theorem then makes the single
   complex compact in the full unbounded derived category.
5. Let `S` be the étale lower-shriek of the constant rank-one `A`-module.
   The free-Yoneda evaluation equivalence and the shriek evaluation equivalence
   both represent evaluation at `W`.  Compose them to obtain mutually inverse
   hom-set equivalences, use Coyoneda extensionality to define the comparison
   isomorphism, and use naturality of both evaluation equivalences to prove the
   required normalization.  This also covers zero coefficients and empty charts.
-/
theorem finiteField_affineEtaleFree_compact
    {k : Type u} [Field k] [Finite k]
    (ℓ : ℕ) (hℓprime : Nat.Prime ℓ) (hℓchar : ℓ ≠ ringChar k)
    {A : Type (u + 1)} [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ℓ : A) ^ r = 0)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (B : Type (u + 1)) [Category.{u} B] (e : B ≌ X.AffineEtale)
    (hB : Skeletal B) :
    ∃ hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule A X),
      LocallySmall.{u + 1} (DerivedCategoryModule A X) ∧
      ∀ U : B,
        Scheme.IsConstructibleEtaleModuleSheaf (Sheaf.freeYoneda X.smallEtaleTopology
          ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)) (ModuleCat.of A A)) ∧
        ObjectProperty.flat (Sheaf.freeYoneda X.smallEtaleTopology
          ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)) (ModuleCat.of A A)) ∧
        DerivedCategory.isBoundedConstructible A X
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Sheaf.freeYoneda X.smallEtaleTopology
              ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)) (ModuleCat.of A A))) ∧
        DerivedCategory.hasTorAmplitudeIn A X 0 0
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Sheaf.freeYoneda X.smallEtaleTopology
              ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)) (ModuleCat.of A A))) ∧
        @IsCompactObject (DerivedCategoryModule A X) _ _ hcoprod
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Sheaf.freeYoneda X.smallEtaleTopology
              ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)) (ModuleCat.of A A))) ∧
        ∃ comparison : (Sheaf.freeYoneda X.smallEtaleTopology
          ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)) (ModuleCat.of A A)) ≅
          ((etaleLowerShriek (ModuleCat.{u + 1} A)
              ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)).hom inferInstance).obj
            ((constantSheaf
              ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)).left.smallEtaleTopology
              (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))),
          ∀ (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
            (a : ((etaleLowerShriek (ModuleCat.{u + 1} A)
              ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)).hom inferInstance).obj
            ((constantSheaf
              ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)).left.smallEtaleTopology
              (ModuleCat.{u + 1} A)).obj (ModuleCat.of A A))) ⟶ G),
            (Sheaf.freeYonedaHomEquiv (comparison.hom ≫ a)).hom 1 =
              Scheme.shriekEvalEquiv ((Scheme.AffineEtale.Spec X).obj (e.functor.obj U)) G a := by
  classical
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  letI : IsNoetherian X := {}
  letI : TopologicalSpace.NoetherianSpace X := by infer_instance
  letI : IsGrothendieckAbelian.{u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
  letI : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
    IsGrothendieckAbelian.hasColimits _
  let hc : HasCoproducts.{u + 1} (DerivedCategoryModule A X) :=
    CategoryTheory.derived_hasCoproducts
  refine ⟨hc, inferInstance, ?_⟩
  intro U
  let W := (Scheme.AffineEtale.Spec X).obj (e.functor.obj U)
  letI : IsAffine W.left := by
    change IsAffine ((Scheme.Spec).obj _)
    infer_instance
  letI : CompactSpace W.left := Scheme.compactSpace_of_isAffine W.left
  letI : QuasiSeparatedSpace W.left := quasiSeparatedSpace_of_isAffine W.left
  have hconstruct : Scheme.IsConstructibleEtaleModuleSheaf
      (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of A A)) := by
    apply (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
    exact isConstructibleSheaf_freeYoneda (X := X) W
  have hflat : ObjectProperty.flat
      (Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of A A)) := by
    exact flat_freeYoneda (X := X) W
  let F := Sheaf.freeYoneda X.smallEtaleTopology W (ModuleCat.of A A)
  letI : Scheme.IsConstructibleSheaf F := isConstructibleSheaf_freeYoneda (X := X) W
  have hbc0 := DerivedCategory.boundedConstructible_singleFunctor_obj F 0
  have hbounded : DerivedCategory.isBoundedConstructible A X
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    unfold DerivedCategory.isBoundedConstructible
    constructor
    · intro q
      exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
        (hbc0.2 q)
    · refine ⟨0, 0, le_rfl, fun q hq ↦ ?_⟩
      rcases hq with hq | hq
      · exact (_root_.DerivedCategory.isGE_iff _ 0).1 inferInstance q hq
      · exact (_root_.DerivedCategory.isLE_iff _ 0).1 inferInstance q hq
  have htor : DerivedCategory.hasTorAmplitudeIn A X 0 0
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    apply (hasTorAmplitudeIn_iff_exists_flatModel A 0 0 le_rfl _ hbc0).2
    refine ⟨(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F,
      ⟨fun q hq ↦ ?_, fun q ↦ ?_⟩,
      ⟨(_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app F⟩⟩
    · exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
    · by_cases hq : q = 0
      · subst hq
        exact ObjectProperty.prop_of_iso _
          (HomologicalComplex.singleObjXSelf _ 0 F).symm hflat
      · exact ObjectProperty.flat_of_isZero
          (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)
  have hcompact : @IsCompactObject (DerivedCategoryModule A X) _ _ hc
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
    obtain ⟨r, hr⟩ := hA
    letI : Fact ℓ.Prime := ⟨hℓprime⟩
    have hAcd : HasFiniteCohomologicalDimension A (Spec (.of k)) :=
      moduleFiniteCd_of_primeCd ℓ k A r hr
    letI : HasInvertibleExponent A (Spec (.of k)) := by
      refine ⟨ℓ ^ r, pow_pos hℓprime.pos r, ?_, ?_⟩
      · simpa only [Nat.cast_pow] using hr
      · have hℓ : (ℓ : k) ≠ 0 :=
          CharP.cast_ne_zero_of_ne_of_prime k (Fact.out : ℓ.Prime) hℓchar.symm
        simpa using (isUnit_iff_ne_zero.mpr (pow_ne_zero r hℓ)).map
          (Scheme.ΓSpecIso (.of k)).inv.hom
    letI : HasInvertibleExponent A X := HasInvertibleExponent.of_hom f
    have hctf : DerivedCategory.constructibleFiniteTor
        (ModuleCat.{u + 1} A) X ((_root_.DerivedCategory.singleFunctor _ 0).obj F) := by
      refine ⟨hbc0, ⟨0, 0, ?_⟩⟩
      exact (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn).1 htor
    have hcb := compactBoundedHom_of_constructibleFiniteTor A hAcd f hctf
    exact (isCompactObject_iff_isCompactObj _).2 hcb.1
  refine ⟨hconstruct, hflat, hbounded, htor, hcompact, ?_⟩
  let S := (etaleLowerShriek (ModuleCat.{u + 1} A) W.hom inferInstance).obj
    ((constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (ModuleCat.of A A))
  let freeEval (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (F ⟶ G) ≃ G.obj.obj (Opposite.op W) :=
    Sheaf.freeYonedaHomEquiv.trans (ModuleCat.homEquiv.trans
      (LinearMap.ringLmapEquivSelf A ℕ _).toEquiv)
  let e' (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (S ⟶ G) ≃ G.obj.obj (Opposite.op W) := Scheme.shriekEvalEquiv W G
  let rep (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (S ⟶ G) ≃ (F ⟶ G) := (e' G).trans (freeEval G).symm
  have freeEval_apply (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (x : F ⟶ G) : freeEval G x = Sheaf.freeYonedaHomEquiv x 1 := by
    rfl
  let cmp : S ≅ F :=
    Coyoneda.ext _ _
      (fun {Z} a ↦ rep Z a)
      (fun {Z} a ↦ (rep Z).symm a)
      (fun a ↦ by simp) (fun a ↦ by simp)
      (fun {Z Z'} a b ↦ by
        apply (e' Z').injective
        simp only [rep, Equiv.symm_trans_apply, Equiv.symm_symm,
          Equiv.apply_symm_apply, e']
        have hh := Scheme.shriekEvalEquiv_comp W
          ((e' Z).symm (freeEval Z a)) b
        rw [hh, Equiv.apply_symm_apply]
        rw [freeEval_apply, freeEval_apply]
        change Sheaf.freeYonedaHomEquiv (a ≫ b) 1 =
          b.hom.app (Opposite.op W) (Sheaf.freeYonedaHomEquiv a 1)
        rw [Etale.freeYonedaHomEquiv_comp]
        rfl)
  let comparison : F ≅ S := cmp.symm
  refine ⟨comparison, ?_⟩
  intro G a
  have hcmp : comparison.hom = rep S (𝟙 S) := by
    rfl
  have hfree0 : freeEval S comparison.hom = e' S (𝟙 S) := by
    rw [hcmp]
    dsimp [rep]
    exact Equiv.apply_symm_apply _ _
  have hfreecomp : Sheaf.freeYonedaHomEquiv comparison.hom 1 = e' S (𝟙 S) := by
    simpa only [freeEval_apply] using hfree0
  have hnat := Etale.freeYonedaHomEquiv_comp comparison.hom a
  rw [hnat]
  change a.hom.app (Opposite.op W) (Sheaf.freeYonedaHomEquiv comparison.hom 1) = _
  rw [hfreecomp]
  have hn := Scheme.shriekEvalEquiv_comp W (𝟙 S) a
  rw [Category.id_comp] at hn
  simpa only using hn.symm

end AlgebraicGeometry.Etale
