/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.Torsion.TorsionEtaleCohomologicalDimension
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import Mathlib.Algebra.Homology.Additive
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTorsionEtaleCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantProjectionFormula
import WeilConjectures.AlgebraicGeometry.Open.OpenTorBoundFiniteConstantTests
import WeilConjectures.AlgebraicGeometry.Open.OpenTorBoundStalkFilteredExtension
import WeilConjectures.AlgebraicGeometry.Open.OpenDirectImageFiniteCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Uniform Tor bound for finite-coefficient etale open direct images

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), finite A open-image case;
Stacks Project, Tag 0F10, clause (1), and definition-cd-f
(blueprint: lem-sfb-finite-etale-open-uniform-tor-image).

The relative dimension is the coefficient-independent torsion dimension of the morphism.
The derived categories and tensor products are ordinary and unbounded.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- For a quasi-compact open immersion of separated finite-type schemes over any field
of positive characteristic, finite prime-to-characteristic coefficients give a uniform
higher-direct-image bound equal to the torsion etale dimension of the immersion.
The canonical finite-constant projection maps are invertible, and bounded constructible
complexes of Tor amplitude `[a,b]` have bounded constructible direct image of Tor amplitude
`[a,b+d]`, tested against every module sheaf. The zero coefficient ring is allowed.

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), finite A open-image case; Stacks 0F10 (1), definition-cd-f
(blueprint: lem-sfb-finite-etale-open-uniform-tor-image).

Proof plan:
1. Apply theorem-results-from-etale-theory--6 (1) over k to j. By definition-cohomological-dimension
its finite dimension is a natural number d, depending only on j; no hypothesis on the absolute
dimension of k is needed.
2. Every A-module sheaf is killed by ell^n, hence its underlying abelian sheaf is torsion.
The definition of d gives abelian higher-image vanishing above d. Transfer this through
lem-sbc-higher-direct-image-forget-comparison; the forgetful functor reflects zero objects.
The bounded-below and total derived images agree on sheaves in degree zero.
3. A finite ring is Noetherian, and every finite A-module is finitely presented, since
both a finite free cover and its kernel are finite. The bounded constructible L is bounded
above. Apply proposition-open-direct-image-preserves-finite--1 using step 2. Its map is the recorded
counit-adjunction mate, with the canonical constant inverse-image identification.
4. L is also bounded below. Apply lem-sf-open-tor-bound-finite-constant-tests with e=d,
the vanishing of step 2 and the projection isomorphisms of step 3. This gives vanishing
outside [a,b+d] after tensoring the direct image with every finite constant module.
5. Apply lem-sf-open-tor-bound-stalk-filtered-extension to extend these tests to all
module sheaves. It uses stalks and exact filtered unions and has no field restriction.
6. ell^n is invertible in k. Apply corollary-open-direct-image-over-field--1 to L to obtain
bounded constructibility of its direct image. Combine with steps 1--5. For the zero ring
all unital modules vanish, and the same coefficient-independent d remains valid. -/
theorem finiteEtaleOpen_uniformTorImage
    (ell p : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : ell ≠ p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 1 ≤ n ∧ (ell : A) ^ n = 0)
    {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    ∃ d : ℕ, (d : ℕ∞) = j.torsionEtaleCohomologicalDimension ∧
      (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ),
        (d : ℤ) < q → IsZero
          ((_root_.DerivedCategory.homologyFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
            ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
              ((_root_.DerivedCategory.singleFunctor
                (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj F)))) ∧
      ∀ (a b : ℤ), a ≤ b → ∀ L : DerivedCategoryModule A U,
        DerivedCategory.isBoundedConstructible A U L →
        DerivedCategory.hasTorAmplitudeIn A U a b L →
        (∀ (M : ModuleCat.{u + 1} A), Finite M → IsIso
          (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app L).app
            ((_root_.DerivedCategory.singleFunctor
              (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
              ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M)))) ∧
        DerivedCategory.isBoundedConstructible A X
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj L) ∧
        DerivedCategory.hasTorAmplitudeIn A X a (b + (d : ℤ))
          ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj L) := by
  classical
  have : Fact p.Prime := ⟨CharP.char_prime_of_ne_zero k (Nat.ne_of_gt _hp)⟩
  obtain ⟨n, hn, hkill⟩ := _hA
  have hkill' : ((ell ^ n : ℕ) : A) = 0 := by
    simpa only [Nat.cast_pow] using hkill
  have hcoeff : IsSmoothBaseChangeCoefficients (ell ^ n) A (Spec (.of k)) := by
    have hell : (ell : k) ≠ 0 := by
      intro hz
      have heq := CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) hz
      exact _hne (heq.symm.trans (ringChar.eq k p))
    have hu : IsUnit ((ell ^ n : ℕ) : k) := by
      rw [Nat.cast_pow]
      exact (isUnit_iff_ne_zero.mpr hell).pow n
    exact ⟨pow_pos (Fact.out : ell.Prime).pos n, inferInstance, hkill',
      by simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  let S : Set ℕ∞ := {d | ∃ m : ℕ, d = (m : ℕ∞) ∧
    ∀ (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}), F.IsTorsion →
      ∀ q : ℤ, (m : ℤ) < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
            ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} j).obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)))}
  have hfin := (torsionEtaleCohomologicalDimension_finite_of_finiteType k U X j).1
  change sInf S < ⊤ at hfin
  have hs : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty.mp h, sInf_empty] at hfin
    exact lt_irrefl _ hfin
  obtain ⟨d, hd, hab⟩ := csInf_mem hs
  have hvan (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ)
      (hq : (d : ℤ) < q) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((rightDerivedLowerStar (ModuleCat.{u + 1} A) j).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
    let V := sheafCompose U.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    let W := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})
    have ht : (V.obj F).IsTorsion :=
      Sheaf.IsTorsion.of_forall_isAddTorsion fun T ↦
        IsAddTorsion.module_of_finite A (F.obj.obj T)
    have hz := hab (V.obj F) ht q hq
    obtain ⟨e⟩ := nonempty_higherDirectImage_forget_iso A j q F
    have hzero := hz.of_iso e
    have hm : IsZero (higherDirectImage A j q F) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply W.map_injective
      exact hzero.eq_of_src _ _
    exact hm.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)).symm)
  refine ⟨d, hd.symm, hvan, ?_⟩
  intro a b hab L hL hTor
  obtain ⟨c, e, hce, hLe⟩ := hL.2
  have hupper : ∃ e : ℤ, ∀ q : ℤ, e < q →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj L) :=
    ⟨e, fun q hq ↦ hLe q (Or.inr hq)⟩
  have hge : L.IsGE c := (_root_.DerivedCategory.isGE_iff L c).2
    (fun q hq ↦ hLe q (Or.inl hq))
  let Lplus : _root_.DerivedCategory.Plus
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) := ⟨L, ⟨c, hge⟩⟩
  have hproj (M : ModuleCat.{u + 1} A) (hM : Finite M) : IsIso
      (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app L).app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))) := by
    have : Finite M := hM
    have : IsNoetherianRing A := isNoetherian_of_finite A A
    have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
    have hi := isIso_finiteConstantProjectionMap A j d
      (fun F q hq ↦ hvan F q (by exact_mod_cast hq)) L hupper M
    dsimp only [finiteConstantProjectionMap, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hi
    exact (isIso_comp_right_iff _ _).1 hi
  refine ⟨hproj, ?_, ?_⟩
  · exact isBoundedConstructible_rightDerivedLowerStar_of_isOpenImmersion k A (ell ^ n)
      hcoeff (X ↘ Spec (.of k)) j L hL
  · apply open_tor_bound_stalk_filtered_extension A a (b + (d : ℤ))
    exact open_tor_bound_finite_constant_tests p k ell _hne A
      ⟨n, fun x ↦ by rw [← Nat.cast_smul_eq_nsmul A, hkill', zero_smul]⟩
      (U ↘ Spec (.of k)) (X ↘ Spec (.of k)) j (comp_over j _) a b d hab
      (Int.natCast_nonneg d) Lplus hTor (fun q F hq ↦ hvan F q hq) hproj

end AlgebraicGeometry.Etale
