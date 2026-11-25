/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.DirectSum.Module
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.Products
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.InjectiveCoseparator
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.DerivedHomologyInjective
import Mathlib.CategoryTheory.Generator.Abelian
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-!
# Unbounded cohomology obstructs right adjoints

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-smooth-base-change/
sec-sbc-uniform/sk-rem-sbc-scope/sk-rem-sf-fullcd-scope.md,
consequences (ii) and (iii) (blueprint: lem-sf-derived-unbounded-cohomology-obstruction).
The natural number `n` indexes the strictly positive integer `n + 1`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory Limits

open scoped DirectSum

universe uA vA dA uB vB dB r m dM

namespace DerivedCategory.UnboundedCohomologyObstruction

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{dA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]
  {R : Type r} [CommRing R] [HasDerivedCategory.{dM} (ModuleCat.{max r m} R)]

/-- The family `K_n = F[0][n]`, with `n ≥ 1` indexed by `ℕ`.
Source: scope remark, consequence (ii)
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
abbrev shifts (F : A) (n : ℕ) : DerivedCategory A :=
  ((DerivedCategory.singleFunctor A 0).obj F)⟦((n + 1 : ℕ) : ℤ)⟧

variable (e : B ⥤ ModuleCat.{max r m} R) [e.Additive]
  [PreservesFiniteLimits e] [PreservesFiniteColimits e]
  (T : DerivedCategory A ⥤ DerivedCategory B)

/-- Evaluation of degree-zero cohomology after the exact termwise functor `e`.
Source: scope remark, consequence (ii)
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
abbrev evaluation : DerivedCategory B ⥤ ModuleCat.{max r m} R :=
  e.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) 0

/-- The modules `H^(n+1)(eT(F[0]))`.
Source: scope remark, consequence (ii)
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
abbrev cohomology (F : A) (n : ℕ) : ModuleCat.{max r m} R :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) ((n + 1 : ℕ) : ℤ)).obj
    (e.mapDerivedCategory.obj (T.obj ((DerivedCategory.singleFunctor A 0).obj F)))

/-- The canonical shift identification `H⁰(eT(K_n)) ≅ H^(n+1)(eT(F[0]))`.
Source: scope remark, consequence (ii), exact functor and shift compatibility
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
def shiftIdentification [T.CommShift ℤ] (F : A) (n : ℕ) :
    (evaluation e).obj (T.obj (shifts F n)) ≅ cohomology e T F n :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) 0).mapIso
      (((T ⋙ e.mapDerivedCategory).commShiftIso ((n + 1 : ℕ) : ℤ)).app
        ((DerivedCategory.singleFunctor A 0).obj F)) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) 0).isoShift
      ((n + 1 : ℕ) : ℤ)).app
        (e.mapDerivedCategory.obj (T.obj ((DerivedCategory.singleFunctor A 0).obj F)))

/-- The canonical map `Hom(T(K_n), v(J)[0]) → Hom_R(H^(n+1)(eT(F[0])), J)`: apply `e`
termwise and degree-zero cohomology, identify `H⁰(eT(K_n))` by `shiftIdentification` and
`H⁰(e(v(J))[0])` with `e(v(J))`, then compose with the counit `e(v(J)) → J`. This is the
derived adjunction isomorphism followed by the injective-target `H⁰` bijection.
Source: scope remark, consequence (iii), injective-cogenerator Hom calculation
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction). -/
def injectiveHomMap [T.CommShift ℤ] {v : ModuleCat.{max r m} R ⥤ B} (a : e ⊣ v)
    (F : A) (n : ℕ) (J : ModuleCat.{max r m} R) :
    (T.obj (shifts F n) ⟶ (DerivedCategory.singleFunctor B 0).obj (v.obj J)) →
      (cohomology e T F n ⟶ J) :=
  fun g => (shiftIdentification e T F n).inv ≫ (evaluation e).map g ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max r m} R) 0).map
      ((e.mapDerivedCategorySingleFunctor 0).hom.app (v.obj J)) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max r m} R) 0).hom.app
      (e.obj (v.obj J)) ≫ a.counit.app J

private theorem shifts_sum_isLimit
    [IsGrothendieckAbelian.{vA} A] [HasExactLimitsOfShape (Discrete ℕ) A] (F : A) :
    Nonempty (IsLimit (Fan.mk (∐ shifts F) (Sigma.π (shifts F)))) := by
  classical
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{vA}
  let K (n : ℕ) := ((CochainComplex.singleFunctor A 0).obj F)⟦((n + 1 : ℕ) : ℤ)⟧
  let hs := coproductIsCoproduct K
  let p := Cofan.IsColimit.proj hs
  have hl := isLimitFanMkQObj
    (HomologicalComplex.isLimitFanMkProjOfIsColimit
      (fun d m n hm hn ↦ Nat.add_right_cancel
        (CochainComplex.eq_of_not_isZero_singleFunctor_obj_shift_X F d (m + 1) (n + 1)
          hm hn)) hs)
  let en (n : ℕ) : Q.obj (K n) ≅ shifts F n :=
    (Q.commShiftIso ((n + 1 : ℕ) : ℤ)).app _ ≪≫
      (shiftFunctor _ ((n + 1 : ℕ) : ℤ)).mapIso ((singleFunctorIsoCompQ A 0).app F).symm
  let x : ∐ shifts F ≅ Q.obj (∐ K) :=
    (Sigma.mapIso en).symm ≪≫ (asIso (sigmaComparison Q K))
  refine ⟨Fan.IsLimit.ofIsos hl (fun n ↦ (en n).symm) x ?_⟩
  intro n
  apply Sigma.hom_ext
  intro j
  dsimp [x]
  simp only [Category.assoc, Sigma.ι_mapIso_inv_assoc, ι_comp_sigmaComparison_assoc]
  change (en j).inv ≫ Q.map (Sigma.ι K j) ≫ Q.map (p n) =
    Sigma.ι (shifts F) j ≫ Sigma.π (shifts F) n ≫ (en n).inv
  rw [← Q.map_comp]
  by_cases h : j = n
  · subst j
    have hp : Sigma.ι K n ≫ p n = 𝟙 _ := Cofan.IsColimit.inj_proj_self hs n
    simp [hp]
  · have hp : Sigma.ι K j ≫ p n = 0 := Cofan.IsColimit.inj_proj_of_ne hs h
    simp [hp, Sigma.ι_π_of_ne_assoc _ h]

omit [HasDerivedCategory (ModuleCat R)] in
private theorem directSum_not_surjective
    (M : ℕ → ModuleCat.{max r m} R) (hM : ∀ n, ¬ IsZero (M n)) :
    ¬ Function.Surjective (DirectSum.coeFnLinearMap R (M := fun n ↦ M n)) := by
  classical
  have hn (n : ℕ) : Nontrivial (M n) :=
    not_subsingleton_iff_nontrivial.mp (fun h ↦ hM n (ModuleCat.isZero_of_subsingleton _))
  let (n : ℕ) := hn n
  choose x hx using fun n ↦ exists_ne (0 : M n)
  intro h
  obtain ⟨y, hy⟩ := h x
  let n := y.support.sup id + 1
  have hn : n ∉ y.support := fun h ↦
    Nat.not_succ_le_self _ (Finset.le_sup (f := id) h)
  have hz : y n = 0 := DFinsupp.notMem_support_iff.mp hn
  exact hx n (by simpa [hz] using (congrFun hy n).symm)

private theorem injectiveHomMap_bijective [T.CommShift ℤ]
    (v : ModuleCat.{max r m} R ⥤ B) [v.Additive]
    [PreservesFiniteLimits v] [PreservesFiniteColimits v] (a : e ⊣ v)
    (F : A) (n : ℕ) (J : ModuleCat.{max r m} R) [Injective J] :
    Function.Bijective (injectiveHomMap e T a F n J) := by
  let : Injective (v.obj J) := a.map_injective J inferInstance
  let X := T.obj (shifts F n)
  let H := DerivedCategory.homologyFunctor B 0
  let s := (DerivedCategory.singleFunctorCompHomologyFunctorIso B 0).app (v.obj J)
  let c := e.mapDerivedCategoryHomologyFunctorIso 0
  let d : cohomology e T F n ≅ e.obj (H.obj X) :=
    (shiftIdentification e T F n).symm ≪≫ (c.app X).symm
  let b := ((Equiv.ofBijective H.map (derived_homology_injective_bijective X (v.obj J))).trans
    ((Iso.refl (H.obj X)).homCongr s)).trans (a.homEquiv (H.obj X) J).symm
  let b' := b.trans (d.symm.homCongr (Iso.refl J))
  have hb : (fun g ↦ b' g) = injectiveHomMap e T a F n J := by
    funext g
    simp only [b', b, Equiv.trans_apply, Equiv.ofBijective_apply, Iso.homCongr_apply,
      Iso.refl_hom, Iso.refl_inv, Category.id_comp, Category.comp_id, Iso.symm_inv]
    change d.hom ≫ (e.map (H.map g ≫ s.hom) ≫ a.counit.app J) = _
    dsimp only [d, Iso.trans_hom, Iso.symm_hom, Iso.app_inv]
    rw [e.map_comp]
    simp only [Category.assoc]
    have hnat : c.inv.app X ≫ e.map (H.map g) =
        (evaluation e).map g ≫ c.inv.app ((singleFunctor B 0).obj (v.obj J)) := by
      simpa only [H, evaluation, Functor.comp_map] using (c.inv.naturality g).symm
    rw [reassoc_of% hnat]
    have hc : e.map s.hom =
        c.hom.app ((singleFunctor B 0).obj (v.obj J)) ≫
          (homologyFunctor (ModuleCat.{max r m} R) 0).map
            ((e.mapDerivedCategorySingleFunctor 0).hom.app (v.obj J)) ≫
          (singleFunctorCompHomologyFunctorIso (ModuleCat.{max r m} R) 0).hom.app
            (e.obj (v.obj J)) := by
      exact (e.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor 0 (v.obj J)).symm
    rw [hc]
    simp [injectiveHomMap, c, H, X, Category.assoc]
  rw [← hb]
  exact b'.bijective

/-- Unbounded positive cohomology prevents coproduct preservation and either right adjoint.

Source: scope remark, consequences (ii) and (iii)
(blueprint: lem-sf-derived-unbounded-cohomology-obstruction).

Proof: In each degree the family of shifted single complexes has at most one nonzero term,
so its direct sum and product coincide. The Grothendieck derived coproduct theorem and
exact-product localization identify them in the derived category. Exactness and shift
compatibility give `shiftIdentification`. Applying degree-zero evaluated cohomology to
the coproduct comparison gives the canonical inclusion of the direct sum into the product:
the two characterizations below check this on every summand and coordinate. Choose a
nonzero element in each cohomology module; the resulting infinite-support tuple proves
that inclusion is not surjective. Thus `T` cannot preserve countable coproducts, and cannot
be a left adjoint. For any injective cogenerator `J`, its image under the exact right
adjoint `v` is injective. Computing derived Hom into its injective single complex, then
applying the ordinary adjunction and the exact-functor homology comparison, shows that the
canonical map `injectiveHomMap` to module Hom into `J` is bijective.
They are nonzero by cogeneration. If the restriction to `D⁺` had a right adjoint `G`, these
same groups would equal `Hom(F[n+1],G(v(J)[0]))`; bounded-below t-structure orthogonality
makes these vanish for all sufficiently large `n`, a contradiction.
-/
theorem obstruction
    [IsGrothendieckAbelian.{vA} A] [IsGrothendieckAbelian.{vB} B]
    [HasExactLimitsOfShape (Discrete ℕ) A] [HasExactLimitsOfShape (Discrete ℕ) B]
    [Nontrivial R]
    (he : ∀ I : Type vB, PreservesColimitsOfShape (Discrete I) e)
    [PreservesLimitsOfShape (Discrete ℕ) e]
    (v : ModuleCat.{max r m} R ⥤ B) [v.Additive]
    [PreservesFiniteLimits v] [PreservesFiniteColimits v] (a : e ⊣ v)
    [T.Additive] [T.CommShift ℤ] [T.IsTriangulated]
    [PreservesLimitsOfShape (Discrete ℕ) T]
    (Tplus : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (compatibility : Tplus ⋙ DerivedCategory.Plus.ι ≅ DerivedCategory.Plus.ι ⋙ T)
    (F : A) (hF : ∀ n : ℕ, ¬ IsZero (cohomology e T F n)) :
    Nonempty (IsLimit (Fan.mk (∐ shifts F) (Sigma.π (shifts F)))) ∧
    (∃ (α : ModuleCat.of R (⨁ n : ℕ, cohomology e T F n) ≅
          (evaluation e).obj (∐ fun n : ℕ => T.obj (shifts F n)))
    (β : (evaluation e).obj (T.obj (∐ shifts F)) ≅
          ModuleCat.of R (∀ n : ℕ, cohomology e T F n)),
      (∀ n : ℕ, ModuleCat.ofHom (DirectSum.lof R ℕ
          (fun j : ℕ => cohomology e T F j) n) ≫ α.hom =
        (shiftIdentification e T F n).inv ≫
          (evaluation e).map (Sigma.ι (fun j : ℕ => T.obj (shifts F j)) n)) ∧
      (∀ n : ℕ, β.hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
        (evaluation e).map (T.map (Sigma.π (shifts F) n)) ≫
          (shiftIdentification e T F n).hom) ∧
      α.hom ≫ (evaluation e).map (sigmaComparison T (shifts F)) ≫ β.hom =
        ModuleCat.ofHom (DirectSum.coeFnLinearMap R)) ∧
    ¬ Function.Surjective
      (DirectSum.coeFnLinearMap R (M := fun n : ℕ => cohomology e T F n)) ∧
    ¬ PreservesColimitsOfShape (Discrete ℕ) T ∧
    ¬ T.IsLeftAdjoint ∧ ¬ Tplus.IsLeftAdjoint ∧
    ∀ (J : ModuleCat.{max r m} R), Injective J → IsCoseparator J →
      Injective (v.obj J) ∧
      ∀ n : ℕ, Function.Bijective (injectiveHomMap e T a F n J) ∧
        Nontrivial (cohomology e T F n ⟶ J) ∧
        Nontrivial (T.obj (shifts F n) ⟶
          (DerivedCategory.singleFunctor B 0).obj (v.obj J)) := by
  classical
  let : Abelian.HasKInjectiveResolutions A :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{vA}
  let : Abelian.HasKInjectiveResolutions B :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian.{vB}
  let : HasFiniteBiproducts B := Abelian.hasFiniteBiproducts
  let : CountableAB4Star B := CountableAB4Star.of_hasExactLimitsOfShape_nat B
  obtain ⟨hP, hprod, hH⟩ := derivedCategory_countableProducts_core.{0} B
  let : HasCountableProducts (DerivedCategory B) := hP
  let := hH ℕ 0
  have heN : PreservesColimitsOfShape (Discrete ℕ) e := by
    let := he (ULift.{vB} ℕ)
    exact preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) e
  let := heN
  have hPev : PreservesColimitsOfShape (Discrete ℕ) (evaluation e) :=
    preservesColimitsOfShape_of_natIso (e.mapDerivedCategoryHomologyFunctorIso 0)
  let : PreservesLimitsOfShape (Discrete ℕ) (evaluation e) :=
    preservesLimitsOfShape_of_natIso (e.mapDerivedCategoryHomologyFunctorIso 0)
  let M := cohomology e T F
  let Y (n : ℕ) := T.obj (shifts F n)
  have : PreservesColimit (Discrete.functor Y) (evaluation e) := hPev.preservesColimit
  let α : ModuleCat.of R (⨁ n : ℕ, M n) ≅ (evaluation e).obj (∐ Y) :=
    (ModuleCat.coprodIsoDirectSum M).symm ≪≫
      Sigma.mapIso (fun n ↦ (shiftIdentification e T F n).symm) ≪≫
        asIso (sigmaComparison (evaluation e) Y)
  have hα (n : ℕ) : ModuleCat.ofHom (DirectSum.lof R ℕ (fun j ↦ M j) n) ≫ α.hom =
      (shiftIdentification e T F n).inv ≫ (evaluation e).map (Sigma.ι Y n) := by
    simp only [α, Iso.trans_hom, Iso.symm_hom, asIso_hom]
    rw [← Category.assoc, ModuleCat.lof_coprodIsoDirectSum_inv]
    simp only [Sigma.ι_mapIso_hom_assoc, Iso.symm_hom]
    exact congrArg (fun f ↦ (shiftIdentification e T F n).inv ≫ f)
      (ι_comp_sigmaComparison (evaluation e) Y n)
  obtain ⟨hK⟩ := shifts_sum_isLimit F
  have hTY := isLimitFanMkObjOfIsLimit T (shifts F) (Sigma.π (shifts F)) hK
  have hEY := isLimitFanMkObjOfIsLimit (evaluation e) Y
    (fun n ↦ T.map (Sigma.π (shifts F) n)) hTY
  let b : (evaluation e).obj (T.obj (∐ shifts F)) ⟶ ModuleCat.of R (∀ n, M n) :=
    ModuleCat.ofHom (LinearMap.pi (fun n ↦
      ((evaluation e).map (T.map (Sigma.π (shifts F) n)) ≫
        (shiftIdentification e T F n).hom).hom))
  have hb (n : ℕ) : b ≫ ModuleCat.ofHom (LinearMap.proj n) =
      (evaluation e).map (T.map (Sigma.π (shifts F) n)) ≫
        (shiftIdentification e T F n).hom := by
    rfl
  have hi : IsIso b := Fan.IsLimit.isIso_of_isos hEY (ModuleCat.productConeIsLimit M)
    (fun n ↦ shiftIdentification e T F n) b hb
  let β := asIso b
  have hβ (n : ℕ) : β.hom ≫ ModuleCat.ofHom (LinearMap.proj n) =
      (evaluation e).map (T.map (Sigma.π (shifts F) n)) ≫
        (shiftIdentification e T F n).hom := hb n
  have hc : α.hom ≫ (evaluation e).map (sigmaComparison T (shifts F)) ≫ β.hom =
      ModuleCat.ofHom (DirectSum.coeFnLinearMap R (M := fun n ↦ M n)) := by
    rw [← cancel_epi (ModuleCat.coprodIsoDirectSum M).hom]
    apply Sigma.hom_ext
    intro j
    apply (ModuleCat.productConeIsLimit M).hom_ext
    intro n
    change _ ≫ (ModuleCat.ofHom (LinearMap.proj n.as) :
      ModuleCat.of R (∀ n, M n) ⟶ M n.as) =
      _ ≫ (ModuleCat.ofHom (LinearMap.proj n.as) :
        ModuleCat.of R (∀ n, M n) ⟶ M n.as)
    simp only [Category.assoc]
    rw [hβ]
    simp only [reassoc_of% (ModuleCat.ι_coprodIsoDirectSum_hom M j)]
    rw [reassoc_of% (hα j)]
    change (shiftIdentification e T F j).inv ≫ (evaluation e).map (Sigma.ι Y j) ≫
      (evaluation e).map (sigmaComparison T (shifts F)) ≫
      (evaluation e).map (T.map (Sigma.π (shifts F) n.as)) ≫
      (shiftIdentification e T F n.as).hom = _
    have hcmp : Sigma.ι Y j ≫ sigmaComparison T (shifts F) =
        T.map (Sigma.ι (shifts F) j) := ι_comp_sigmaComparison T (shifts F) j
    have hcoord : (evaluation e).map (Sigma.ι Y j) ≫
        (evaluation e).map (sigmaComparison T (shifts F)) ≫
        (evaluation e).map (T.map (Sigma.π (shifts F) n.as)) =
        (evaluation e).map (T.map (Sigma.ι (shifts F) j ≫ Sigma.π (shifts F) n.as)) := by
      rw [← Functor.map_comp_assoc, hcmp, ← Functor.map_comp, ← T.map_comp]
    calc
      _ = (shiftIdentification e T F j).inv ≫
          (evaluation e).map (T.map (Sigma.ι (shifts F) j ≫ Sigma.π (shifts F) n.as)) ≫
          (shiftIdentification e T F n.as).hom := by
        dsimp only [evaluation, Functor.comp_map] at hcoord ⊢
        rw [reassoc_of% hcoord]
      _ = _ := by
        by_cases h : j = n.as
        · subst j
          simp only [Sigma.ι_π_eq_id]
          ext x
          simp only [Functor.comp_obj, CategoryTheory.Functor.map_id, Functor.comp_map,
            Category.id_comp, Iso.inv_hom_id, ModuleCat.hom_id, LinearMap.id_coe, id_eq,
            Int.natCast_add, Int.cast_ofNat_Int, ModuleCat.of_coe, ModuleCat.hom_comp,
            ConcreteCategory.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
            DirectSum.coeFnLinearMap_apply]
          change x = ((DirectSum.lof R ℕ (fun i ↦ M i) n.as) x) n.as
          exact (DirectSum.lof_apply (M := fun i ↦ M i) R n.as x).symm
        · simp only [Sigma.ι_π_of_ne _ h, Functor.map_zero, comp_zero, zero_comp]
          ext x
          change 0 = ((DirectSum.lof R ℕ (fun i ↦ M i) j) x) n.as
          exact (DirectSum.of_eq_of_ne (β := fun i ↦ M i) j n.as x (Ne.symm h)).symm
  have hn := directSum_not_surjective M hF
  have hnp : ¬ PreservesColimitsOfShape (Discrete ℕ) T := by
    intro h
    let := h
    have : IsIso (ModuleCat.ofHom (DirectSum.coeFnLinearMap R (M := fun n ↦ M n))) := by
      rw [← hc]
      infer_instance
    exact hn (ConcreteCategory.bijective_of_isIso
      (ModuleCat.ofHom (DirectSum.coeFnLinearMap R (M := fun n ↦ M n)))).2
  have hnl : ¬ T.IsLeftAdjoint := by
    intro h
    let := h
    exact hnp inferInstance
  have hJ (J : ModuleCat.{max r m} R) (hj : Injective J) (hcJ : IsCoseparator J) :
      Injective (v.obj J) ∧ ∀ n : ℕ,
        Function.Bijective (injectiveHomMap e T a F n J) ∧
        Nontrivial (cohomology e T F n ⟶ J) ∧
        Nontrivial (T.obj (shifts F n) ⟶ (singleFunctor B 0).obj (v.obj J)) := by
    let := hj
    refine ⟨a.map_injective J hj, fun n ↦ ⟨injectiveHomMap_bijective e T v a F n J, ?_⟩⟩
    have hm : Nontrivial (cohomology e T F n ⟶ J) := by
      apply not_subsingleton_iff_nontrivial.mp
      intro h
      apply hF n
      exact (IsZero.iff_id_eq_zero _).mpr (hcJ.def _ _ (fun f ↦ h.elim _ _))
    refine ⟨hm, ?_⟩
    exact (Equiv.ofBijective _ (injectiveHomMap_bijective e T v a F n J)).nontrivial
  have hplus : ¬ Tplus.IsLeftAdjoint := by
    intro h
    let := h
    let ad := Adjunction.ofIsLeftAdjoint Tplus
    obtain ⟨J, hj, hcJ⟩ := Abelian.has_injective_coseparator
      (ModuleCat.of R (Shrink.{max r m} R)) (ModuleCat.isSeparator R)
    let I := (DerivedCategory.Plus.singleFunctor B 0).obj (v.obj J)
    let L := Tplus.rightAdjoint.obj I
    obtain ⟨k, hk⟩ := L.property
    let := hk
    let n : ℕ := (-k).toNat
    let P := ((DerivedCategory.Plus.singleFunctor A 0).obj F)⟦((n + 1 : ℕ) : ℤ)⟧
    let ki : DerivedCategory.Plus.ι.obj P ≅ shifts F n :=
      (DerivedCategory.Plus.ι.commShiftIso ((n + 1 : ℕ) : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor A 0).obj F)
    have hs : (DerivedCategory.TStructure.t (C := A)).IsLE (shifts F n)
        (-((n + 1 : ℕ) : ℤ)) :=
      DerivedCategory.TStructure.t.isLE_shift ((singleFunctor A 0).obj F) 0
        ((n + 1 : ℕ) : ℤ) (-((n + 1 : ℕ) : ℤ)) (by omega)
    let := hs
    have hp := DerivedCategory.TStructure.t.isLE_of_iso ki.symm (-((n + 1 : ℕ) : ℤ))
    let := hp
    have hzero (g : P ⟶ L) : g = 0 := by
      apply DerivedCategory.Plus.ι.map_injective
      rw [Functor.map_zero]
      exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE
        (DerivedCategory.Plus.ι.map g) (-((n + 1 : ℕ) : ℤ)) k
        (by dsimp [n]; omega) inferInstance hk
    let ti : DerivedCategory.Plus.ι.obj (Tplus.obj P) ≅ T.obj (shifts F n) :=
      compatibility.app P ≪≫ T.mapIso ki
    have hnt := (hJ J hj hcJ).2 n |>.2.2
    let := hnt
    obtain ⟨f, hf⟩ := exists_ne
      (0 : T.obj (shifts F n) ⟶ (singleFunctor B 0).obj (v.obj J))
    let g : Tplus.obj P ⟶ I := DerivedCategory.Plus.ι.preimage (ti.hom ≫ f)
    have hg : g = 0 := (ad.homEquiv P I).injective
      ((hzero _).trans (hzero _).symm)
    have hg' : ti.hom ≫ f = 0 := by
      calc
        ti.hom ≫ f = DerivedCategory.Plus.ι.map g :=
          (Functor.map_preimage (X := Tplus.obj P) (Y := I)
            DerivedCategory.Plus.ι (ti.hom ≫ f)).symm
        _ = 0 := by rw [hg, Functor.map_zero]
    exact hf ((cancel_epi ti.hom).mp (by simpa only [comp_zero] using hg'))
  exact ⟨⟨hK⟩, ⟨α, β, hα, hβ, hc⟩, hn, hnp, hnl, hplus, hJ⟩

end DerivedCategory.UnboundedCohomologyObstruction
