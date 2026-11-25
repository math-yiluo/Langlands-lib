/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit

/-!
# Derived limits of surjective towers on the small pro-etale site

`n: ℕ` denotes positive level `n + 1`. Products and inverse limits are the existing
Mathlib constructions. The derived product is asserted to exist and the Roos assertion
works for every choice of its limit structure, without an existence hypothesis.

## Main declarations

* `surjectiveTower_hasSheafify` and `surjectiveTower_wEqualsLocallyBijective` transport
  Mathlib's sheafification structures to larger coefficient universes.
* `proEtale_surjectiveTower_derivedLimit` states the short exact Roos sequence, its
  derived-limit triangle, and uniqueness of compatible lifts from degree-zero sheaves.

## References

* Bhatt--Scholze, Proposition 3.1.10, Proposition 3.2.3(1), and Proposition 4.2.8
* Stacks Project, Tags 07KC, 08TC, and 06XS
* Bhatt--Scholze, Proposition 3.1.10 (sign changed to `1 - s`), Proposition 3.2.3(1), and
  Proposition 4.2.8
-/

@[expose] public section

set_option autoImplicit false

universe t u w v v'

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace AlgebraicGeometry.ProEtale

/-- Weak contractibility is unchanged by enlarging the universe of sections.
Choose one local lift for each arrow of the image sieve of a fixed section.
The coproduct of the corresponding representables is a small presheaf mapping
locally surjectively to the representable of W. Sheafify, apply weak contractibility,
and map the resulting section to the original sheaf, using compatibility of
sheafification with universe lifting. -/
private theorem large_section_surjective
    {C : Type v} [Category.{v'} C] (J : GrothendieckTopology C) (W : C)
    (hW : ∀ (F G : Sheaf J (Type (max v v'))) (f : F ⟶ G),
      Epi f → Function.Surjective (f.hom.app (op W)))
    (F G : Sheaf J (Type (max u v v'))) (e : F ⟶ G)
    [Sheaf.IsLocallySurjective e] : Function.Surjective (e.hom.app (op W)) := by
  classical
  intro x
  let S := Presheaf.imageSieve e.hom x
  let P : Cᵒᵖ ⥤ Type (max v v') :=
    { obj := fun V ↦ Σ (Z : C) (g : Z ⟶ W), {h : V.unop ⟶ Z // S g}
      map := fun a ↦ TypeCat.ofHom (fun z ↦
        ⟨z.1, z.2.1, a.unop ≫ z.2.2.val, z.2.2.property⟩)
      map_id := by intros; apply ConcreteCategory.hom_ext; intro z; simp
      map_comp := by intros; apply ConcreteCategory.hom_ext; intro z; simp [Category.assoc] }
  let Q := uliftYoneda.{v}.obj W
  let b : P ⟶ Q :=
    { app := fun _ ↦ TypeCat.ofHom (fun z ↦ ⟨z.2.2.val ≫ z.2.1⟩)
      naturality := by
        intros
        apply ConcreteCategory.hom_ext
        intro z
        simp [P, Q, Category.assoc] }
  have hb : Presheaf.IsLocallySurjective J b := by
    constructor
    intro V a
    apply J.superset_covering (S := S.pullback a.down)
    · intro Z g hg
      exact ⟨⟨Z, g ≫ a.down, 𝟙 Z, hg⟩, by simp [b, Q]⟩
    · exact J.pullback_stable a.down (Presheaf.imageSieve_mem J e.hom x)
  let bS : (⟨J.sheafify P, J.sheafify_isSheaf P⟩ : Sheaf J (Type (max v v'))) ⟶
      ⟨J.sheafify Q, J.sheafify_isSheaf Q⟩ := ⟨J.sheafifyMap b⟩
  have : Epi bS := by
    have : Sheaf.IsLocallySurjective bS := by
      change Presheaf.IsLocallySurjective J (J.sheafifyMap b)
      have : Presheaf.IsLocallySurjective J (b ≫ J.toSheafify Q) := inferInstance
      rw [J.toSheafify_naturality] at this
      exact Presheaf.isLocallySurjective_of_isLocallySurjective J (J.toSheafify P)
        (J.sheafifyMap b)
    infer_instance
  obtain ⟨z, hz⟩ := hW _ _ bS inferInstance ((J.toSheafify Q).app (op W) ⟨𝟙 W⟩)
  let L := uliftFunctor.{u, max v v'}
  let a : P ⋙ L ⟶ F.obj :=
    { app := fun V ↦ TypeCat.ofHom (fun z ↦ F.obj.map z.down.2.2.val.op
        (Presheaf.localPreimage e.hom x z.down.2.1 z.down.2.2.property))
      naturality := by intros; ext z; simp [L, P, Functor.map_comp] }
  let q : Q ⋙ L ⟶ G.obj :=
    { app := fun _ ↦ TypeCat.ofHom (fun z ↦ G.obj.map z.down.down.op x)
      naturality := by intros; ext z; simp [L, Q, Functor.map_comp] }
  have ha : a ≫ e.hom = Functor.whiskerRight b L ≫ q := by
    ext V z
    dsimp [a, q, b, L, Q]
    rw [NatTrans.naturality_apply, Presheaf.app_localPreimage]
    simp [Functor.map_comp]
  let aS := (J.sheafifyCompIso L P).hom ≫ J.sheafifyLift a F.property
  let qS := (J.sheafifyCompIso L Q).hom ≫ J.sheafifyLift q G.property
  have hS : aS ≫ e.hom = Functor.whiskerRight (J.sheafifyMap b) L ≫ qS := by
    have hn := (J.sheafificationWhiskerRightIso L).hom.naturality b
    change Functor.whiskerRight (J.sheafifyMap b) L ≫ (J.sheafifyCompIso L Q).hom =
      (J.sheafifyCompIso L P).hom ≫ J.sheafifyMap (Functor.whiskerRight b L) at hn
    dsimp only [aS, qS]
    rw [← Category.assoc, hn]
    simp only [Category.assoc, J.sheafifyMap_sheafifyLift]
    rw [← ha]
    congr 1
    apply J.sheafify_hom_ext _ _ G.property
    simp
  refine ⟨aS.app (op W) ⟨z⟩, ?_⟩
  have hh := congrArg (fun k ↦ k.app (op W) ⟨z⟩) hS
  change e.hom.app (op W) (aS.app (op W) ⟨z⟩) = _ at hh
  rw [hh]
  change qS.app (op W) ⟨bS.hom.app (op W) z⟩ = x
  rw [hz]
  have hq : Functor.whiskerRight (J.toSheafify Q) L ≫ qS = q := by
    dsimp only [qS]
    rw [← Category.assoc, J.whiskerRight_toSheafify_sheafifyCompIso_hom,
      J.toSheafify_sheafifyLift]
  have := congrArg (fun k ↦ k.app (op W) ⟨⟨𝟙 W⟩⟩) hq
  simpa [q, L, Q] using this

set_option backward.isDefEq.respectTransparency false in
private theorem roos_zero {A : Type*} [Category A] [Preadditive A]
    (F : ℕ → A) [HasProduct F] (t : ∀ n, F (n + 1) ⟶ F n)
    [HasLimit (Functor.ofOpSequence t)] :
    (Pi.lift (f := F) (fun n ↦ (limit.π (Functor.ofOpSequence t) (op n) : _ ⟶ F n))) ≫
      towerTransitionEndomorphism (K := F) t = 0 := by
  apply Pi.hom_ext
  intro n
  have hn := limit.w (Functor.ofOpSequence t) (homOfLE (Nat.le_succ n)).op
  simp only [Functor.ofOpSequence_map_homOfLE_succ] at hn
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
    Preadditive.sub_comp, Category.comp_id, Category.assoc, Pi.lift_comp_π,
    Pi.lift_comp_π_assoc, zero_comp]
  exact sub_eq_zero.mpr hn.symm

set_option backward.isDefEq.respectTransparency false in
private noncomputable def roos_kernel {A : Type*} [Category A] [Preadditive A]
    (F : ℕ → A) [HasProduct F] (t : ∀ n, F (n + 1) ⟶ F n)
    [HasLimit (Functor.ofOpSequence t)] :
    IsLimit (KernelFork.ofι
      (Pi.lift (f := F) (fun n ↦
        (limit.π (Functor.ofOpSequence t) (op n) : _ ⟶ F n))) (roos_zero F t)) := by
  apply Fork.IsLimit.mk'
  intro s
  let k := s.ι
  have hk : k ≫ towerTransitionEndomorphism (K := F) t = 0 := by simp [k]
  let W := s.pt
  let c : Cone (Functor.ofOpSequence t) :=
    { pt := W
      π := NatTrans.ofOpSequence (fun n ↦ k ≫ Pi.π F n) (by
        intro n
        have h := congrArg (fun a ↦ a ≫ Pi.π F n) hk
        have h' : k ≫ Pi.π F n - k ≫ Pi.π F (n + 1) ≫ t n = 0 := by
          simpa [towerTransitionEndomorphism, towerProductShift, Category.assoc] using h
        simpa using (sub_eq_zero.mp h')) }
  refine ⟨limit.lift _ c, ?_, ?_⟩
  · apply Pi.hom_ext
    intro n
    simp [c, k]
  · intro m hm
    apply limit.hom_ext (F := Functor.ofOpSequence t)
    rintro ⟨n⟩
    have h := congrArg (fun a ↦ a ≫ Pi.π F n) hm
    simpa [c, Category.assoc] using h

/-- Recursively lift coordinates of `1 - s`, starting with the zero coordinate. -/
private theorem roos_sections_surjective
    {A : Type*} [Category A] [Preadditive A]
    {B : Type*} [Ring B] (E : A ⥤ ModuleCat B) [E.Additive]
    (F : ℕ → A) [HasProduct F]
    [PreservesLimit (Discrete.functor F) (E ⋙ CategoryTheory.forget _)]
    (t : ∀ n, F (n + 1) ⟶ F n)
    (ht : ∀ n, Function.Surjective (E.map (t n))) :
    Function.Surjective (E.map (towerTransitionEndomorphism t)) := by
  classical
  intro y
  choose σ hσ using ht
  let x : ∀ n, E.obj (F n) :=
    fun n ↦ Nat.rec (0 : E.obj (F 0))
      (fun n a ↦ σ n (a - E.map (Pi.π F n) y)) n
  let T := E ⋙ CategoryTheory.forget _
  let e := Types.isLimitEquivSections
    (isLimitOfPreserves T (limit.isLimit (Discrete.functor F)))
  let s : (Discrete.functor F ⋙ T).sections :=
    ⟨fun j ↦ x j.as, by
      rintro ⟨i⟩ ⟨j⟩ a
      obtain rfl := Discrete.eq_of_hom a
      have ha : a = 𝟙 _ := Subsingleton.elim _ _
      subst a
      simp⟩
  refine ⟨e.symm s, ?_⟩
  apply e.injective
  apply Subtype.ext
  funext j
  have hx (n : ℕ) : E.map (Pi.π F n) (e.symm s) = x n :=
    congrArg (fun z ↦ z.val ⟨n⟩) (e.apply_symm_apply s)
  change E.map (Pi.π F j.as) (E.map (towerTransitionEndomorphism t) (e.symm s)) =
    E.map (Pi.π F j.as) y
  rw [← ModuleCat.comp_apply, ← E.map_comp]
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_comp_π, E.map_sub, E.map_comp, ModuleCat.hom_sub, LinearMap.sub_apply,
    ModuleCat.comp_apply, hx]
  change x j.as - E.map (t j.as) (x (j.as + 1)) = _
  rw [show x (j.as + 1) = σ j.as (x j.as - E.map (Pi.π F j.as) y) from rfl, hσ]
  exact sub_sub_cancel _ _

set_option backward.isDefEq.respectTransparency false in
private theorem roos_epi
    (Y : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (F : ℕ → ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    (t : ∀ n, F (n + 1) ⟶ F n) (ht : ∀ n, Epi (t n)) :
    Epi (towerTransitionEndomorphism t) := by
  let X : Scheme := Y
  let J := Scheme.ProEt.topology X
  let A := (sheafCompose J
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  let T := SheafOfModules.toSheaf.{max u (t + 1)} A ⋙
    sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})
  have hlocal (n : ℕ) : Sheaf.IsLocallySurjective (T.map (t n)) := by
    have : Epi (t n) := ht n
    let g := (SheafOfModules.toSheaf A).map (t n)
    have : Sheaf.IsLocallySurjective g :=
      (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{max u (t + 1)} g).mpr
        inferInstance
    change Sheaf.IsLocallySurjective
      ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)})).map g)
    infer_instance
  have : Sheaf.IsLocallySurjective (T.map (towerTransitionEndomorphism t)) := by
    constructor
    intro U s
    obtain ⟨K, V, a, hcov, _, hweak⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family Y U
    apply J.superset_covering (S := Sieve.ofArrows V a) _
      (Precoverage.generate_mem_toGrothendieck hcov)
    apply (Sieve.generate_le_iff _ _).mpr
    intro W g hg
    obtain ⟨k⟩ := hg
    let E := SheafOfModules.evaluation.{max u (t + 1)} A (op (V k))
    have : E.Additive := ⟨by intros; rfl⟩
    have hs (n : ℕ) : Function.Surjective (E.map (t n)) := by
      change Function.Surjective ((T.map (t n)).hom.app (op (V k)))
      exact large_section_surjective (C := X.ProEt) (J := J) (W := V k)
        (hW := hweak k) (T.obj (F (n + 1))) (T.obj (F n)) (T.map (t n))
    exact roos_sections_surjective E F t hs
      ((T.obj (∏ᶜ F)).obj.map (a k).op s)
  exact T.epi_of_epi_map inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem exact_countable_products
    (Y : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)}) :
    CountableAB4Star (ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)) := by
  let A := ringedSiteModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
  constructor
  intro I _
  have : (lim : (Discrete I ⥤ A) ⥤ A).PreservesEpimorphisms := by
    constructor
    intro B C f hf
    let eB := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))
    let eC := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := C))
    have h (i : I) : Epi (f.app ⟨i⟩) := inferInstance
    have : Epi (Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩)) :=
      (Scheme.ProEt.countableProducts_exact Y R).2.2 I _ _ _ h
    have hh : lim.map f = eB.hom ≫ Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ eC.inv := by
      apply limit.hom_ext
      rintro ⟨i⟩
      dsimp only [eB, eC]
      simp only [Category.assoc, HasLimit.isoOfNatIso_inv_π,
        Discrete.natIsoFunctor_inv_app]
      change lim.map f ≫ limit.π C ⟨i⟩ =
        (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))).hom ≫
          Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ Pi.π _ i
      rw [Pi.map_π, HasLimit.isoOfNatIso_hom_π_assoc]
      simp
    rw [hh]
    infer_instance
  exact hasExactLimitsOfShape_of_preservesEpi (C := A) (Discrete I)

set_option backward.isDefEq.respectTransparency false in
/-- Exact countable products identify the degree-zero product with a derived product. -/
private theorem single_product
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [CountableAB4Star A] (F : ℕ → A) :
    Nonempty (IsLimit (Fan.mk ((DerivedCategory.singleFunctor.{w} A 0).obj (∏ᶜ F))
      (fun n ↦ (DerivedCategory.singleFunctor.{w} A 0).map (Pi.π F n)))) := by
  let C := HomologicalComplex.single A (ComplexShape.up ℤ) 0
  let Q := DerivedCategory.Q (C := A)
  obtain ⟨hP, hproducts, _⟩ := derivedCategory_countableProducts_and_towerLimit A
  have hQ : PreservesLimit (Discrete.functor (fun n ↦ C.obj (F n))) Q :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hproducts _ _).some
  have : PreservesLimit (Discrete.functor F ⋙ C) Q :=
    (preservesLimit_iff_of_iso_diagram Q (Discrete.compNatIsoDiscrete F C)).mpr hQ
  have : PreservesLimit (Discrete.functor F) C := inferInstance
  have hcomp : PreservesLimit (Discrete.functor F) (C ⋙ Q) := inferInstance
  have hcomp' : PreservesLimit (Discrete.functor F)
      (CochainComplex.singleFunctor A 0 ⋙ DerivedCategory.Q) := by
    change PreservesLimit (Discrete.functor F) (C ⋙ Q)
    exact hcomp
  have hS : PreservesLimit (Discrete.functor F) (DerivedCategory.singleFunctor.{w} A 0) :=
    (preservesLimit_iff_of_natIso (Discrete.functor F)
      (DerivedCategory.singleFunctorIsoCompQ A 0)).mpr hcomp'
  let hc := isLimitOfPreserves (DerivedCategory.singleFunctor.{w} A 0)
    (limit.isLimit (Discrete.functor F))
  let hc' := (IsLimit.postcomposeHomEquiv
    (Discrete.compNatIsoDiscrete F (DerivedCategory.singleFunctor.{w} A 0)) _).symm hc
  exact ⟨IsLimit.ofIsoLimit hc' (Cone.ext (Iso.refl _) (by intro ⟨n⟩; simp))⟩

/-- An additive functor transports the tower endomorphism along a product comparison. -/
private theorem map_towerTransitionEndomorphism_comp_comparison
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (S : A ⥤ B) [S.Additive] (F : ℕ → A) [HasProduct F]
    [HasProduct (fun n ↦ S.obj (F n))] (t : ∀ n, F (n + 1) ⟶ F n)
    (e : S.obj (∏ᶜ F) ⟶ ∏ᶜ (fun n ↦ S.obj (F n)))
    (he : ∀ n, e ≫ Pi.π (fun n ↦ S.obj (F n)) n = S.map (Pi.π F n)) :
    S.map (towerTransitionEndomorphism t) ≫ e =
      e ≫ towerTransitionEndomorphism (fun n ↦ S.map (t n)) := by
  apply Pi.hom_ext
  intro n
  have h₁ := (towerTransitionEndomorphism_eq_iff t _).mp rfl n
  have h₂ := (towerTransitionEndomorphism_eq_iff
    (K := fun n ↦ S.obj (F n)) (fun n ↦ S.map (t n)) _).mp rfl n
  simp only [Category.assoc, he]
  rw [← S.map_comp, h₁, S.map_sub, S.map_comp, h₂]
  simp only [Preadditive.comp_sub, he]
  exact congrArg (fun q ↦ S.map (Pi.π F n) - q)
    ((congrArg (fun q ↦ q ≫ S.map (t n)) (he (n + 1))).symm.trans
      (Category.assoc _ _ _))

-- Preserve the original name of the product-instance binder, used only by typeclass search.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- A surjective tower of module sheaves has its ordinary limit as a derived limit,
with its canonical projections and the triangle of its short exact Roos sequence.
-/
theorem proEtale_surjectiveTower_derivedLimit
    (Y : Scheme.{t})
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    [HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))]
    (F : ℕ → ringedSiteModules.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
    (t : ∀ n : ℕ, F (n + 1) ⟶ F n) (ht : ∀ n : ℕ, Epi (t n)) :
    ∃ (hzero :
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) ≫
          towerTransitionEndomorphism t = 0)
      (hSES : (ShortComplex.mk
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n)))
        (towerTransitionEndomorphism t) hzero).ShortExact),
      Epi (towerTransitionEndomorphism t) ∧
      Nonempty (IsLimit (KernelFork.ofι
        (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) hzero)) ∧
      Nonempty (IsLimit (Fan.mk ((DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F))
        (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.π F n)))) ∧
      hSES.singleTriangle ∈ distTriang _ ∧
      (∀ [hprod : HasProduct (fun n : ℕ ↦
          (DerivedCategory.singleFunctor.{w} _ 0).obj (F n))],
        ∃ e : (DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F) ≅
            ∏ᶜ (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n)),
          (∀ n : ℕ, e.hom ≫
              Pi.π (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n)) n =
            (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.π F n)) ∧
          IsDerivedLimitTriangle
            (K := fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).obj (F n))
            (fun n : ℕ ↦ (DerivedCategory.singleFunctor.{w} _ 0).map (t n))
            ((DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)))
            ((DerivedCategory.singleFunctor.{w} _ 0).map
              (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) ≫ e.hom)
            (e.inv ≫ hSES.singleδ)) ∧
      (∀ (G : ringedSiteModules.{max u (t + 1)}
          ((sheafCompose (Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R))
        (g : ∀ n : ℕ, G ⟶ F n), (∀ n : ℕ, g (n + 1) ≫ t n = g n) →
        ∃ (h₀ : G ⟶ limit (Functor.ofOpSequence t)),
          (∀ n : ℕ, h₀ ≫ limit.π (Functor.ofOpSequence t) (op n) = g n) ∧
          (∃! h : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
              (DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)),
            h ≫ (DerivedCategory.singleFunctor.{w} _ 0).map
                (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) =
              (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.lift g)) ∧
          (∀ h : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
              (DerivedCategory.singleFunctor.{w} _ 0).obj (limit (Functor.ofOpSequence t)),
            h ≫ (DerivedCategory.singleFunctor.{w} _ 0).map
                (Pi.lift (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))) =
              (DerivedCategory.singleFunctor.{w} _ 0).map (Pi.lift g) →
            h = (DerivedCategory.singleFunctor.{w} _ 0).map h₀) ∧
          (∀ k : (DerivedCategory.singleFunctor.{w} _ 0).obj G ⟶
            ((DerivedCategory.singleFunctor.{w} _ 0).obj (∏ᶜ F))⟦(-1 : ℤ)⟧, k = 0)) := by
  classical
  let A := ringedSiteModules.{max u (t + 1)}
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R)
  let S := DerivedCategory.singleFunctor.{w} A 0
  let i : limit (Functor.ofOpSequence t) ⟶ ∏ᶜ F :=
    Pi.lift (f := F) (fun n : ℕ ↦ limit.π (Functor.ofOpSequence t) (op n))
  have hz : i ≫ towerTransitionEndomorphism t = 0 := roos_zero F t
  let hk := roos_kernel F t
  have hmono : Mono i := mono_of_isLimit_fork hk
  have hepi : Epi (towerTransitionEndomorphism t) := roos_epi Y R F t ht
  let sc := ShortComplex.mk i (towerTransitionEndomorphism t) hz
  have hSES : sc.ShortExact :=
    ShortComplex.ShortExact.mk' (sc.exact_of_f_is_kernel hk) hmono hepi
  have : CountableAB4Star A := exact_countable_products Y R
  have hp0 : Nonempty (IsLimit (Fan.mk (S.obj (∏ᶜ F))
      (fun n : ℕ ↦ S.map (Pi.π F n)))) := single_product F
  obtain ⟨hp⟩ := hp0
  refine ⟨hz, hSES, hepi, ⟨hk⟩, ⟨hp⟩, hSES.singleTriangle_distinguished, ?_, ?_⟩
  · intro hprod
    let e := hp.conePointUniqueUpToIso (limit.isLimit _)
    have he (n : ℕ) : e.hom ≫ Pi.π (fun n ↦ S.obj (F n)) n = S.map (Pi.π F n) :=
      hp.conePointUniqueUpToIso_hom_comp _ ⟨n⟩
    refine ⟨e, he, ?_⟩
    have htrans : S.map (towerTransitionEndomorphism t) ≫ e.hom =
        e.hom ≫ towerTransitionEndomorphism (fun n ↦ S.map (t n)) := by
      exact map_towerTransitionEndomorphism_comp_comparison S F t e.hom he
    let T := Pretriangulated.Triangle.mk (S.map i ≫ e.hom)
      (towerTransitionEndomorphism (K := fun n ↦ S.obj (F n)) (fun n ↦ S.map (t n)))
      (e.inv ≫ hSES.singleδ)
    have eT : hSES.singleTriangle ≅ T := by
      refine Pretriangulated.Triangle.isoMk hSES.singleTriangle T (Iso.refl _) e e
        ?_ ?_ ?_
      · change S.map i ≫ e.hom = 𝟙 _ ≫ (S.map i ≫ e.hom)
        simp only [Category.id_comp]
      · exact htrans
      · change hSES.singleδ ≫ (𝟙 _)⟦(1 : ℤ)⟧' = e.hom ≫ (e.inv ≫ hSES.singleδ)
        rw [Iso.hom_inv_id_assoc]
        exact (congrArg (fun q ↦ hSES.singleδ ≫ q)
          ((shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id _)).trans (Category.comp_id _)
    exact Pretriangulated.isomorphic_distinguished _ hSES.singleTriangle_distinguished T eT.symm
  · intro G g hg
    let c : Cone (Functor.ofOpSequence t) :=
      ⟨G, NatTrans.ofOpSequence g (by intro n; simpa using (hg n).symm)⟩
    let h₀ := limit.lift _ c
    have hproj (n : ℕ) : h₀ ≫ limit.π (Functor.ofOpSequence t) (op n) = g n :=
      limit.lift_π c (op n)
    have htuple : h₀ ≫ i = Pi.lift g := by
      apply Pi.hom_ext
      intro n
      simp [i, hproj]
    have huniq (h : S.obj G ⟶ S.obj (limit (Functor.ofOpSequence t)))
        (hh : h ≫ S.map i = S.map (Pi.lift g)) : h = S.map h₀ := by
      obtain ⟨a, rfl⟩ := S.map_surjective h
      congr 1
      apply limit.hom_ext
      rintro ⟨n⟩
      have ha : a ≫ i = Pi.lift g := S.map_injective (by simpa using hh)
      have han := congrArg (fun q ↦ q ≫ Pi.π F n) ha
      simpa [i, Category.assoc, hproj] using han
    refine ⟨h₀, hproj, ⟨S.map h₀, ?_, huniq⟩, huniq, ?_⟩
    · change S.map h₀ ≫ S.map i = S.map (Pi.lift g)
      rw [← S.map_comp, htuple]
    · intro k
      exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE k 0 1 (by decide)
        inferInstance (DerivedCategory.TStructure.t.isGE_shift (S.obj (∏ᶜ F)) 0 (-1) 1)

end AlgebraicGeometry.ProEtale
