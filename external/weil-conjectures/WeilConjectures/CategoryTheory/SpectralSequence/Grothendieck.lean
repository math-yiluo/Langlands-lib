/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralObject.SpectralSequence
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.SpectralObject
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-!
# The Grothendieck spectral sequence

Let `A ⥤ B ⥤ C` be left exact additive functors such that `F` sends injective objects of `A` to
`G`-acyclic objects of `B`. Then for every `X : A` there is a first quadrant cohomological
spectral sequence with `E₂`-page `R^p G (R^q F X)` abutting to `R^{p + q} (F ⋙ G) X`.

Convergence is expressed through `CategoryTheory.SpectralSequence.AbutsTo` of
`WeilConjectures/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`; the blueprint's
`det-def-groth-ss` describes both the acyclicity hypothesis on the pair `(F, G)` and the image
filtration attached to a first quadrant double complex, and the second half of that subsection
is what `SpectralSequence.Abutment` records.

## The construction

The blueprint builds the spectral sequence from a Cartan–Eilenberg resolution of `F(I)`, `I` an
injective resolution of `X`. We use instead the equivalent construction through the canonical
t-structure on the bounded below derived category `D⁺(B)`, for which Mathlib provides spectral
objects and their spectral sequences. Let `K = RF(X) = R⁺F(X[0]) ∈ D⁺(B)`. To `a ≤ b` in `EInt`
and `n : ℤ` we attach `Hⁿ(RG(τ_{≥ a} τ_{< b} K))`; this is a first quadrant spectral object in
`C` (`Functor.grothendieckSpectralObject`), whose `E₂` spectral sequence is the Grothendieck
spectral sequence (`Functor.grothendieckSpectralSequence`). Its `E₂`-terms are
`H^{p+q}(RG(τ_{≥ q} τ_{< q+1} K)) = H^{p+q}(RG((R^q F X)[-q])) = R^p G (R^q F X)`, and it
converges to `Hⁿ(RG(K))`, which is `Hⁿ(G(F(I))) = R^n (F ⋙ G) X` because `F(I)` is a complex
of `G`-acyclic objects. The two filtrations of the Cartan–Eilenberg double complex in the
blueprint are replaced by the truncation filtration (giving the `E₂`-page) and the
identification of the abutment through acyclic resolutions.

## Main definitions

- `CategoryTheory.Functor.IsAcyclicComposablePair`: a composable pair with acyclicity.
- `CategoryTheory.Functor.grothendieckSpectralObjectFunctor`,
  `CategoryTheory.Functor.grothendieckSpectralObject`: the spectral object of the Grothendieck
  spectral sequence, functorially in `X`.
- `CategoryTheory.Functor.grothendieckSpectralSequence`: the Grothendieck spectral sequence.
- `CategoryTheory.Functor.grothendieckBottomEdge`, `CategoryTheory.Functor.grothendieckLeftEdge`:
  the edge maps `E₂^{n,0} ⟶ Hⁿ ⟶ E₂^{0,n}` of the spectral object, natural in `X`.
- `CategoryTheory.Functor.grothendieckSpectralObjectHIso`,
  `CategoryTheory.Functor.grothendieckSpectralObjectHBotTopIso`: the natural identifications
  of the `E₂`-terms with `R^p G (R^q F X)` and of the abutment with `R^n (F ⋙ G) X`.
- `CategoryTheory.Functor.grothendieckSpectralSequencePageTwoIso`: `E₂^{p,q} ≅ R^p G (R^q F X)`.
- `CategoryTheory.Functor.grothendieckBottomEdgeMap`,
  `CategoryTheory.Functor.grothendieckLeftEdgeMap`: the edge maps
  `R^n G (F X) ⟶ R^n (F ⋙ G) X ⟶ G (R^n F X)`, natural in `X`
  (`lem-sp-grothendieck-edge-maps`).
- `CategoryTheory.Functor.grothendieckE₂BaseChange`: the base change morphism
  `γ (R^p G (R^q F X)) ⟶ R^p G' (R^q F' (α X))` on `E₂`-terms.
- `CategoryTheory.Functor.grothendieckSpectralObjectBaseChange`: the base change morphism of the
  spectral objects of two Grothendieck spectral sequences related by exact functors.

## Main statements

- `CategoryTheory.Adjunction.isAcyclicComposablePair`: a right adjoint of an exact functor gives
  a composable pair with acyclicity.
- `CategoryTheory.Functor.nonempty_grothendieckSpectralSequence_page_two_iso`,
  `CategoryTheory.Functor.grothendieckSpectralSequence_abutsTo`: the `E₂`-page and the abutment.
- `CategoryTheory.Functor.exists_grothendieckSpectralSequence`: the Grothendieck spectral
  sequence of a composable pair with acyclicity.
- `CategoryTheory.Functor.exists_grothendieckSpectralObject_baseChange`: compatibility with base
  change along exact functors (`thm-sp-grothendieck-base-change`).
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits ComposableArrows

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [IsGrothendieckAbelian.{v₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [IsGrothendieckAbelian.{v₂} B]
  {C : Type u₃} [Category.{v₃} C] [Abelian C]

/-- The pair of additive functors `A ⥤ B ⥤ C` is a *composable pair with acyclicity* if `F` sends
every injective object `I` of `A` to a `G`-acyclic object of `B`, that is, one at which all the
higher right derived functors `R^q G` for `q > 0` vanish. This is what makes an injective
resolution of `X : A` compute `R^n (F ⋙ G) X` after applying `F`, and hence what makes the
Grothendieck spectral sequence of `Functor.exists_grothendieckSpectralSequence` exist.

(blueprint: `det-def-groth-ss`) -/
def Functor.IsAcyclicComposablePair (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive] : Prop :=
  ∀ (I : A) [Injective I] (q : ℕ), 0 < q → IsZero ((G.rightDerived q).obj (F.obj I))

omit [IsGrothendieckAbelian.{v₁} A] in
/-- If `F` preserves injective objects, then `(F, G)` is a composable pair with acyclicity, since
the higher right derived functors of `G` vanish on injective objects. -/
theorem Functor.isAcyclicComposablePair_of_preservesInjectiveObjects (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [F.PreservesInjectiveObjects] : F.IsAcyclicComposablePair G := by
  intro I _ q hq
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by lia⟩
  exact G.isZero_rightDerived_obj_injective_succ q (F.obj I)

omit [IsGrothendieckAbelian.{v₁} A] in
/-- **The acyclicity hypothesis for a right adjoint of an exact functor.** If `F : A ⥤ B` has a
left adjoint `u` which is exact (it is enough that `u` preserves finite limits), then `F` preserves
injective objects (`lem-sp-right-adjoint-preserves-injectives`), so `(F, G)` is a composable pair
with acyclicity for every `G`. This is the situation of `F = f_*`, `u = f⁻¹` for a morphism of
sites `f` (Step 1 of the proof of `det-thm-groth-ss`). -/
theorem Adjunction.isAcyclicComposablePair {u : B ⥤ A} {F : A ⥤ B} (adj : u ⊣ F)
    [PreservesFiniteLimits u] (G : B ⥤ C) [F.Additive] [G.Additive] :
    F.IsAcyclicComposablePair G :=
  have := adj.preservesInjectiveObjects_of_preservesFiniteLimits
  F.isAcyclicComposablePair_of_preservesInjectiveObjects G

namespace Functor

variable (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

variable [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]

/-- The object `RF(X) = R⁺F(X[0])` of `D⁺(B)` is cohomologically `≥ 0`. -/
instance (X : A) : DerivedCategory.Plus.TStructure.t.IsGE
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) 0 := by
  have : DerivedCategory.Plus.TStructure.t.IsGE
      (DerivedCategory.Plus.Q.obj (F.rightDerivedPlusComplex X)) 0 := by
    refine (DerivedCategory.Plus.isGE_ι_obj_iff _ 0).1 ?_
    have : (F.rightDerivedPlusComplex X).obj.IsStrictlyGE 0 :=
      inferInstanceAs (CochainComplex.IsStrictlyGE ((F.mapHomologicalComplex _).obj
        (injectiveResolution X).cochainComplex) 0)
    exact inferInstanceAs ((DerivedCategory.Q.obj (F.rightDerivedPlusComplex X).obj).IsGE 0)
  exact DerivedCategory.Plus.TStructure.t.isGE_of_iso
    (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X).symm 0

/-- The functor sending `X : A` to the spectral object in `C` whose spectral sequence is the
Grothendieck spectral sequence of `X`: to `a ≤ b` in `EInt` and `n : ℤ` it attaches
`H^n(RG(τ_{≥ a} τ_{< b} RF(X)))`, where `RF(X) = R⁺F(X[0])` and `τ` denotes the truncations for
the canonical t-structure on `D⁺(B)`. -/
noncomputable def grothendieckSpectralObjectFunctor : A ⥤ Abelian.SpectralObject C EInt :=
  DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
    DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
    G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt ⋙
    (DerivedCategory.Plus.homologyFunctor C 0).mapHomologicalSpectralObject EInt

/-- The spectral object of the Grothendieck spectral sequence of `X : A`, see
`Functor.grothendieckSpectralObjectFunctor`. -/
noncomputable abbrev grothendieckSpectralObject (X : A) : Abelian.SpectralObject C EInt :=
  (F.grothendieckSpectralObjectFunctor G).obj X

instance (X : A) : (F.grothendieckSpectralObject G X).IsFirstQuadrant where
  isZero₁ i j hij hj n := by
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
    have := t.isZero_eTruncLT_obj_obj K 0 j hj
    change IsZero (((DerivedCategory.Plus.homologyFunctor C 0).shift n).obj
      (G.rightDerivedFunctorPlus.obj ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj K))))
    exact Functor.map_isZero _ (Functor.map_isZero _ (Functor.map_isZero _ this))
  isZero₂ i j hij n hi := by
    let t := DerivedCategory.Plus.TStructure.t (C := B)
    let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
    have := t.isGE_eTruncGE_obj_obj (n + 1) i (by
      induction i using WithBotTop.rec with
      | bot => simp at hi
      | coe i => simp at hi ⊢; lia
      | top => simp) ((t.eTruncLT.obj j).obj K)
    exact G.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      ((t.eTruncGE.obj i).obj ((t.eTruncLT.obj j).obj K)) (n + 1) (by lia)

/-- The Grothendieck spectral sequence of `X : A`, the first quadrant `E₂` spectral sequence of
the spectral object `Functor.grothendieckSpectralObject`. -/
noncomputable def grothendieckSpectralSequence (X : A) : E₂CohomologicalSpectralSequenceNat C :=
  (F.grothendieckSpectralObject G X).E₂SpectralSequenceNat

/-- The terms `H^{p+q}(RG(τ_{≥ q} τ_{< q+1} RF(X)))` of the spectral object of the Grothendieck
spectral sequence, which give its `E₂`-page, are `R^p G (R^q F X)`. Indeed
`τ_{≥ q} τ_{< q+1} RF(X) ≅ (R^q F X)[-q]`. -/
theorem nonempty_grothendieckSpectralObject_H_iso (X : A) (p q : ℕ) (n a b : ℤ)
    (hn : n = p + q) (ha : a = q) (hb : b = q + 1) :
    Nonempty (((F.grothendieckSpectralObject G X).H n).obj
        (mk₁ (homOfLE (show (a : EInt) ≤ b by simp [ha, hb]))) ≅
      (G.rightDerived p).obj ((F.rightDerived q).obj X)) := by
  subst hn ha hb
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  let H₀ := DerivedCategory.Plus.homologyFunctor C 0
  let M := (DerivedCategory.Plus.homologyFunctor B q).obj K
  obtain ⟨e₁⟩ := DerivedCategory.Plus.nonempty_eTruncGE_eTruncLT_iso_singleFunctor K q
  let e₂ : M ≅ (F.rightDerived q).obj X :=
    F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X q
  let e₃ := G.homologyRightDerivedFunctorPlusObjSingleFunctorIso M p
  let e₄ := ((DerivedCategory.Plus.singleFunctors B).shiftIso (-(q : ℤ)) q 0 (by simp)).app M
  let e₅ := (G.rightDerivedFunctorPlus.commShiftIso (-(q : ℤ))).app
    ((DerivedCategory.Plus.singleFunctor B 0).obj M)
  let e₆ := (H₀.shiftIso (-(q : ℤ)) ((p : ℤ) + q) p (by ring)).app
    (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj M))
  exact ⟨(H₀.shift ((p : ℤ) + q)).mapIso
    (G.rightDerivedFunctorPlus.mapIso (e₁ ≪≫ e₄.symm) ≪≫ e₅) ≪≫
    e₆ ≪≫ e₃ ≪≫ (G.rightDerived p).mapIso e₂⟩

/-- The `E₂`-page of the Grothendieck spectral sequence is `E₂^{p,q} = R^p G (R^q F X)`. -/
theorem nonempty_grothendieckSpectralSequence_page_two_iso (X : A) (p q : ℕ) :
    Nonempty (((F.grothendieckSpectralSequence G X).page 2).X (p, q) ≅
      (G.rightDerived p).obj ((F.rightDerived q).obj X)) := by
  obtain ⟨e⟩ := F.nonempty_grothendieckSpectralObject_H_iso G X p q (p + q : ℕ) q (q + 1)
    (by push_cast; rfl) rfl rfl
  exact ⟨(F.grothendieckSpectralObject G X).E₂SpectralSequenceNatPageTwoXIso p q ≪≫ e⟩

/-- For a composable pair with acyclicity, the term `Hⁿ(RG(RF(X)))` of the spectral object of
the Grothendieck spectral sequence, to which it abuts, is `R^n (F ⋙ G) X`. -/
theorem nonempty_grothendieckSpectralObject_H_bot_top_iso [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) (n : ℕ) :
    Nonempty (((F.grothendieckSpectralObject G X).H n).obj
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ ((F ⋙ G).rightDerived n).obj X) := by
  let t := DerivedCategory.Plus.TStructure.t (C := B)
  let K := F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)
  have hK : (t.eTruncGE.obj ⊥).obj ((t.eTruncLT.obj ⊤).obj K) = K := by
    rw [t.eTruncGE_obj_bot, t.eTruncLT_obj_top]
    rfl
  have hL (k : ℤ) : G.rightAcyclic ((F.rightDerivedPlusComplex X).obj.X k) :=
    fun q ↦ hFG _ (q + 1) (by lia)
  obtain ⟨e⟩ := G.nonempty_homology_rightDerivedFunctorPlus_obj_Q_iso _ hL n
  exact ⟨(DerivedCategory.Plus.homologyFunctor C n).mapIso
    (G.rightDerivedFunctorPlus.mapIso (eqToIso hK ≪≫
      F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X)) ≪≫ e ≪≫
      ((injectiveResolution X).isoRightDerivedObjCochainComplex (F ⋙ G) n).symm⟩

/-- The Grothendieck spectral sequence of a composable pair with acyclicity abuts to
`R^n (F ⋙ G) X`. -/
theorem grothendieckSpectralSequence_abutsTo [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) :
    (F.grothendieckSpectralSequence G X).AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X) :=
  (F.grothendieckSpectralObject G X).abutsTo_E₂SpectralSequenceNat.of_nonempty_iso
    (F.nonempty_grothendieckSpectralObject_H_bot_top_iso G hFG X)

/-- The *bottom edge map* `E₂^{n,0} ⟶ Hⁿ` of the Grothendieck spectral sequence, as a natural
transformation in `X : A`. Its source `H^n(RG(τ_{≥ 0} τ_{< 1} RF(X)))` is `R^n G (F X)` when `F`
is left exact (`Functor.grothendieckBottomEdgeSourceIso`) and its target `H^n(RG(RF(X)))` is
`R^n (F ⋙ G) X` for a composable pair with acyclicity
(`Functor.grothendieckSpectralObjectHBotTopIso`); through these natural identifications it
gives the blueprint edge map `Functor.grothendieckBottomEdgeMap`. It is the composite
`E₂^{n,0} ↠ E∞^{n,0} = Fⁿ Hⁿ ↪ Hⁿ`, its image being the last step of the abutment filtration
(`Abelian.SpectralObject.imageSubobject_bottomEdge`).

(blueprint: `lem-sp-grothendieck-edge-maps`) -/
noncomputable def grothendieckBottomEdge (n : ℤ) :
    F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (show ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) by simp))) ⟶
      F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) where
  app X := (F.grothendieckSpectralObject G X).bottomEdge n
  naturality _ _ f :=
    Abelian.SpectralObject.bottomEdge_naturality ((F.grothendieckSpectralObjectFunctor G).map f) n

/-- The *left edge map* `Hⁿ ⟶ E₂^{0,n}` of the Grothendieck spectral sequence, as a natural
transformation in `X : A`. Its source `H^n(RG(RF(X)))` is `R^n (F ⋙ G) X` for a composable pair
with acyclicity (`Functor.grothendieckSpectralObjectHBotTopIso`) and its target
`H^n(RG(τ_{≥ n} τ_{< n+1} RF(X)))` is `G (R^n F X)` when `G` is left exact
(`Functor.grothendieckLeftEdgeTargetIso`); through these natural identifications it gives the
blueprint edge map `Functor.grothendieckLeftEdgeMap`.

(blueprint: `lem-sp-grothendieck-edge-maps`) -/
noncomputable def grothendieckLeftEdge (n : ℤ) :
    F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ⟶
      F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (show ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt) by simp))) where
  app X := (F.grothendieckSpectralObject G X).leftEdge n
  naturality _ _ f :=
    Abelian.SpectralObject.leftEdge_naturality ((F.grothendieckSpectralObjectFunctor G).map f) n

/-- The source of the bottom edge map is `R^n G (F X)`. -/
theorem nonempty_grothendieckSpectralObject_H_zero_one_iso [PreservesFiniteLimits F] (X : A)
    (n : ℕ) :
    Nonempty (((F.grothendieckSpectralObject G X).H n).obj
        (mk₁ (homOfLE (show ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) by simp))) ≅
      (G.rightDerived n).obj (F.obj X)) := by
  obtain ⟨e⟩ := F.nonempty_grothendieckSpectralObject_H_iso G X n 0 n 0 1 (by simp) rfl rfl
  exact ⟨e ≪≫ (G.rightDerived n).mapIso (F.rightDerivedZeroIsoSelf.app X)⟩

/-- The target of the left edge map is `G (R^n F X)`. -/
theorem nonempty_grothendieckSpectralObject_H_self_succ_iso [PreservesFiniteLimits G] (X : A)
    (n : ℕ) :
    Nonempty (((F.grothendieckSpectralObject G X).H n).obj
        (mk₁ (homOfLE (show ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt) by simp))) ≅
      G.obj ((F.rightDerived n).obj X)) := by
  obtain ⟨e⟩ := F.nonempty_grothendieckSpectralObject_H_iso G X 0 n n n (n + 1) (by simp) rfl rfl
  exact ⟨e ≪≫ G.rightDerivedZeroIsoSelf.app _⟩

/-- The terms `H^{p+q}(RG(τ_{≥ q} τ_{< q+1} RF(X)))` of the spectral object of the
Grothendieck spectral sequence, which give its `E₂`-page, are `R^p G (R^q F X)`, naturally in
`X`. Indeed `τ_{≥ q} τ_{< q+1} RF(X) ≅ (R^q F X)[-q]` naturally in `X`
(`DerivedCategory.Plus.eTruncLTCompETruncGEIso`). -/
noncomputable def grothendieckSpectralObjectHIso (p q : ℕ) (n a b : ℤ) (hn : n = p + q)
    (ha : a = q) (hb : b = q + 1) :
    F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (show (a : EInt) ≤ b by simp [ha, hb]))) ≅
      F.rightDerived q ⋙ G.rightDerived p := by
  subst hn ha hb
  let S₀ := DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus
  let H₀ := DerivedCategory.Plus.homologyFunctor C 0
  let RG := G.rightDerivedFunctorPlus
  let Hq := DerivedCategory.Plus.homologyFunctor B q
  exact Functor.isoWhiskerLeft S₀ (Functor.isoWhiskerRight
      (DerivedCategory.Plus.eTruncLTCompETruncGEIso (q : ℤ)) (RG ⋙ H₀.shift ((p : ℤ) + q))) ≪≫
    Functor.isoWhiskerLeft (S₀ ⋙ Hq) (Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors B).shiftIso (-(q : ℤ)) q 0 (by simp)).symm
      (RG ⋙ H₀.shift ((p : ℤ) + q))) ≪≫
    Functor.isoWhiskerLeft (S₀ ⋙ Hq ⋙ DerivedCategory.Plus.singleFunctor B 0)
      (Functor.isoWhiskerRight (RG.commShiftIso (-(q : ℤ))) (H₀.shift ((p : ℤ) + q))) ≪≫
    Functor.isoWhiskerLeft (S₀ ⋙ Hq ⋙ DerivedCategory.Plus.singleFunctor B 0 ⋙ RG)
      (H₀.shiftIso (-(q : ℤ)) ((p : ℤ) + q) p (by ring)) ≪≫
    Functor.isoWhiskerLeft (S₀ ⋙ Hq)
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p) ≪≫
    Functor.isoWhiskerRight (F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q)
      (G.rightDerived p)

/-- The components of `Functor.grothendieckSpectralObjectHIso`. -/
lemma grothendieckSpectralObjectHIso_hom_app (p q : ℕ) (X : A) :
    (F.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1) (by push_cast; rfl) rfl
        rfl).hom.app X =
      (DerivedCategory.Plus.homologyFunctor C (p + q : ℕ)).map (G.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.eTruncLTCompETruncGEIso (q : ℤ)).hom.app
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) ≫
      (DerivedCategory.Plus.homologyFunctor C (p + q : ℕ)).map (G.rightDerivedFunctorPlus.map
        (((DerivedCategory.Plus.singleFunctors B).shiftIso (-(q : ℤ)) q 0 (by simp)).inv.app
          ((DerivedCategory.Plus.homologyFunctor B q).obj
            (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
      (DerivedCategory.Plus.homologyFunctor C (p + q : ℕ)).map
        ((G.rightDerivedFunctorPlus.commShiftIso (-(q : ℤ))).hom.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj
            ((DerivedCategory.Plus.homologyFunctor B q).obj
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
      ((DerivedCategory.Plus.homologyFunctor C 0).shiftIso (-(q : ℤ)) (p + q : ℕ) p
        (by push_cast; ring)).hom.app
          (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj
            ((DerivedCategory.Plus.homologyFunctor B q).obj
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
      (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).hom.app
        ((DerivedCategory.Plus.homologyFunctor B q).obj
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))) ≫
      (G.rightDerived p).map
        ((F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).hom.app X) := by
  simp only [grothendieckSpectralObjectHIso, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app, Iso.symm_hom,
    Functor.comp_map]
  rfl

/-- The `E₂`-page of the Grothendieck spectral sequence is `E₂^{p,q} ≅ R^p G (R^q F X)`. This
isomorphism is natural in `X`, see `Functor.grothendieckSpectralObjectHIso`. -/
noncomputable def grothendieckSpectralSequencePageTwoIso (X : A) (p q : ℕ) :
    ((F.grothendieckSpectralSequence G X).page 2).X (p, q) ≅
      (G.rightDerived p).obj ((F.rightDerived q).obj X) :=
  (F.grothendieckSpectralObject G X).E₂SpectralSequenceNatPageTwoXIso p q ≪≫
    (F.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1) (by push_cast; rfl) rfl
      rfl).app X

/-- For a composable pair with acyclicity, the term `Hⁿ(RG(RF(X)))` of the spectral object of
the Grothendieck spectral sequence, to which it abuts, is `R^n (F ⋙ G) X`, naturally in `X`:
this is the composition isomorphism `R⁺(F ⋙ G) ≅ R⁺F ⋙ R⁺G`
(`Functor.rightDerivedFunctorPlusCompIsoOfRightAcyclic`). -/
noncomputable def grothendieckSpectralObjectHBotTopIso [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (n : ℕ) :
    F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ (F ⋙ G).rightDerived n :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
      (Functor.isoWhiskerRight (F.rightDerivedFunctorPlusCompIsoOfRightAcyclic G
        (fun I _ q ↦ hFG I (q + 1) (by lia))).symm
      (DerivedCategory.Plus.homologyFunctor C n)) ≪≫
    (F ⋙ G).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n

/-- The source `E₂^{n,0}` of the bottom edge map is `R^n G (F X)`, naturally in `X`. -/
noncomputable def grothendieckBottomEdgeSourceIso [PreservesFiniteLimits F] (n : ℕ) :
    F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (show ((0 : ℤ) : EInt) ≤ ((1 : ℤ) : EInt) by simp))) ≅
      F ⋙ G.rightDerived n :=
  F.grothendieckSpectralObjectHIso G n 0 n 0 1 (by simp) (by simp) (by simp) ≪≫
    Functor.isoWhiskerRight F.rightDerivedZeroIsoSelf (G.rightDerived n)

/-- The target `E₂^{0,n}` of the left edge map is `G (R^n F X)`, naturally in `X`. -/
noncomputable def grothendieckLeftEdgeTargetIso [PreservesFiniteLimits G] (n : ℕ) :
    F.grothendieckSpectralObjectFunctor G ⋙ Abelian.SpectralObject.hFunctor n
        (mk₁ (homOfLE (show ((n : ℤ) : EInt) ≤ ((n + 1 : ℤ) : EInt) by simp))) ≅
      F.rightDerived n ⋙ G :=
  F.grothendieckSpectralObjectHIso G 0 n n n (n + 1) (by simp) rfl rfl ≪≫
    Functor.isoWhiskerLeft (F.rightDerived n) G.rightDerivedZeroIsoSelf

/-- **The bottom edge map** `R^n G (F X) ⟶ R^n (F ⋙ G) X` of the Grothendieck spectral
sequence, natural in `X`. It is the composite `E₂^{n,0} ↠ E∞^{n,0} = Fⁿ Hⁿ ↪ Hⁿ`
(`Functor.grothendieckBottomEdge`), read through the identifications
`E₂^{n,0} ≅ R^n G (F X)` and `Hⁿ ≅ R^n (F ⋙ G) X`.

For `F = f_*` and `G = h_*` along morphisms of sites `X ⟶ Y ⟶ Z`, this is the edge map
`R^n h_* (f_* 𝓕) ⟶ R^n (h ∘ f)_* 𝓕`.

(blueprint: `lem-sp-grothendieck-edge-maps`) -/
noncomputable def grothendieckBottomEdgeMap [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (n : ℕ) :
    F ⋙ G.rightDerived n ⟶ (F ⋙ G).rightDerived n :=
  (F.grothendieckBottomEdgeSourceIso G n).inv ≫ F.grothendieckBottomEdge G n ≫
    (F.grothendieckSpectralObjectHBotTopIso G hFG n).hom

/-- **The left edge map** `R^n (F ⋙ G) X ⟶ G (R^n F X)` of the Grothendieck spectral sequence,
natural in `X`. It is the composite `Hⁿ ↠ Hⁿ / F¹ Hⁿ = E∞^{0,n} ↪ E₂^{0,n}`
(`Functor.grothendieckLeftEdge`), read through the identifications `Hⁿ ≅ R^n (F ⋙ G) X` and
`E₂^{0,n} ≅ G (R^n F X)`.

For `F = f_*` and `G = h_*` along morphisms of sites `X ⟶ Y ⟶ Z`, this is the edge map
`R^n (h ∘ f)_* 𝓕 ⟶ h_* (R^n f_* 𝓕)`.

(blueprint: `lem-sp-grothendieck-edge-maps`) -/
noncomputable def grothendieckLeftEdgeMap [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (n : ℕ) :
    (F ⋙ G).rightDerived n ⟶ F.rightDerived n ⋙ G :=
  (F.grothendieckSpectralObjectHBotTopIso G hFG n).inv ≫ F.grothendieckLeftEdge G n ≫
    (F.grothendieckLeftEdgeTargetIso G n).hom

section BaseChange

universe v₄ v₅ v₆ u₄ u₅ u₆

variable {A' : Type u₄} [Category.{v₄} A'] [Abelian A'] [IsGrothendieckAbelian.{v₄} A']
  {B' : Type u₅} [Category.{v₅} B'] [Abelian B'] [IsGrothendieckAbelian.{v₅} B']
  {C' : Type u₆} [Category.{v₆} C'] [Abelian C']
  [HasDerivedCategory A'] [HasDerivedCategory B'] [HasDerivedCategory C']
  (F' : A' ⥤ B') (G' : B' ⥤ C') [F'.Additive] [G'.Additive]
  {α : A ⥤ A'} {β : B ⥤ B'} {γ : C ⥤ C'} [α.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

/-- The base change morphism `γ (R^p G (R^q F X)) ⟶ R^p G' (R^q F' (α X))` between the
`E₂`-terms of two Grothendieck spectral sequences related by exact functors `α`, `β`, `γ` and
isomorphisms `F ⋙ β ≅ α ⋙ F'`, `G ⋙ γ ≅ β ⋙ G'`, natural in `X`. It is assembled from the
base change morphisms `Functor.rightDerivedBaseChange` of the classical right derived
functors. -/
noncomputable def grothendieckE₂BaseChange (eF : F ⋙ β ≅ α ⋙ F') (eG : G ⋙ γ ≅ β ⋙ G')
    (p q : ℕ) :
    (F.rightDerived q ⋙ G.rightDerived p) ⋙ γ ⟶ α ⋙ F'.rightDerived q ⋙ G'.rightDerived p :=
  Functor.whiskerLeft (F.rightDerived q) (rightDerivedBaseChange eG.hom p) ≫
    Functor.whiskerRight (rightDerivedBaseChange eF.hom q) (G'.rightDerived p)

/-- The natural transformation `R⁺F(X[0]) ⟶ R⁺F'((α X)[0])` in `D⁺(B')`, natural in `X`, given
by the base change morphism `β⁺ R⁺F ⟶ R⁺F' α⁺` of the right derived functors. -/
noncomputable def rightDerivedFunctorPlusSingleBaseChange (eF : F ⋙ β ≅ α ⋙ F') :
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
        β.mapDerivedCategoryPlus ⟶
      α ⋙ DerivedCategory.Plus.singleFunctor A' 0 ⋙ F'.rightDerivedFunctorPlus :=
  Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
      (rightDerivedFunctorPlusBaseChange eF.hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (α.mapDerivedCategoryPlusSingleFunctor 0).hom
      F'.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

/-- The morphism of triangulated spectral objects underlying the base change morphism of the
Grothendieck spectral sequences: on `τ_{≥ a} τ_{< b} RF(X)` it is the base change morphism
`γ⁺ R⁺G ⟶ R⁺G' β⁺`, followed by the commutation of the t-exact functor `β⁺` with the
truncations and the base change morphism `β⁺ RF(X) ⟶ RF'(α X)`. -/
noncomputable def grothendieckTriangulatedSpectralObjectBaseChange (eF : F ⋙ β ≅ α ⋙ F')
    (eG : G ⋙ γ ≅ β ⋙ G') :
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
        G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt ⋙
        γ.mapDerivedCategoryPlus.mapTriangulatedSpectralObject EInt ⟶
      α ⋙ DerivedCategory.Plus.singleFunctor A' 0 ⋙ F'.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
        G'.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt :=
  Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.TStructure.t.spectralObjectFunctor)
      ((Functor.mapTriangulatedSpectralObjectCompIso _ _ EInt).inv ≫
        NatTrans.mapTriangulatedSpectralObject (rightDerivedFunctorPlusBaseChange eG.hom) EInt ≫
        (Functor.mapTriangulatedSpectralObjectCompIso _ _ EInt).hom) ≫
    Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus)
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (β.mapDerivedCategoryPlus.mapTriangulatedSpectralObjectIso
          DerivedCategory.Plus.TStructure.t DerivedCategory.Plus.TStructure.t).hom
          (G'.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt) ≫
        (Functor.associator _ _ _).hom) ≫
    (Functor.associator _ _ _).inv ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (rightDerivedFunctorPlusSingleBaseChange F F' eF)
      (DerivedCategory.Plus.TStructure.t.spectralObjectFunctor ⋙
        G'.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt) ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft α (Functor.associator _ _ _).hom

/-- Applying `γ` to the spectral object of the Grothendieck spectral sequence amounts to applying
the homology functor after `γ⁺` on the derived category. -/
noncomputable def grothendieckSpectralObjectFunctorCompMapSpectralObjectIso :
    (G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt ⋙
        (DerivedCategory.Plus.homologyFunctor C 0).mapHomologicalSpectralObject EInt) ⋙
        γ.mapSpectralObject EInt ≅
      G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt ⋙
        γ.mapDerivedCategoryPlus.mapTriangulatedSpectralObject EInt ⋙
        (DerivedCategory.Plus.homologyFunctor C' 0).mapHomologicalSpectralObject EInt :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (G.rightDerivedFunctorPlus.mapTriangulatedSpectralObject EInt)
      (Functor.mapHomologicalSpectralObjectCompMapSpectralObjectIso
        (DerivedCategory.Plus.homologyFunctor C 0)
        (DerivedCategory.Plus.homologyFunctor C' 0) γ.mapDerivedCategoryPlus γ
        (fun n ↦ γ.mapDerivedCategoryPlusHomologyFunctorIso n)
        (fun a a' h X ↦ γ.mapDerivedCategoryPlusHomologyFunctorIso_hom_app_shiftIso
          1 a a' h X) EInt)

-- Unifying the source and target with the composed functors needs unfolding definitions.
/-- The base change morphism between the spectral objects of two Grothendieck spectral
sequences related by exact functors, see `Functor.exists_grothendieckSpectralObject_baseChange`. -/
noncomputable def grothendieckSpectralObjectBaseChange (eF : F ⋙ β ≅ α ⋙ F')
    (eG : G ⋙ γ ≅ β ⋙ G') :
    F.grothendieckSpectralObjectFunctor G ⋙ γ.mapSpectralObject EInt ⟶
      α ⋙ F'.grothendieckSpectralObjectFunctor G' :=
  Functor.whiskerLeft (DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.TStructure.t.spectralObjectFunctor)
      (grothendieckSpectralObjectFunctorCompMapSpectralObjectIso G (γ := γ)).hom ≫
    Functor.whiskerRight (grothendieckTriangulatedSpectralObjectBaseChange F G F' G' eF eG)
      ((DerivedCategory.Plus.homologyFunctor C' 0).mapHomologicalSpectralObject EInt)

/-- The components of `Functor.grothendieckSpectralObjectBaseChange`: on
`γ(Hⁿ(R⁺G(τ_{≥ a} τ_{< b} RF(X))))` it is the commutation of `γ` with homology, followed by the
base change morphism of `R⁺G` and the commutation of `β⁺` with the truncations. -/
lemma grothendieckSpectralObjectBaseChange_app_hom_app (eF : F ⋙ β ≅ α ⋙ F')
    (eG : G ⋙ γ ≅ β ⋙ G') (X : A) (n : ℤ) (D : ComposableArrows EInt 1) :
    (((grothendieckSpectralObjectBaseChange F G F' G' eF eG).app X).hom n).app D =
      (γ.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
          (G.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj (D.obj 0)).obj
              ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj (D.obj 1)).obj
                (F.rightDerivedFunctorPlus.obj
                  ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map
          ((rightDerivedFunctorPlusBaseChange eG.hom).app _) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map (G'.rightDerivedFunctorPlus.map
          (β.mapDerivedCategoryPlus.eTruncGELTIsoApp DerivedCategory.Plus.TStructure.t
            DerivedCategory.Plus.TStructure.t (D.obj 0) (D.obj 1) _).hom) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map (G'.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj (D.obj 0)).map
            ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj (D.obj 1)).map
              ((rightDerivedFunctorPlusSingleBaseChange F F' eF).app X)))) := by
  simp only [comp_obj, grothendieckSpectralObjectBaseChange,
    grothendieckSpectralObjectFunctorCompMapSpectralObjectIso,
    mapHomologicalSpectralObjectCompMapSpectralObjectIso, Iso.trans_hom, isoWhiskerLeft_hom,
    whiskerLeft_comp, whiskerLeft_twice, grothendieckTriangulatedSpectralObjectBaseChange,
    Category.assoc, whiskerRight_comp, whiskerRight_twice, NatTrans.comp_app, whiskerLeft_app,
    associator_hom_app, associator_inv_app, NatIso.ofComponents_hom_app, whiskerRight_app, map_id,
    comp_map, Category.comp_id, Category.id_comp, Abelian.SpectralObject.comp_hom,
    Abelian.SpectralObject.id_hom, Abelian.SpectralObject.isoMk_hom_hom,
    mapHomologicalSpectralObject_map_hom, mapTriangulatedSpectralObjectCompIso_inv_app_hom,
    whiskerRight_id', NatTrans.mapTriangulatedSpectralObject_app_hom,
    mapTriangulatedSpectralObjectCompIso_hom_app_hom, NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp, Category.id_comp]
  rfl

/-- The components of `Functor.grothendieckSpectralObjectBaseChange` at `a ≤ b`. -/
lemma grothendieckSpectralObjectBaseChange_app_hom_app_mk₁ (eF : F ⋙ β ≅ α ⋙ F')
    (eG : G ⋙ γ ≅ β ⋙ G') (X : A) (n : ℤ) (a b : EInt) (hab : a ≤ b) :
    (((grothendieckSpectralObjectBaseChange F G F' G' eF eG).app X).hom n).app
        (mk₁ (homOfLE hab)) =
      (γ.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app
          (G.rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj a).obj
              ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj b).obj
                (F.rightDerivedFunctorPlus.obj
                  ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map
          ((rightDerivedFunctorPlusBaseChange eG.hom).app _) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map (G'.rightDerivedFunctorPlus.map
          (β.mapDerivedCategoryPlus.eTruncGELTIsoApp DerivedCategory.Plus.TStructure.t
            DerivedCategory.Plus.TStructure.t a b _).hom) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map (G'.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.TStructure.t.eTruncGE.obj a).map
            ((DerivedCategory.Plus.TStructure.t.eTruncLT.obj b).map
              ((rightDerivedFunctorPlusSingleBaseChange F F' eF).app X)))) :=
  grothendieckSpectralObjectBaseChange_app_hom_app F G F' G' eF eG X n (mk₁ (homOfLE hab))

/-- On the `E₂`-terms, the base change morphism `Functor.grothendieckSpectralObjectBaseChange` is
the base change morphism `γ (R^p G (R^q F X)) ⟶ R^p G' (R^q F' (α X))`
(`Functor.grothendieckE₂BaseChange`). -/
lemma grothendieckSpectralObjectBaseChange_E₂ (eF : F ⋙ β ≅ α ⋙ F') (eG : G ⋙ γ ≅ β ⋙ G')
    (p q : ℕ) (X : A) :
    (((grothendieckSpectralObjectBaseChange F G F' G' eF eG).app X).hom (p + q : ℕ)).app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp))) ≫
      (F'.grothendieckSpectralObjectHIso G' p q (p + q : ℕ) q (q + 1) (by push_cast; rfl) rfl
        rfl).hom.app (α.obj X) =
    γ.map ((F.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1) (by push_cast; rfl) rfl
        rfl).hom.app X) ≫ (grothendieckE₂BaseChange F G F' G' eF eG p q).app X := by
  rw [grothendieckSpectralObjectBaseChange_app_hom_app_mk₁, grothendieckSpectralObjectHIso_hom_app,
    grothendieckSpectralObjectHIso_hom_app]
  simp only [grothendieckE₂BaseChange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  have hB := β.mapDerivedCategoryPlus_eTruncGELTIsoApp_eTruncLTCompETruncGEIso q
    (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))
    ((rightDerivedFunctorPlusSingleBaseChange F F' eF).app X)
  have hB' := congrArg (fun f ↦ (DerivedCategory.Plus.homologyFunctor C' (p + q : ℕ)).map
    (G'.rightDerivedFunctorPlus.map f)) hB
  simp only [Functor.map_comp] at hB'
  rw [reassoc_of% hB']
  have hd {Z₁ Z₂ : DerivedCategory.Plus B} (x : Z₁ ⟶ Z₂) (n : ℤ) {W : C'}
      (w : (DerivedCategory.Plus.homologyFunctor C' n).obj
        (G'.rightDerivedFunctorPlus.obj (β.mapDerivedCategoryPlus.obj Z₂)) ⟶ W) :
      (γ.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app (G.rightDerivedFunctorPlus.obj Z₁) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map
          ((rightDerivedFunctorPlusBaseChange eG.hom).app Z₁) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map
          (G'.rightDerivedFunctorPlus.map (β.mapDerivedCategoryPlus.map x)) ≫ w =
      γ.map ((DerivedCategory.Plus.homologyFunctor C n).map (G.rightDerivedFunctorPlus.map x)) ≫
        (γ.mapDerivedCategoryPlusHomologyFunctorIso n).hom.app (G.rightDerivedFunctorPlus.obj Z₂) ≫
        (DerivedCategory.Plus.homologyFunctor C' n).map
          ((rightDerivedFunctorPlusBaseChange eG.hom).app Z₂) ≫ w := by
    have h₁ := (rightDerivedFunctorPlusBaseChange eG.hom).naturality x
    have h₂ := (γ.mapDerivedCategoryPlusHomologyFunctorIso n).hom.naturality
      (G.rightDerivedFunctorPlus.map x)
    simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
    rw [← Functor.map_comp_assoc, ← h₁, Functor.map_comp_assoc, reassoc_of% h₂]
  rw [hd, hd]
  have hb {Y₀ Y₁ Y₂ Y₃ : DerivedCategory.Plus B'} (x : Y₀ ⟶ Y₁) (y : Y₁ ⟶ Y₂) (z : Y₂ ⟶ Y₃)
      (m a a' : ℤ) (h : m + a = a') {W : C'}
      (w : (DerivedCategory.Plus.homologyFunctor C' a').obj (G'.rightDerivedFunctorPlus.obj Y₃) ⟶
        W) :
      (DerivedCategory.Plus.homologyFunctor C' a).map
          (G'.rightDerivedFunctorPlus.map ((shiftFunctor _ m).map x)) ≫
        (DerivedCategory.Plus.homologyFunctor C' a).map
          (G'.rightDerivedFunctorPlus.map ((shiftFunctor _ m).map y)) ≫
        (DerivedCategory.Plus.homologyFunctor C' a).map
          (G'.rightDerivedFunctorPlus.map ((shiftFunctor _ m).map z)) ≫
        (DerivedCategory.Plus.homologyFunctor C' a).map
          ((G'.rightDerivedFunctorPlus.commShiftIso m).hom.app Y₃) ≫
        ((DerivedCategory.Plus.homologyFunctor C' 0).shiftIso m a a' h).hom.app
          (G'.rightDerivedFunctorPlus.obj Y₃) ≫ w =
      (DerivedCategory.Plus.homologyFunctor C' a).map
          ((G'.rightDerivedFunctorPlus.commShiftIso m).hom.app Y₀) ≫
        ((DerivedCategory.Plus.homologyFunctor C' 0).shiftIso m a a' h).hom.app
          (G'.rightDerivedFunctorPlus.obj Y₀) ≫
        (DerivedCategory.Plus.homologyFunctor C' a').map
          (G'.rightDerivedFunctorPlus.map (x ≫ y ≫ z)) ≫ w := by
    have h₁ := G'.rightDerivedFunctorPlus.commShiftIso_hom_naturality (x ≫ y ≫ z) m
    have h₂ := (DerivedCategory.Plus.homologyFunctor C' 0).shiftIso_hom_naturality m a a' h
      (G'.rightDerivedFunctorPlus.map (x ≫ y ≫ z))
    simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
    rw [h₁, Functor.map_comp_assoc]
    erw [reassoc_of% h₂]
    rfl
  rw [hb, ← rightDerivedFunctorPlusBaseChange_homologyFunctor_shiftIso_assoc]
  have hψ : (rightDerivedFunctorPlusSingleBaseChange F F' eF).app X =
      (rightDerivedFunctorPlusBaseChange eF.hom).app
          ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
        F'.rightDerivedFunctorPlus.map ((α.mapDerivedCategoryPlusSingleFunctor 0).hom.app X) := by
    simp [rightDerivedFunctorPlusSingleBaseChange]
  have hend : γ.map ((G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).hom.app
        ((DerivedCategory.Plus.homologyFunctor B q).obj
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)))) ≫
      γ.map ((G.rightDerived p).map
        ((F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).hom.app X)) ≫
      (rightDerivedBaseChange eG.hom p).app ((F.rightDerived q).obj X) ≫
      (G'.rightDerived p).map ((rightDerivedBaseChange eF.hom q).app X) =
      (γ.mapDerivedCategoryPlusHomologyFunctorIso p).hom.app
          (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj
            ((DerivedCategory.Plus.homologyFunctor B q).obj
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
        (DerivedCategory.Plus.homologyFunctor C' p).map
          ((rightDerivedFunctorPlusBaseChange eG.hom).app
          ((DerivedCategory.Plus.singleFunctor B 0).obj
            ((DerivedCategory.Plus.homologyFunctor B q).obj
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
        (DerivedCategory.Plus.homologyFunctor C' p).map (G'.rightDerivedFunctorPlus.map
          ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app
            ((DerivedCategory.Plus.homologyFunctor B q).obj
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
        (DerivedCategory.Plus.homologyFunctor C' p).map (G'.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor B' 0).map
            ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
              (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X))))) ≫
        (DerivedCategory.Plus.homologyFunctor C' p).map (G'.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor B' 0).map
            ((DerivedCategory.Plus.homologyFunctor B' q).map
              ((rightDerivedFunctorPlusSingleBaseChange F F' eF).app X)))) ≫
        (G'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).hom.app
          ((DerivedCategory.Plus.homologyFunctor B' q).obj
            (F'.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A' 0).obj
              (α.obj X)))) ≫
        (G'.rightDerived p).map
          ((F'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).hom.app
            (α.obj X)) := by
    have hnat := (rightDerivedBaseChange eG.hom p).naturality
      ((F.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso q).hom.app X)
    have hρ := (G'.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso p).hom.naturality
      ((β.mapDerivedCategoryPlusHomologyFunctorIso q).hom.app
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor A 0).obj X)) ≫
        (DerivedCategory.Plus.homologyFunctor B' q).map
          ((rightDerivedFunctorPlusSingleBaseChange F F' eF).app X))
    simp only [Functor.comp_obj, Functor.comp_map] at hnat hρ
    rw [reassoc_of% hnat, rightDerivedBaseChange_app, rightDerivedBaseChange_app]
    simp only [Functor.map_comp, Category.assoc] at hρ ⊢
    rw [← γ.map_comp_assoc, Iso.hom_inv_id_app, γ.map_id, Category.id_comp, reassoc_of% hρ, hψ,
      ← Functor.map_comp_assoc (G'.rightDerived p), ← β.map_comp, Iso.hom_inv_id_app]
    erw [β.map_id, Functor.map_id, Category.id_comp]
    simp only [Functor.map_comp, Category.assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [hend]

/-- **Base change for the Grothendieck spectral sequence.** Let `(F, G)` and `(F', G')` be
composable pairs with acyclicity, related by exact functors `α : A ⥤ A'`, `β : B ⥤ B'`,
`γ : C ⥤ C'` and isomorphisms `F ⋙ β ≅ α ⋙ F'`, `G ⋙ γ ≅ β ⋙ G'`. Then there is a morphism
from the image under `γ` of the spectral object of the Grothendieck spectral sequence of `X` to
the spectral object of the Grothendieck spectral sequence of `α X`, natural in `X`, which on
the `E₂`-terms is the base change morphism
`γ (R^p G (R^q F X)) ⟶ R^p G' (R^q F' (α X))` (`Functor.grothendieckE₂BaseChange`). Since the
spectral sequences are those of these spectral objects, this is a morphism of spectral sequences
which is the base change morphism on the `E₂`-pages.

In the proper base change situation `α`, `β`, `γ` are the inverse images along the maps of a
cartesian square, which are exact.

The acyclicity hypotheses are only needed to identify the abutments of the two spectral sequences
with `R^n (F ⋙ G) X` and `R^n (F' ⋙ G') (α X)`; the construction of the morphism does not use
them.

(blueprint: `thm-sp-grothendieck-base-change`) -/
theorem exists_grothendieckSpectralObject_baseChange [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] [PreservesFiniteLimits F'] [PreservesFiniteLimits G']
    (_hFG : F.IsAcyclicComposablePair G) (_hFG' : F'.IsAcyclicComposablePair G')
    (eF : F ⋙ β ≅ α ⋙ F') (eG : G ⋙ γ ≅ β ⋙ G') :
    ∃ φ : F.grothendieckSpectralObjectFunctor G ⋙ γ.mapSpectralObject EInt ⟶
        α ⋙ F'.grothendieckSpectralObjectFunctor G',
      ∀ p q : ℕ, Functor.whiskerRight φ (Abelian.SpectralObject.hFunctor (p + q : ℕ)
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q + 1 : ℤ) : EInt) by simp)))) =
        (Functor.isoWhiskerRight (F.grothendieckSpectralObjectHIso G p q (p + q : ℕ) q (q + 1)
            (by push_cast; rfl) rfl rfl) γ).hom ≫
          grothendieckE₂BaseChange F G F' G' eF eG p q ≫
          (Functor.isoWhiskerLeft α (F'.grothendieckSpectralObjectHIso G' p q (p + q : ℕ) q
            (q + 1) (by push_cast; rfl) rfl rfl)).inv := by
  refine ⟨grothendieckSpectralObjectBaseChange F G F' G' eF eG, fun p q ↦ ?_⟩
  ext X
  have := grothendieckSpectralObjectBaseChange_E₂ F G F' G' eF eG p q X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Abelian.SpectralObject.hFunctor_map]
  rw [← cancel_mono ((F'.grothendieckSpectralObjectHIso G' p q (p + q : ℕ) q (q + 1)
    (by push_cast; rfl) rfl rfl).hom.app (α.obj X)), Category.assoc, Category.assoc,
    Iso.inv_hom_id_app]
  exact this.trans (by erw [Category.comp_id])

end BaseChange

end Functor

/-- **The Grothendieck spectral sequence.** If `F : A ⥤ B` and `G : B ⥤ C` are left exact
additive functors forming a composable pair with acyclicity

```
    A ───── F ─────▶ B ───── G ─────▶ C
     ╲                                ▲
      ╲───────────── F ⋙ G ──────────╱
```

then for every `X : A` there is a first quadrant cohomological spectral sequence with
`E₂^{p, q} ≅ R^p G (R^q F X)` abutting to `R^{p + q} (F ⋙ G) X`.

For `A` the abelian sheaves on a site `X`, `F = f_*` and `G = h_*` along morphisms of sites
`X ⥤ Y ⥤ Z`, the acyclicity hypothesis holds because `f_*` is right adjoint to the exact functor
`f^{-1}` and hence preserves injectives, and the statement specializes to
`R^p h_* R^q f_* F ⟹ R^{p + q} (h ∘ f)_* F`. Taking `Z` to be the punctual site, so that
`h_* = Γ(Y, -)`, it specializes further to the Leray spectral sequence
`H^p(Y, R^q f_* F) ⟹ H^{p + q}(X, F)`.

(blueprint: `det-thm-groth-ss`) -/
theorem Functor.exists_grothendieckSpectralSequence (F : A ⥤ B) (G : B ⥤ C)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : F.IsAcyclicComposablePair G) (X : A) :
    ∃ E : E₂CohomologicalSpectralSequenceNat C,
      (∀ p q : ℕ,
        Nonempty ((E.page 2).X (p, q) ≅ (G.rightDerived p).obj ((F.rightDerived q).obj X))) ∧
      E.AbutsTo (fun n ↦ ((F ⋙ G).rightDerived n).obj X) := by
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard B
  let := HasDerivedCategory.standard C
  exact ⟨F.grothendieckSpectralSequence G X,
    F.nonempty_grothendieckSpectralSequence_page_two_iso G X,
    F.grothendieckSpectralSequence_abutsTo G hFG X⟩

end CategoryTheory
