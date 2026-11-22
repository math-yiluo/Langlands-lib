import Langlands.Geometry.FormalGroup.AtlasBaseChange
import Langlands.Geometry.FormalGroup.AtlasTangentFiniteLocalization

/-! # The overlap tangent module is independent of a principal subcover -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas

open _root_.CategoryTheory
open scoped TensorProduct

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {I : Type} [Finite I] (X : BasicAtlas O R I)
variable (s : Set R) (hs : s ⊆ X.opens) (hc : Ideal.span s = ⊤)

/-- Retain a covering subset of the original principal generators, charts, and transitions. -/
def coverSubset : BasicAtlas O R I where
  opens := s
  covers := hc
  chart a := X.chart ⟨a.val, hs a.property⟩
  transition A a b ha hb := X.transition A ⟨a.val, hs a.property⟩ ⟨b.val, hs b.property⟩ ha hb
  transition_self A a ha := X.transition_self A ⟨a.val, hs a.property⟩ ha
  transition_cocycle A a b c ha hb hf := X.transition_cocycle A ⟨a.val, hs a.property⟩
    ⟨b.val, hs b.property⟩ ⟨c.val, hs c.property⟩ ha hb hf
  transition_natural g a b ha hb ha' hb' := X.transition_natural g
    ⟨a.val, hs a.property⟩ ⟨b.val, hs b.property⟩ ha hb ha' hb'

local notation "Y" => X.coverSubset s hs hc

/-- Regard a retained chart as an original chart. -/
def coverSubsetChart (b : (Y).opens) : X.opens := ⟨b.val, hs b.property⟩

local notation "old" => X.coverSubsetChart s hs hc

/-- Restrict compatible tangent coordinates to the chosen subcover. -/
def tangentRestrictCover (A : CommAlgCat.{v} R) :
    X.tangentSubmodule A →ₗ[A] (Y).tangentSubmodule A where
  toFun z := ⟨fun a => z.val (old a), ((Y).mem_tangentSubmodule A _).mpr fun a b =>
    (X.mem_tangentSubmodule A z.val).mp z.property (old a) (old b)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {A B C : CommAlgCat.{v} R}

private def subcoverTransport (y : (Y).tangentSubmodule A) (f : A ⟶ B)
    (a : X.opens) (ha : IsUnit (algebraMap R B a.val))
    (b : (Y).opens) (hb : IsUnit (algebraMap R B b.val)) : I → B :=
  X.transitionTangent B (old b) a hb ha ((Y).tangentTestEvaluation y ⟨B, f, b, hb⟩)

private theorem subcoverTransport_natural (y : (Y).tangentSubmodule A) (f : A ⟶ B) (g : B ⟶ C)
    (a : X.opens) (ha : IsUnit (algebraMap R B a.val)) (ha' : IsUnit (algebraMap R C a.val))
    (b : (Y).opens) (hb : IsUnit (algebraMap R B b.val)) (hb' : IsUnit (algebraMap R C b.val)) :
    (fun i => g.hom (X.subcoverTransport s hs hc y f a ha b hb i)) =
      X.subcoverTransport s hs hc y (f ≫ g) a ha' b hb' :=
  (X.transitionTangent_natural g (old b) a hb ha hb' ha'
    ((Y).tangentTestEvaluation y ⟨B, f, b, hb⟩)).trans
    (congrArg (X.transitionTangent C (old b) a hb' ha')
      ((Y).tangentTestEvaluation_map y ⟨B, f, b, hb⟩ g hb'))

private theorem subcoverTransport_independent (y : (Y).tangentSubmodule A) (f : A ⟶ B)
    (a : X.opens) (ha : IsUnit (algebraMap R B a.val))
    (b c : (Y).opens) (hb : IsUnit (algebraMap R B b.val)) (hd : IsUnit (algebraMap R B c.val)) :
    X.subcoverTransport s hs hc y f a ha b hb = X.subcoverTransport s hs hc y f a ha c hd := by
  let x := (Y).tangentTestEvaluation y ⟨B, f, b, hb⟩
  have h := (Y).tangentTestEvaluation_transition y f b c hb hd
  exact (LinearEquiv.congr_fun (X.transitionTangent_cocycle B (old b) (old c) a hb hd ha) x).symm.trans
    (congrArg (X.transitionTangent B (old c) a hd ha) h)

private theorem subcoverTransport_transition (y : (Y).tangentSubmodule A) (f : A ⟶ B)
    (a a' : X.opens) (ha : IsUnit (algebraMap R B a.val)) (ha' : IsUnit (algebraMap R B a'.val))
    (b : (Y).opens) (hb : IsUnit (algebraMap R B b.val)) :
    X.transitionTangent B a a' ha ha' (X.subcoverTransport s hs hc y f a ha b hb) =
      X.subcoverTransport s hs hc y f a' ha' b hb :=
  LinearEquiv.congr_fun (X.transitionTangent_cocycle B (old b) a a' hb ha ha')
    ((Y).tangentTestEvaluation y ⟨B, f, b, hb⟩)

private def subcoverImageTest (B : CommAlgCat.{v} R) (c : (Y).baseOpens B) : (Y).ChartTest B :=
  ⟨awayTangentTest B c.val, awayTangentTestMap B c.val, (Y).baseSource B c,
    (Y).baseChartCoefficient_unit B c⟩

private def subcoverLocalTangent (y : (Y).tangentSubmodule A) (t : X.ChartTest A)
    (c : (Y).baseOpens t.algebra) : I → Localization.Away c.val :=
  let q := X.subcoverImageTest s hs hc t.algebra c
  X.subcoverTransport s hs hc y (t.map ≫ q.map) t.chart (unit_map q.map t.isUnit) q.chart q.isUnit

private def imageAwayRight (B : CommAlgCat.{v} R) (b c : B) :
    awayTangentTest B b ⟶ awayTangentTest B (b * c) :=
  CommAlgCat.ofHom {
    __ := IsLocalization.Away.awayToAwayRight b c
    commutes' r := IsLocalization.Away.awayToAwayRight_eq b c (algebraMap R B r) }

private def imageAwayLeft (B : CommAlgCat.{v} R) (b c : B) :
    awayTangentTest B c ⟶ awayTangentTest B (b * c) :=
  CommAlgCat.ofHom {
    __ := IsLocalization.Away.awayToAwayLeft c b
    commutes' r := IsLocalization.Away.awayToAwayLeft_eq c b (algebraMap R B r) }

private theorem awayTangentTestMap_imageAwayRight (B : CommAlgCat.{v} R) (b c : B) :
    awayTangentTestMap B b ≫ imageAwayRight B b c = awayTangentTestMap B (b * c) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  exact IsLocalization.Away.awayToAwayRight_eq b c

private theorem awayTangentTestMap_imageAwayLeft (B : CommAlgCat.{v} R) (b c : B) :
    awayTangentTestMap B c ≫ imageAwayLeft B b c = awayTangentTestMap B (b * c) := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  exact IsLocalization.Away.awayToAwayLeft_eq c b

private theorem subcoverLocalTangent_agrees (y : (Y).tangentSubmodule A) (t : X.ChartTest A)
    (b c : (Y).baseOpens t.algebra) (i : I) :
    IsLocalization.Away.awayToAwayRight (P := Localization.Away (b.val * c.val)) b.val c.val
        (X.subcoverLocalTangent s hs hc y t b i) =
      IsLocalization.Away.awayToAwayLeft c.val b.val (X.subcoverLocalTangent s hs hc y t c i) := by
  let T := t.algebra
  let W := awayTangentTest T (b.val * c.val)
  let f := awayTangentTestMap T (b.val * c.val)
  let l := imageAwayRight T b.val c.val
  let r := imageAwayLeft T b.val c.val
  let q := X.subcoverImageTest s hs hc T b
  let q' := X.subcoverImageTest s hs hc T c
  let ha : IsUnit (algebraMap R W t.chart.val) := unit_map f t.isUnit
  let hb := unit_map l q.isUnit
  let hd := unit_map r q'.isUnit
  have h1 := X.subcoverTransport_natural s hs hc y (t.map ≫ q.map) l t.chart
    (unit_map q.map t.isUnit) ha q.chart q.isUnit hb
  have h2 := X.subcoverTransport_natural s hs hc y (t.map ≫ q'.map) r t.chart
    (unit_map q'.map t.isUnit) ha q'.chart q'.isUnit hd
  have h1c : (t.map ≫ q.map) ≫ l = t.map ≫ f := (Category.assoc t.map q.map l).trans
    (congrArg (fun g : T ⟶ W => t.map ≫ g) (awayTangentTestMap_imageAwayRight T b.val c.val))
  have h2c : (t.map ≫ q'.map) ≫ r = t.map ≫ f := (Category.assoc t.map q'.map r).trans
    (congrArg (fun g : T ⟶ W => t.map ≫ g) (awayTangentTestMap_imageAwayLeft T b.val c.val))
  rw [h1c] at h1
  rw [h2c] at h2
  exact congrFun (h1.trans ((X.subcoverTransport_independent s hs hc y (t.map ≫ f) t.chart
    ha q.chart q'.chart hb hd).trans h2.symm)) i

private def subcoverGluedTangent (y : (Y).tangentSubmodule A) (t : X.ChartTest A) : I → t.algebra :=
  fun i => Classical.choose (Localization.existsUnique_algebraMap_eq_of_span_eq_top
    ((Y).baseOpens t.algebra) ((Y).baseOpens_covers t.algebra)
    (fun c => X.subcoverLocalTangent s hs hc y t c i)
    (fun b c => X.subcoverLocalTangent_agrees s hs hc y t b c i))

private theorem subcoverGluedTangent_local (y : (Y).tangentSubmodule A) (t : X.ChartTest A)
    (c : (Y).baseOpens t.algebra) (i : I) :
    (X.subcoverImageTest s hs hc t.algebra c).map.hom (X.subcoverGluedTangent s hs hc y t i) =
      X.subcoverLocalTangent s hs hc y t c i :=
  (Classical.choose_spec (Localization.existsUnique_algebraMap_eq_of_span_eq_top
    ((Y).baseOpens t.algebra) ((Y).baseOpens_covers t.algebra)
    (fun b => X.subcoverLocalTangent s hs hc y t b i)
    (fun b d => X.subcoverLocalTangent_agrees s hs hc y t b d i))).1 c

private theorem subcoverGluedTangent_map (y : (Y).tangentSubmodule A) (t : X.ChartTest A)
    (g : t.algebra ⟶ B) (ha : IsUnit (algebraMap R B t.chart.val))
    (b : (Y).opens) (hb : IsUnit (algebraMap R B b.val)) :
    (fun i => g.hom (X.subcoverGluedTangent s hs hc y t i)) =
      X.subcoverTransport s hs hc y (t.map ≫ g) t.chart ha b hb := by
  let T := t.algebra
  let c : (Y).baseOpens T := ⟨algebraMap R T b.val, ⟨b.val, b.property, rfl⟩⟩
  let q := X.subcoverImageTest s hs hc T c
  let k : q.algebra ⟶ B := (Y).testFactor ⟨B, g, b, hb⟩
  have hk : q.map ≫ k = g := (Y).localizationMap_testFactor ⟨B, g, b, hb⟩
  have he : (fun i => g.hom (X.subcoverGluedTangent s hs hc y t i)) =
      fun i => k.hom (X.subcoverLocalTangent s hs hc y t c i) := funext fun i =>
    (congrArg (fun f : T ⟶ B => f.hom (X.subcoverGluedTangent s hs hc y t i)) hk.symm).trans
      (congrArg k.hom (X.subcoverGluedTangent_local s hs hc y t c i))
  have h := X.subcoverTransport_natural s hs hc y (t.map ≫ q.map) k t.chart
    (unit_map q.map t.isUnit) ha q.chart q.isUnit (unit_map k q.isUnit)
  have hcomp : (t.map ≫ q.map) ≫ k = t.map ≫ g :=
    (Category.assoc t.map q.map k).trans (congrArg (fun f : T ⟶ B => t.map ≫ f) hk)
  rw [hcomp] at h
  exact he.trans (h.trans (X.subcoverTransport_independent s hs hc y (t.map ≫ g) t.chart ha
    q.chart b (unit_map k q.isUnit) hb))

private theorem subcoverGluedTangent_overlap (y : (Y).tangentSubmodule A) :
    (fun a => X.subcoverGluedTangent s hs hc y (X.localTest A a)) ∈ X.tangentSubmodule A := by
  apply (X.mem_tangentSubmodule A _).mpr
  intro a a'
  let T := X.overlapAlgebra A a a'
  let l := X.overlapFromLeft A a a'
  let r := X.overlapFromRight A a a'
  let ha := X.overlapUnitLeft A a a'
  let ha' := X.overlapUnitRight A a a'
  let t := X.localTest A a
  let t' := X.localTest A a'
  let x : I → T := fun i => l.hom (X.subcoverGluedTangent s hs hc y t i)
  let x' : I → T := fun i => r.hom (X.subcoverGluedTangent s hs hc y t' i)
  change X.transitionTangent T a a' ha ha' x = x'
  funext i
  apply Localization.algebraMap_injective_of_span_eq_top
    ((Y).baseOpens T) ((Y).baseOpens_covers T)
  funext c
  let q := X.subcoverImageTest s hs hc T c
  let k := q.map
  let h := unit_map k ha
  let h' := unit_map k ha'
  let f := X.overlapMap A a a' ≫ k
  have hl : t.map ≫ (l ≫ k) = f :=
    (Category.assoc t.map l k).symm.trans
      (congrArg (fun g : A ⟶ T => g ≫ k)
        (X.localizationMap_testFactor ⟨T, X.overlapMap A a a', a, ha⟩))
  have hr : t'.map ≫ (r ≫ k) = f :=
    (Category.assoc t'.map r k).symm.trans
      (congrArg (fun g : A ⟶ T => g ≫ k)
        (X.localizationMap_testFactor ⟨T, X.overlapMap A a a', a', ha'⟩))
  have hx := X.subcoverGluedTangent_map s hs hc y t (l ≫ k) h q.chart q.isUnit
  have hx' := X.subcoverGluedTangent_map s hs hc y t' (r ≫ k) h' q.chart q.isUnit
  rw [hl] at hx
  rw [hr] at hx'
  have hn := X.transitionTangent_natural k a a' ha ha' h h' x
  have ht := X.subcoverTransport_transition s hs hc y f a a' h h' q.chart q.isUnit
  change k.hom (X.transitionTangent T a a' ha ha' x i) = k.hom (x' i)
  exact congrFun (hn.trans ((congrArg (X.transitionTangent q.algebra a a' h h') hx).trans
    (ht.trans hx'.symm))) i

private def tangentFromSubcover (y : (Y).tangentSubmodule A) : X.tangentSubmodule A :=
  ⟨fun a => X.subcoverGluedTangent s hs hc y (X.localTest A a), X.subcoverGluedTangent_overlap s hs hc y⟩

private theorem tangentRestrictCover_left (z : X.tangentSubmodule A) :
    X.tangentFromSubcover s hs hc (X.tangentRestrictCover s hs hc A z) = z := by
  apply Subtype.ext
  funext a i
  let t := X.localTest A a
  let T := t.algebra
  let y := X.tangentRestrictCover s hs hc A z
  change X.subcoverGluedTangent s hs hc y t i = z.val a i
  apply Localization.algebraMap_injective_of_span_eq_top
    ((Y).baseOpens T) ((Y).baseOpens_covers T)
  funext c
  let q := X.subcoverImageTest s hs hc T c
  let ha := unit_map q.map t.isUnit
  have h₁ := X.subcoverGluedTangent_local s hs hc y t c i
  have h₂ := X.tangentTestEvaluation_transition z (t.map ≫ q.map) (old q.chart) a q.isUnit ha
  have h₃ := X.tangentTestEvaluation_map z t q.map ha
  change q.map.hom (X.subcoverGluedTangent s hs hc y t i) = q.map.hom (z.val a i)
  exact h₁.trans ((congrFun (h₂.trans h₃.symm) i).trans
    (congrArg q.map.hom (congrFun (X.tangentTestEvaluation_localTest z a) i)))

private theorem tangentRestrictCover_right (y : (Y).tangentSubmodule A) :
    X.tangentRestrictCover s hs hc A (X.tangentFromSubcover s hs hc y) = y := by
  apply Subtype.ext
  funext b
  let a := old b
  let t := X.localTest A a
  let T := t.algebra
  have h := X.subcoverGluedTangent_map s hs hc y t (𝟙 T) t.isUnit b ((Y).localUnit A b)
  have hcomp : t.map ≫ 𝟙 T = (Y).localizationMap A b := Category.comp_id t.map
  rw [hcomp] at h
  change X.subcoverGluedTangent s hs hc y t =
    X.transitionTangent T a a t.isUnit t.isUnit ((Y).tangentTestEvaluation y ((Y).localTest A b)) at h
  have ht := LinearEquiv.congr_fun (X.transitionTangent_self T a t.isUnit)
    ((Y).tangentTestEvaluation y ((Y).localTest A b))
  exact h.trans (ht.trans ((Y).tangentTestEvaluation_localTest y b))

/-- Retaining a principal subcover identifies the two compatible tangent modules. -/
def tangentSubcoverEquiv (A : CommAlgCat.{v} R) :
    X.tangentSubmodule A ≃ₗ[A] (Y).tangentSubmodule A where
  __ := X.tangentRestrictCover s hs hc A
  invFun := X.tangentFromSubcover s hs hc
  left_inv := X.tangentRestrictCover_left s hs hc
  right_inv := X.tangentRestrictCover_right s hs hc

/-- Tangent coordinates restrict to a subcover naturally in the test. -/
theorem tangentSubcoverEquiv_natural (f : A ⟶ B) (z : X.tangentSubmodule A) :
    X.tangentSubcoverEquiv s hs hc B (X.tangentMap f z) =
      (Y).tangentMap f (X.tangentSubcoverEquiv s hs hc A z) := by
  apply Subtype.ext
  rfl

/-- The affine overlap tangent module commutes with localization at every test coefficient. -/
theorem tangentAwayMap_isLocalized (A : CommAlgCat.{v} R) (r : A) :
    IsLocalizedModule (Submonoid.powers r) (X.tangentAwayMap A r) := by
  obtain ⟨t, ht, hspan⟩ := (Ideal.span_eq_top_iff_finite X.opens).mp X.covers
  let Z := X.coverSubset (t : Set R) ht hspan
  have : Finite Z.opens := t.finite_toSet.to_subtype
  let T := awayTangentTest A r
  let e := X.tangentSubcoverEquiv (t : Set R) ht hspan A
  let e' : (X.tangentSubmodule T).restrictScalars A ≃ₗ[A] (Z.tangentSubmodule T).restrictScalars A :=
    (X.tangentSubcoverEquiv (t : Set R) ht hspan T).restrictScalars A
  have he : e'.toLinearMap.comp (X.tangentAwayMap A r) =
      (Z.tangentAwayMap A r).comp e.toLinearMap :=
    LinearMap.ext (X.tangentSubcoverEquiv_natural (t : Set R) ht hspan (awayTangentTestMap A r))
  apply (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r) e'.toLinearMap e'.bijective).mp
  rw [he]
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r) e.toLinearMap
    e.bijective).mpr (Z.tangentAwayMap_isLocalized_of_finite A r)

/-- The tensor product of the overlap tangent module with the test localization is its new tangent module. -/
def tangentAwayEquiv (A : CommAlgCat.{v} R) (r : A) :
    (awayTangentTest A r ⊗[A] X.tangentSubmodule A) ≃ₗ[awayTangentTest A r]
      X.tangentSubmodule (awayTangentTest A r) :=
  ((isLocalizedModule_iff_isBaseChange (Submonoid.powers r) (awayTangentTest A r)
    (X.tangentAwayMap A r)).mp (X.tangentAwayMap_isLocalized A r)).equiv

@[simp]
theorem tangentAwayEquiv_tmul (A : CommAlgCat.{v} R) (r : A) (x : awayTangentTest A r)
    (z : X.tangentSubmodule A) :
    X.tangentAwayEquiv A r (x ⊗ₜ[A] z) = x • X.tangentMap (awayTangentTestMap A r) z := by
  have h : IsBaseChange (awayTangentTest A r) (X.tangentAwayMap A r) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers r) (awayTangentTest A r)
      (X.tangentAwayMap A r)).mp (X.tangentAwayMap_isLocalized A r)
  exact h.equiv_tmul x z

end Langlands.FormalGroup.ModuleLaw.BasicAtlas
