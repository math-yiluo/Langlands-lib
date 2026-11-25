/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ColimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.SingleObj
public import WeilConjectures.Mathlib.RingTheory.TotallySplit
public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Quotients of affine schemes by monoid actions

Let `X` be a scheme and `P` a property of affine morphisms. A diagram
`K : SingleObj G ⥤ P.Over ⊤ X` is an affine
`X`-scheme `W` with an action of the monoid `G` by `X`-endomorphisms. If `X` is affine, its
colimit is `Spec` of the invariants of `Γ(W)`, and a cocone is a colimit iff its leg is injective
on global sections with image the invariants
(`AlgebraicGeometry.Scheme.isColimit_iff_injective_appTop`). If `G` is finite, the formation of
the quotient commutes with flat base change, so the quotients over the affine opens of an
arbitrary `X` glue (`AlgebraicGeometry.Scheme.Cover.hasColimit_of_locallyDirected`).

## Main results

- `AlgebraicGeometry.Scheme.isColimit_iff_injective_appTop`: the characterisation of colimits
  over an affine base.
- `AlgebraicGeometry.Scheme.hasColimitsOfShape_singleObj_isAffineHom_over`: affine `X`-schemes
  have quotients by finite groups.

-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

lemma toSpecΓ_comp_specMap_appTop (W : Scheme.{u}) {R : CommRingCat.{u}} (f : R ⟶ Γ(W, ⊤)) :
    (W.toSpecΓ ≫ Spec.map f).appTop = (ΓSpecIso R).hom ≫ f := by
  rw [Hom.comp_appTop, toSpecΓ_appTop, ΓSpecIso_naturality]

/-- The morphism of affine schemes with a given map on global sections. -/
noncomputable def homOfAppTop {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (φ : Γ(T', ⊤) ⟶ Γ(T, ⊤)) : T ⟶ T' :=
  T.isoSpec.hom ≫ Spec.map φ ≫ T'.isoSpec.inv

@[simp]
lemma homOfAppTop_appTop {T T' : Scheme.{u}} [IsAffine T] [IsAffine T']
    (φ : Γ(T', ⊤) ⟶ Γ(T, ⊤)) : (homOfAppTop φ).appTop = φ := by
  apply Spec.map_injective
  rw [← cancel_epi T.isoSpec.hom, isoSpec_hom_naturality, homOfAppTop]
  simp

variable {P : MorphismProperty Scheme.{u}}
  (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), P f → IsAffineHom f)
  {X : Scheme.{u}} {G : Type*} [Monoid G] (K : SingleObj G ⥤ P.Over ⊤ X)

include hP in
lemma isAffine_left [IsAffine X] (W : P.Over ⊤ X) : IsAffine W.left :=
  have : IsAffineHom W.hom := hP _ W.prop
  have : IsAffine ((Functor.fromPUnit X).obj W.right) := ‹IsAffine X›
  isAffine_of_isAffineHom W.hom

lemma appTop_map_apply_of_cocone (c : Cocone K) (g : G) (z : Γ(c.pt.left, ⊤)) :
    (K.map g).left.appTop.hom ((c.ι.app (SingleObj.star G)).left.appTop.hom z) =
      (c.ι.app (SingleObj.star G)).left.appTop.hom z := by
  have := congr_arg (fun f : K.obj (SingleObj.star G) ⟶ c.pt ↦ f.left.appTop.hom z)
    (c.w (j := SingleObj.star G) (j' := SingleObj.star G) g)
  rwa [MorphismProperty.Comma.comp_left, Hom.comp_appTop] at this

section Affine

variable [IsAffine X]

include hP in
/-- A cocone over an affine base `X` of a monoid action on an affine `X`-scheme `W` is a colimit
if its leg `W ⟶ c.pt` is injective on global sections with image containing the invariants. -/
noncomputable def isColimitOfInjectiveAppTop (c : Cocone K)
    (hinj : Function.Injective (c.ι.app (SingleObj.star G)).left.appTop.hom)
    (hrange : ∀ a, (∀ g, (K.map g).left.appTop.hom a = a) →
      a ∈ Set.range (c.ι.app (SingleObj.star G)).left.appTop.hom) : IsColimit c := by
  have (W : P.Over ⊤ X) : IsAffine W.left := isAffine_left hP W
  let α := (c.ι.app (SingleObj.star G)).left.appTop.hom
  let e := RingEquiv.ofBijective α.rangeRestrict
    ⟨fun a b h ↦ hinj (congr_arg Subtype.val h), α.rangeRestrict_surjective⟩
  have he (y : α.range) : α (e.symm y) = y := congr_arg Subtype.val (e.apply_symm_apply y)
  -- the global sections map of the descended morphism
  let β (s : Cocone K) : Γ(s.pt.left, ⊤) →+* Γ(c.pt.left, ⊤) :=
    e.symm.toRingHom.comp ((s.ι.app (SingleObj.star G)).left.appTop.hom.codRestrict α.range
      fun z ↦ hrange _ fun g ↦ appTop_map_apply_of_cocone K s g z)
  have hβ (s : Cocone K) (z : Γ(s.pt.left, ⊤)) :
      α (β s z) = (s.ι.app (SingleObj.star G)).left.appTop.hom z := he _
  have hdesc (s : Cocone K) : homOfAppTop (CommRingCat.ofHom (β s)) ≫ s.pt.hom = c.pt.hom := by
    have : IsAffine ((Functor.fromPUnit X).obj s.pt.right) := ‹IsAffine X›
    apply ext_of_isAffine
    ext x
    apply hinj
    simp only [Hom.comp_appTop, CommRingCat.hom_comp, homOfAppTop_appTop, CommRingCat.hom_ofHom,
      RingHom.coe_comp, Function.comp_apply]
    rw [hβ]
    change ((s.ι.app _).left ≫ s.pt.hom).appTop.hom x = ((c.ι.app _).left ≫ c.pt.hom).appTop.hom x
    have h₁ : (s.ι.app (SingleObj.star G)).left ≫ s.pt.hom = (K.obj (SingleObj.star G)).hom :=
      MorphismProperty.Over.w _
    have h₂ : (c.ι.app (SingleObj.star G)).left ≫ c.pt.hom = (K.obj (SingleObj.star G)).hom :=
      MorphismProperty.Over.w _
    exact congr($(h₁.trans h₂.symm).appTop.hom x)
  refine
    { desc s := Over.homMk (homOfAppTop (CommRingCat.ofHom (β s))) (hdesc s) trivial
      fac s j := ?_
      uniq s m hm := ?_ }
  · obtain rfl : j = SingleObj.star G := rfl
    ext1
    apply ext_of_isAffine
    ext z
    simp only [Over.homMk_hom, MorphismProperty.Comma.comp_left, Hom.comp_appTop,
      CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply]
    exact (congr_arg α (by simp)).trans (hβ s z)
  · ext1
    apply ext_of_isAffine
    ext z
    apply hinj
    have := congr_arg (fun f : K.obj (SingleObj.star G) ⟶ s.pt ↦ f.left.appTop.hom z)
      (hm (SingleObj.star G))
    simp only [MorphismProperty.Comma.comp_left, Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.coe_comp,
      Function.comp_apply] at this
    refine this.trans ((hβ s z).symm.trans ?_)
    congr 1
    change _ = (homOfAppTop (CommRingCat.ofHom (β s))).appTop.hom z
    simp

omit [IsAffine X] in
/-- The invariants of the action of `G` on the global sections of `K(⋆)`. -/
def invariants : Subring Γ((K.obj (SingleObj.star G)).left, ⊤) :=
  ⨅ g : G, RingHom.eqLocus (K.map g).left.appTop.hom (RingHom.id _)

omit [IsAffine X] in
lemma mem_invariants {a : Γ((K.obj (SingleObj.star G)).left, ⊤)} :
    a ∈ invariants K ↔ ∀ g : G, (K.map g).left.appTop.hom a = a := by
  simp [invariants, Subring.mem_iInf, RingHom.mem_eqLocus]

omit [IsAffine X] in
lemma appTop_hom_mem_invariants (x : Γ(X, ⊤)) :
    (K.obj (SingleObj.star G)).hom.appTop.hom x ∈ invariants K := by
  rw [mem_invariants]
  intro g
  have h : (K.map g).left ≫ (K.obj (SingleObj.star G)).hom = (K.obj (SingleObj.star G)).hom :=
    MorphismProperty.Over.w _
  exact congr($(h).appTop.hom x)

variable (hP' : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), IsAffine Y → IsAffine Z → P f)

omit [IsAffine X] in
/-- The inclusion of the invariants into the global sections. -/
noncomputable def invariantsι :
    CommRingCat.of (invariants K) ⟶ Γ((K.obj (SingleObj.star G)).left, ⊤) :=
  CommRingCat.ofHom (invariants K).subtype

omit [IsAffine X] in
/-- The structure map of the invariants. -/
noncomputable def invariantsStructure : Γ(X, ⊤) ⟶ CommRingCat.of (invariants K) :=
  CommRingCat.ofHom (((K.obj (SingleObj.star G)).hom.appTop.hom).codRestrict _
    (appTop_hom_mem_invariants K))

omit [IsAffine X] in
lemma invariantsStructure_invariantsι :
    invariantsStructure K ≫ invariantsι K = (K.obj (SingleObj.star G)).hom.appTop :=
  rfl

omit [IsAffine X] in
lemma map_invariantsι (g : G) : invariantsι K ≫ (K.map g).left.appTop = invariantsι K := by
  ext a
  exact (mem_invariants K).mp a.2 g

include hP' in
/-- The quotient of an affine `X`-scheme by a monoid action: `Spec` of the invariants. -/
noncomputable abbrev quotientPt : P.Over ⊤ X :=
  { left := Spec (CommRingCat.of (invariants K))
    right := ⟨⟨⟩⟩
    hom := Spec.map (invariantsStructure K) ≫ X.isoSpec.inv
    prop := hP' _ (inferInstanceAs (IsAffine (Spec _))) ‹IsAffine X› }

include hP' in
/-- The quotient map. -/
noncomputable def quotientι : K.obj (SingleObj.star G) ⟶ quotientPt K hP' :=
  MorphismProperty.Over.homMk ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
    Spec.map (invariantsι K)) (by
      have key : ((K.obj (SingleObj.star G)).left.toSpecΓ ≫ Spec.map (invariantsι K)) ≫
          Spec.map (invariantsStructure K) ≫ X.isoSpec.inv = (K.obj (SingleObj.star G)).hom := by
        rw [Category.assoc, ← Spec.map_comp_assoc, invariantsStructure_invariantsι,
          ← toSpecΓ_naturality_assoc]
        change (K.obj (SingleObj.star G)).hom ≫ X.toSpecΓ ≫ X.isoSpec.inv = _
        simp
      exact key) trivial

include hP' in
/-- The quotient of an affine `X`-scheme by a monoid action, as a cocone. -/
noncomputable def quotientCocone : Cocone K where
  pt := quotientPt K hP'
  ι :=
    { app _ := quotientι K hP'
      naturality := fun x y g ↦ by
        obtain rfl : x = SingleObj.star G := rfl
        obtain rfl : y = SingleObj.star G := rfl
        ext1
        change (K.map g).left ≫ ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
          Spec.map (invariantsι K)) =
          (K.obj (SingleObj.star G)).left.toSpecΓ ≫ Spec.map (invariantsι K)
        rw [toSpecΓ_naturality_assoc, ← Spec.map_comp, map_invariantsι] }

omit [IsAffine X] in
lemma quotientι_left_appTop_apply (x : Γ(Spec (CommRingCat.of (invariants K)), ⊤)) :
    ((K.obj (SingleObj.star G)).left.toSpecΓ ≫ Spec.map (invariantsι K)).appTop.hom x =
      invariantsι K ((ΓSpecIso (CommRingCat.of (invariants K))).hom x) :=
  congr($(toSpecΓ_comp_specMap_appTop _ (invariantsι K)).hom x)

omit [IsAffine X] in
lemma injective_quotientι_left_appTop :
    Function.Injective ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
      Spec.map (invariantsι K)).appTop.hom := by
  intro x y hxy
  have := (quotientι_left_appTop_apply K x).symm.trans
    (hxy.trans (quotientι_left_appTop_apply K y))
  exact (ΓSpecIso (CommRingCat.of (invariants K))).commRingCatIsoToRingEquiv.injective
    (Subtype.val_injective this)

omit [IsAffine X] in
lemma mem_range_quotientι_left_appTop (a : Γ((K.obj (SingleObj.star G)).left, ⊤))
    (ha : ∀ g : G, (K.map g).left.appTop.hom a = a) :
    a ∈ Set.range ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
      Spec.map (invariantsι K)).appTop.hom := by
  refine ⟨(ΓSpecIso (CommRingCat.of (invariants K))).inv.hom ⟨a, (mem_invariants K).mpr ha⟩, ?_⟩
  refine (quotientι_left_appTop_apply K _).trans ?_
  change invariantsι K (((ΓSpecIso (CommRingCat.of (invariants K))).inv ≫
    (ΓSpecIso (CommRingCat.of (invariants K))).hom).hom _) = _
  rw [Iso.inv_hom_id]
  rfl

include hP hP' in
/-- The quotient cocone is a colimit. -/
noncomputable def isColimitQuotientCocone : IsColimit (quotientCocone K hP') :=
  isColimitOfInjectiveAppTop hP K _ (injective_quotientι_left_appTop K)
    (mem_range_quotientι_left_appTop K)

include hP hP' in
/-- Over an affine base, the leg of a colimit cocone of a monoid action on an affine scheme is
injective on global sections, with image the invariants. -/
lemma injective_appTop_of_isColimit {c : Cocone K} (hc : IsColimit c) :
    Function.Injective (c.ι.app (SingleObj.star G)).left.appTop.hom ∧
      ∀ a, (∀ g : G, (K.map g).left.appTop.hom a = a) →
        a ∈ Set.range (c.ι.app (SingleObj.star G)).left.appTop.hom := by
  let e := hc.coconePointUniqueUpToIso (isColimitQuotientCocone hP K hP')
  have he := hc.comp_coconePointUniqueUpToIso_hom (isColimitQuotientCocone hP K hP')
    (SingleObj.star G)
  have heq (x) : ((K.obj (SingleObj.star G)).left.toSpecΓ ≫
      Spec.map (invariantsι K)).appTop.hom x =
      (c.ι.app (SingleObj.star G)).left.appTop.hom (e.hom.left.appTop.hom x) := by
    have := congr($(he).left.appTop.hom x)
    exact this.symm
  have hbij : Function.Bijective e.hom.left.appTop.hom :=
    (Scheme.Γ.mapIso ((MorphismProperty.Over.forget P ⊤ X ⋙ Over.forget X).mapIso
      e).op).commRingCatIsoToRingEquiv.bijective
  refine ⟨fun x y hxy ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := hbij.2 x
    obtain ⟨y, rfl⟩ := hbij.2 y
    rw [injective_quotientι_left_appTop K ((heq x).trans (hxy.trans (heq y).symm))]
  · obtain ⟨x, hx⟩ := mem_range_quotientι_left_appTop K a ha
    exact ⟨_, (heq x).symm.trans hx⟩

include hP hP' in
/-- Over affine schemes, base change along a flat morphism preserves quotients by finite monoid
actions: the base change of the invariants is computed by flat base change of fixed points
(`AlgHom.injective_and_mem_range_of_isPushout`). -/
lemma preservesColimit_pullback [Finite G] {U : Scheme.{u}} [IsAffine U] (f : U ⟶ X) [Flat f]
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] :
    PreservesColimit K (MorphismProperty.Over.pullback P ⊤ f) := by
  have hA (W : P.Over ⊤ X) : IsAffine W.left := isAffine_left hP W
  let c := quotientCocone K hP'
  have hc := isColimitQuotientCocone hP K hP'
  refine preservesColimit_of_preserves_colimit_cocone hc ?_
  let K' := K ⋙ MorphismProperty.Over.pullback P ⊤ f
  let c' := (MorphismProperty.Over.pullback P ⊤ f).mapCocone c
  let W := K.obj (SingleObj.star G)
  let Q := c.pt
  -- the rings
  let R := Γ(X, ⊤)
  let S := Γ(U, ⊤)
  let A := Γ(W.left, ⊤)
  let B := Γ(Q.left, ⊤)
  let A' := Γ(pullback W.hom f, ⊤)
  let B' := Γ(pullback Q.hom f, ⊤)
  letI : Algebra R S := f.appTop.hom.toAlgebra
  letI : Algebra R A := W.hom.appTop.hom.toAlgebra
  letI : Algebra R B := Q.hom.appTop.hom.toAlgebra
  letI : Algebra A A' := (pullback.fst W.hom f).appTop.hom.toAlgebra
  letI : Algebra S A' := (pullback.snd W.hom f).appTop.hom.toAlgebra
  letI : Algebra R A' := (W.hom.appTop ≫ (pullback.fst W.hom f).appTop).hom.toAlgebra
  letI : Algebra B B' := (pullback.fst Q.hom f).appTop.hom.toAlgebra
  letI : Algebra S B' := (pullback.snd Q.hom f).appTop.hom.toAlgebra
  letI : Algebra R B' := (Q.hom.appTop ≫ (pullback.fst Q.hom f).appTop).hom.toAlgebra
  have hsqA : W.hom.appTop ≫ (pullback.fst W.hom f).appTop =
      f.appTop ≫ (pullback.snd W.hom f).appTop := by
    rw [← Hom.comp_appTop, ← Hom.comp_appTop, pullback.condition]
  have hsqB : Q.hom.appTop ≫ (pullback.fst Q.hom f).appTop =
      f.appTop ≫ (pullback.snd Q.hom f).appTop := by
    rw [← Hom.comp_appTop, ← Hom.comp_appTop, pullback.condition]
  haveI : IsScalarTower R A A' := .of_algebraMap_eq' rfl
  haveI : IsScalarTower R S A' := .of_algebraMap_eq' congr($(hsqA).hom)
  haveI : IsScalarTower R B B' := .of_algebraMap_eq' rfl
  haveI : IsScalarTower R S B' := .of_algebraMap_eq' congr($(hsqB).hom)
  have : IsAffine ((𝟭 Scheme).obj W.left) := hA W
  have : IsAffine ((𝟭 Scheme).obj Q.left) := hA Q
  have : IsAffine ((Functor.fromPUnit X).obj W.right) := ‹IsAffine X›
  have : IsAffine ((Functor.fromPUnit X).obj Q.right) := ‹IsAffine X›
  haveI : Algebra.IsPushout R S A A' :=
    (CommRingCat.isPushout_iff_isPushout.mp
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback W.hom f))).symm
  haveI : Algebra.IsPushout R S B B' :=
    (CommRingCat.isPushout_iff_isPushout.mp
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback Q.hom f))).symm
  haveI : Module.Flat R S := by
    have := (HasRingHomProperty.iff_of_isAffine (P := @Flat) (f := f)).mp ‹_›
    exact RingHom.flat_algebraMap_iff.mpr this
  -- the leg and the action
  have hι : Q.hom.appTop ≫ (c.ι.app (SingleObj.star G)).left.appTop = W.hom.appTop := by
    rw [← Hom.comp_appTop]
    congr 1
    exact MorphismProperty.Over.w _
  let α : B →ₐ[R] A :=
    { (c.ι.app (SingleObj.star G)).left.appTop.hom with
      commutes' r := congr($(hι).hom r) }
  have hσ (g : G) : W.hom.appTop ≫ (K.map g).left.appTop = W.hom.appTop := by
    rw [← Hom.comp_appTop]
    congr 1
    exact MorphismProperty.Over.w _
  let σ (g : G) : A →ₐ[R] A :=
    { (K.map g).left.appTop.hom with
      commutes' r := congr($(hσ g).hom r) }
  obtain ⟨hinj, hrange⟩ := injective_appTop_of_isColimit hP K hP' hc
  have e₁ : (c'.ι.app (SingleObj.star G)).left ≫ pullback.fst Q.hom f =
      pullback.fst W.hom f ≫ (c.ι.app (SingleObj.star G)).left :=
    pullback.lift_fst _ _ _
  have e₂ : (c'.ι.app (SingleObj.star G)).left ≫ pullback.snd Q.hom f = pullback.snd W.hom f :=
    pullback.lift_snd _ _ _
  have e₁' (g : G) : (K'.map g).left ≫ pullback.fst W.hom f =
      pullback.fst W.hom f ≫ (K.map g).left :=
    pullback.lift_fst _ _ _
  have e₂' (g : G) : (K'.map g).left ≫ pullback.snd W.hom f = pullback.snd W.hom f :=
    pullback.lift_snd _ _ _
  obtain ⟨hinj', hrange'⟩ := AlgHom.injective_and_mem_range_of_isPushout (R := R) (S := S)
    (A := A) (B := B) (A' := A') (B' := B') α hinj
    (c'.ι.app (SingleObj.star G)).left.appTop.hom
    (fun y ↦ congr($(e₁).appTop.hom y)) (fun s ↦ congr($(e₂).appTop.hom s))
    σ (fun g ↦ (K'.map g).left.appTop.hom)
    (fun g x ↦ congr($(e₁' g).appTop.hom x)) (fun g s ↦ congr($(e₂' g).appTop.hom s))
    (fun x hx ↦ hrange x (AlgHom.mem_fixedPoints.mp hx))
  have hA' (W : P.Over ⊤ U) : IsAffine W.left := isAffine_left hP W
  exact isColimitOfInjectiveAppTop hP K' c' hinj' hrange'

include hP hP' in
/-- Over an affine base, the quotient of a finite étale scheme by a finite monoid action is
finite étale: its ring is the ring of invariants (`AlgHom.finite_and_etale_fixedPoints`). -/
lemma isFinite_and_etale_quotientPt [Finite G] [IsFinite (K.obj (SingleObj.star G)).hom]
    [Etale (K.obj (SingleObj.star G)).hom] :
    IsFinite (quotientPt K hP').hom ∧ Etale (quotientPt K hP').hom := by
  let W := K.obj (SingleObj.star G)
  have : IsAffine W.left := isAffine_left hP W
  have : IsAffine ((Functor.fromPUnit X).obj W.right) := ‹IsAffine X›
  have : IsAffine ((𝟭 Scheme).obj W.left) := ‹IsAffine W.left›
  let R := Γ(X, ⊤)
  let A := Γ(W.left, ⊤)
  let : Algebra R A := W.hom.appTop.hom.toAlgebra
  have : Module.Finite R A := W.hom.finite_appTop
  have : Algebra.Etale R A := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := W.hom)).mp ‹_›)
  have hσ (g : G) : W.hom.appTop ≫ (K.map g).left.appTop = W.hom.appTop := by
    rw [← Hom.comp_appTop]
    congr 1
    exact MorphismProperty.Over.w _
  let σ (g : G) : A →ₐ[R] A :=
    { (K.map g).left.appTop.hom with
      commutes' r := congr($(hσ g).hom r) }
  obtain ⟨hfin, het⟩ := AlgHom.finite_and_etale_fixedPoints σ
  have heq : invariants K = (AlgHom.fixedPoints σ).toSubring := by
    ext a
    rw [mem_invariants, Subalgebra.mem_toSubring, AlgHom.mem_fixedPoints]
    rfl
  let ψ : invariants K ≃+* AlgHom.fixedPoints σ := RingEquiv.subringCongr heq
  have hψ : (invariantsStructure K).hom = ψ.symm.toRingHom.comp
      (algebraMap R (AlgHom.fixedPoints σ)) := by
    ext x
    rfl
  have hfin' : (invariantsStructure K).hom.Finite := by
    rw [hψ]
    exact RingHom.finite_respectsIso.1 _ ψ.symm (RingHom.finite_algebraMap.mpr hfin)
  have het' : (invariantsStructure K).hom.Etale := by
    rw [hψ]
    exact RingHom.Etale.respectsIso.1 _ ψ.symm (RingHom.etale_algebraMap.mpr het)
  have h1 : IsFinite (Spec.map (invariantsStructure K)) := (IsFinite.SpecMap_iff _).mpr hfin'
  have h2 : Etale (Spec.map (invariantsStructure K)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr het'
  exact ⟨inferInstanceAs (IsFinite (Spec.map _ ≫ _)), inferInstanceAs (Etale (Spec.map _ ≫ _))⟩

end Affine

instance isAffine_directedAffineCover_X {Y : Scheme.{u}} (U : Y.directedAffineCover.I₀) :
    IsAffine (Y.directedAffineCover.X U) :=
  U.2

section Global

variable [P.IsStableUnderBaseChange] [P.IsMultiplicative] [IsZariskiLocalAtTarget P]
  (hP' : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), IsAffine Y → IsAffine Z → P f) [Finite G]
  {Y : Scheme.{u}} (D : SingleObj G ⥤ P.Over ⊤ Y)

omit [P.IsMultiplicative] [IsZariskiLocalAtTarget P] in
include hP hP' in
lemma preservesColimitsOfShape_pullback {U V : Scheme.{u}} [IsAffine U] [IsAffine V] (f : U ⟶ V)
    [Flat f] : PreservesColimitsOfShape (SingleObj G) (MorphismProperty.Over.pullback P ⊤ f) :=
  ⟨fun {K} ↦ preservesColimit_pullback hP K hP' f⟩

include hP in
/-- The gluing data for the quotient of an affine `Y`-scheme by a finite monoid action: the
quotients over the affine opens of `Y`. -/
noncomputable def quotientGluingData : Y.directedAffineCover.ColimitGluingData D where
  cocone U := quotientCocone (D ⋙ MorphismProperty.Over.pullback P ⊤ (Y.directedAffineCover.f U))
    hP'
  isColimit _ := isColimitQuotientCocone hP _ hP'
  prop_trans _ := hP' _ inferInstance inferInstance

include hP hP' in
/-- **Quotients of affine `Y`-schemes by finite monoid actions.** If `P` is a property of affine
morphisms containing all morphisms of affine schemes, then `P.Over ⊤ Y` has quotients by finite
monoid actions: over every affine open of `Y` the quotient is `Spec` of the invariants, and these
glue. -/
theorem hasColimitsOfShape_singleObj : HasColimitsOfShape (SingleObj G) (P.Over ⊤ Y) := by
  have : ∀ {U V : Y.directedAffineCover.I₀} (hUV : U ⟶ V),
      PreservesColimitsOfShape (SingleObj G)
        (MorphismProperty.Over.pullback P ⊤ (Y.directedAffineCover.trans hUV)) :=
    fun _ ↦ preservesColimitsOfShape_pullback hP hP' _
  exact ⟨fun D ↦ ⟨_, (quotientGluingData hP hP' D).isColimitGluedCocone⟩⟩

include hP hP' in
/-- Restriction to an affine open of `Y` preserves quotients by finite monoid actions. -/
lemma preservesColimit_pullback_directedAffineCover (U : Y.directedAffineCover.I₀) :
    PreservesColimit D (MorphismProperty.Over.pullback P ⊤ (Y.directedAffineCover.f U)) := by
  have : ∀ {U V : Y.directedAffineCover.I₀} (hUV : U ⟶ V),
      PreservesColimitsOfShape (SingleObj G)
        (MorphismProperty.Over.pullback P ⊤ (Y.directedAffineCover.trans hUV)) :=
    fun _ ↦ preservesColimitsOfShape_pullback hP hP' _
  let d := quotientGluingData hP hP' D
  refine preservesColimit_of_preserves_colimit_cocone d.isColimitGluedCocone
    (IsColimit.ofIsoColimit (d.isColimit U) (Cocone.ext (d.pullbackGluedIso U).symm ?_))
  intro j
  obtain rfl : j = SingleObj.star G := rfl
  ext1
  apply pullback.hom_ext
  · erw [MorphismProperty.Comma.comp_left, Category.assoc, d.pullbackGluedIso_inv_fst]
    exact (d.fst_gluedCocone_ι _ _).symm.trans (pullback.lift_fst _ _ _).symm
  · erw [MorphismProperty.Comma.comp_left, Category.assoc, d.pullbackGluedIso_inv_snd]
    exact (MorphismProperty.Over.w ((d.cocone U).ι.app (SingleObj.star G))).trans
      (pullback.lift_snd (f := d.gluedCocone.pt.hom) (g := Y.directedAffineCover.f U) _ _ _).symm

include hP hP' in
/-- A quotient of a finite étale `Y`-scheme by a finite monoid action, computed in `P.Over ⊤ Y`,
is finite étale over `Y`: this is local on `Y`, and over an affine open it is the ring of
invariants. -/
lemma isFinite_and_etale_of_isColimit {c : Cocone D} (hc : IsColimit c)
    [IsFinite (D.obj (SingleObj.star G)).hom] [Etale (D.obj (SingleObj.star G)).hom] :
    IsFinite c.pt.hom ∧ Etale c.pt.hom := by
  suffices H : ∀ U, IsFinite (Y.directedAffineCover.pullbackHom c.pt.hom U) ∧
      Etale (Y.directedAffineCover.pullbackHom c.pt.hom U) by
    exact ⟨(IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite) _).mpr fun U ↦ (H U).1,
      (IsZariskiLocalAtTarget.iff_of_openCover (P := @Etale) _).mpr fun U ↦ (H U).2⟩
  intro U
  let F := MorphismProperty.Over.pullback P ⊤ (Y.directedAffineCover.f U)
  have := preservesColimit_pullback_directedAffineCover hP hP' D U
  let e := (isColimitOfPreserves F hc).coconePointUniqueUpToIso
    (isColimitQuotientCocone hP (D ⋙ F) hP')
  have : IsFinite ((D ⋙ F).obj (SingleObj.star G)).hom :=
    inferInstanceAs (IsFinite (pullback.snd _ _))
  have : Etale ((D ⋙ F).obj (SingleObj.star G)).hom :=
    inferInstanceAs (Etale (pullback.snd _ _))
  obtain ⟨h₁, h₂⟩ := isFinite_and_etale_quotientPt hP (D ⋙ F) hP'
  have he : e.hom.left ≫ (quotientPt (D ⋙ F) hP').hom = (F.obj c.pt).hom :=
    MorphismProperty.Over.w e.hom
  have : IsIso e.hom.left :=
    inferInstanceAs (IsIso ((MorphismProperty.Over.forget P ⊤ _ ⋙ Over.forget _).map e.hom))
  change IsFinite (F.obj c.pt).hom ∧ Etale (F.obj c.pt).hom
  rw [← he]
  exact ⟨inferInstance, inferInstance⟩

end Global

end AlgebraicGeometry.Scheme
