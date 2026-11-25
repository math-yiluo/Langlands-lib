/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Constructor
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Fractions
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Right derived functors computed on adapted complexes

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`,
in Situation 05S8, with the universal comparison of Definition 05S9 and
`equation-everywhere` (blueprint: lem-sf-right-derived-from-adapted-complexes).
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory

namespace CategoryTheory.Functor

section AdaptedSubcategory

variable {C : Type*} [Category* C] (W : MorphismProperty C)
  [W.HasLeftCalculusOfFractions] (P : ObjectProperty C)
  (hP : ∀ X : C, ∃ (Y : C) (r : X ⟶ Y), P Y ∧ W r)

private abbrev adaptedLocalizer : LocalizerMorphism (W.inverseImage P.ι) W where
  functor := P.ι
  map _ _ _ hf := hf

include hP in
private lemma adaptedCalculus : (W.inverseImage P.ι).HasLeftCalculusOfFractions where
  exists_leftFraction {X Y} φ := by
    obtain ⟨ψ, hψ⟩ :=
      (MorphismProperty.RightFraction.mk φ.s.hom φ.hs φ.f.hom).exists_leftFraction
    obtain ⟨Z, r, hr, hwr⟩ := hP ψ.Y'
    refine ⟨{ Y' := ⟨Z, hr⟩
              f := ObjectProperty.homMk (ψ.f ≫ r)
              s := ObjectProperty.homMk (ψ.s ≫ r)
              hs := W.comp_mem _ _ ψ.hs hwr }, ?_⟩
    apply ObjectProperty.hom_ext
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ r) hψ).trans (Category.assoc _ _ _))
  ext {X' X Y} f g s hs hfg := by
    obtain ⟨Z, t, ht, h⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
      f.hom g.hom s.hom hs (congrArg InducedCategory.Hom.hom hfg)
    obtain ⟨Z', r, hr, hwr⟩ := hP Z
    refine ⟨⟨Z', hr⟩, ObjectProperty.homMk (t ≫ r), W.comp_mem _ _ ht hwr, ?_⟩
    apply ObjectProperty.hom_ext
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ r) h).trans (Category.assoc _ _ _))

omit [W.HasLeftCalculusOfFractions] in
include hP in
private lemma adaptedHasResolutions : (adaptedLocalizer W P).HasRightResolutions := by
  intro X
  obtain ⟨Y, r, hr, hwr⟩ := hP X
  exact ⟨{ X₁ := ⟨Y, hr⟩, w := r, hw := hwr }⟩

include hP in
private lemma adaptedConnected (X : C) :
    IsConnected ((adaptedLocalizer W P).RightResolution X) := by
  have := adaptedHasResolutions W P hP X
  apply zigzag_isConnected
  intro R S
  obtain ⟨ψ, hψ⟩ :=
    (MorphismProperty.RightFraction.mk R.w R.hw S.w).exists_leftFraction
  obtain ⟨Z, r, hr, hwr⟩ := hP ψ.Y'
  let T : (adaptedLocalizer W P).RightResolution X :=
    { X₁ := ⟨Z, hr⟩
      w := S.w ≫ ψ.s ≫ r
      hw := W.comp_mem _ _ S.hw (W.comp_mem _ _ ψ.hs hwr) }
  have a : R ⟶ T :=
    { f := ObjectProperty.homMk (ψ.f ≫ r)
      comm := by
        change R.w ≫ (ψ.f ≫ r) = S.w ≫ (ψ.s ≫ r)
        simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ r) hψ.symm }
  have b : S ⟶ T := { f := ObjectProperty.homMk (ψ.s ≫ r) }
  exact (Zigzag.of_hom a).trans (Zigzag.of_inv b)

include hP in
private lemma adaptedArrowResolutions : (adaptedLocalizer W P).arrow.HasRightResolutions := by
  intro f
  obtain ⟨I, r, hr, hwr⟩ := hP f.left
  obtain ⟨ψ, hψ⟩ :=
    (MorphismProperty.RightFraction.mk r hwr f.hom).exists_leftFraction
  obtain ⟨J, s, hs, hws⟩ := hP ψ.Y'
  refine ⟨{ X₁ := Arrow.mk (ObjectProperty.homMk (ψ.f ≫ s) :
              (⟨I, hr⟩ : P.FullSubcategory) ⟶ ⟨J, hs⟩)
            w := Arrow.homMk r (ψ.s ≫ s) ?_
            hw := ⟨hwr, W.comp_mem _ _ ψ.hs hws⟩ }⟩
  change r ≫ (ψ.f ≫ s) = f.hom ≫ (ψ.s ≫ s)
  simpa only [Category.assoc] using congrArg (fun g ↦ g ≫ s) hψ.symm

include hP in
private lemma adaptedLocalizedEquivalence :
    (adaptedLocalizer W P).IsLocalizedEquivalence := by
  let W₁ := W.inverseImage P.ι
  let Φ := adaptedLocalizer W P
  have := adaptedCalculus W P hP
  let L := W₁.Q
  let Q := W.Q
  let F := Φ.localizedFunctor L Q
  let e : P.ι ⋙ Q ≅ L ⋙ F :=
    (Localization.fac (Φ.functor ⋙ Q) (Φ.inverts Q) L).symm
  let : CatCommSq Φ.functor L Q F := ⟨e⟩
  have : L.EssSurj := Localization.essSurj L W₁
  have : F.Faithful := by
    apply Functor.faithful_of_comp_of_hasLeftCalculusOfFractions L W₁ F
    intro X Y f g hfg
    have h : Q.map f.hom = Q.map g.hom := by
      apply (cancel_mono (e.hom.app Y)).1
      exact (e.hom.naturality f).trans
        ((congrArg (fun k ↦ e.hom.app X ≫ k) hfg).trans (e.hom.naturality g).symm)
    obtain ⟨Z, t, ht, h⟩ := (MorphismProperty.map_eq_iff_postcomp Q W _ _).1 h
    obtain ⟨Z', r, hr, hwr⟩ := hP Z
    let t' : Y ⟶ (⟨Z', hr⟩ : P.FullSubcategory) := ObjectProperty.homMk (t ≫ r)
    have ht' : W₁ t' := W.comp_mem _ _ ht hwr
    have : IsIso (L.map t') := Localization.inverts L W₁ t' ht'
    rw [← cancel_mono (L.map t'), ← L.map_comp, ← L.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    dsimp [t']
    rw [← Category.assoc, ← Category.assoc, h]
  have : F.Full := by
    apply F.full_of_comp_essSurj L
    intro X Y g
    obtain ⟨φ, hφ⟩ := Localization.exists_leftFraction Q W
      (e.hom.app X ≫ g ≫ e.inv.app Y)
    obtain ⟨Z, r, hr, hwr⟩ := hP φ.Y'
    let Z' : P.FullSubcategory := ⟨Z, hr⟩
    let a : X ⟶ Z' := ObjectProperty.homMk (φ.f ≫ r)
    let b : Y ⟶ Z' := ObjectProperty.homMk (φ.s ≫ r)
    have hb : W₁ b := W.comp_mem _ _ φ.hs hwr
    have : IsIso (L.map b) := Localization.inverts L W₁ b hb
    refine ⟨L.map a ≫ CategoryTheory.inv (L.map b), ?_⟩
    rw [F.map_comp, F.map_inv]
    apply (cancel_mono (F.map (L.map b))).1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    apply (cancel_epi (e.hom.app X)).1
    have ha : F.map (L.map a) ≫ e.inv.app Z' = e.inv.app X ≫ Q.map a.hom :=
      e.inv.naturality a
    have hb' : F.map (L.map b) ≫ e.inv.app Z' = e.inv.app Y ≫ Q.map b.hom :=
      e.inv.naturality b
    apply (cancel_mono (e.inv.app Z')).1
    simp only [Category.assoc]
    rw [ha, hb', Iso.hom_inv_id_app_assoc]
    have : IsIso (Q.map φ.s) := Localization.inverts Q W φ.s φ.hs
    have hh := congrArg (fun k ↦ k ≫ Q.map φ.s) hφ
    rw [MorphismProperty.LeftFraction.map_comp_map_s] at hh
    dsimp [a, b]
    simpa only [Q.map_comp, Category.assoc] using
      congrArg (fun k ↦ k ≫ Q.map r) hh.symm
  have : Φ.HasRightResolutions := adaptedHasResolutions W P hP
  have : (P.ι ⋙ Q).EssSurj := Φ.essSurj_of_hasRightResolutions Q
  have : F.EssSurj := by
    constructor
    intro Y
    obtain ⟨X, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (P.ι ⋙ Q) Y
    exact ⟨L.obj X, ⟨(e.app X).symm ≪≫ i⟩⟩
  have : F.IsEquivalence := { }
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ L Q F

include hP in
private lemma adaptedDerivability : (adaptedLocalizer W P).IsRightDerivabilityStructure := by
  have := adaptedLocalizedEquivalence W P hP
  have := adaptedConnected W P hP
  have := adaptedArrowResolutions W P hP
  exact LocalizerMorphism.IsRightDerivabilityStructure.mk' _

end AdaptedSubcategory

/-- An exact functor on the homotopy category has a total right derived functor computed
on any class admitting right quasi-isomorphism replacements on which it inverts
quasi-isomorphisms. The class is a set of objects of the homotopy category, whose objects
are complexes; no invariance or closure condition on the class is required.
`IsRightDerivedFunctor` is the universal property: for every `T` and `β : G ⟶ Qh ⋙ T`,
there is a unique `u : RG ⟶ T` such that `α ≫ whiskerLeft Qh u = β`.

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`,
right-derived assertion in Situation 05S8; Definition 05S9 and `equation-everywhere`
(blueprint: lem-sf-right-derived-from-adapted-complexes).

Proof:
1. Quasi-isomorphisms in the homotopy category admit a left calculus of fractions
   (`lem-pc-quasi-isomorphisms-multiplicative-system`) and satisfy two out of three,
   as can be checked on every cohomology functor. Choose replacements `r_K : K ⟶ I_K`
   with `I_K` in the class. These choices need not be functorial.
2. A derived morphism between adapted objects is a left fraction `(a : I ⟶ P, b : J ⟶ P)`
   with `b` a quasi-isomorphism (`lem-pc-left-localization-fraction-representation`).
   Replace its common target to make `P` adapted, and assign `G.map a ≫ inv (G.map b)`.
3. Equal fractions have common postcompositions with equal numerators and denominators
   (`lem-pc-left-localization-fraction-equality`). Two out of three makes these
   postcompositions quasi-isomorphisms. Replace the common target again; all resulting
   objects are adapted, so cancellation of the invertible images proves independence.
   The fraction `(f, identity)` shows that actual arrows are sent to `G.map f`.
4. For composable fractions, the left Ore axiom gives a common square for the middle
   denominator and numerator. Replace its target by an adapted object. The square,
   functoriality of `G`, and cancellation of the two invertible denominator images show
   compatibility with composition. Thus the assignment is a functor on localized Hom
   sets between adapted objects; denote it by `Gbar`.
5. Put `H(K) = G(I_K)` and send `f : K ⟶ L` to the value of `Gbar` on
   `inv (Qh.map r_K) ≫ Qh.map f ≫ Qh.map r_L`. This functor inverts quasi-isomorphisms.
   An Ore square for `r_K` and `f ≫ r_L`, followed by an adapted replacement, proves
   naturality of `α0_K = G.map r_K`. Its components at adapted objects are invertible,
   and `H.map r_K = α0_(I_K)` by the actual-arrow computation in Step 3.
6. Localize `H` using `lem-weil-pbc-localization-universal-property` to obtain `RG`
   and `φ : Qh ⋙ RG ≅ H`. Set `α_K = α0_K ≫ φ.inv.app K`. Its components on the
   adapted class are isomorphisms.
7. For arbitrary `T` and `β : G ⟶ Qh ⋙ T`, set
   `v_K = β.app I_K ≫ inv (T.map (Qh.map r_K))`. The Ore square in Step 5 and
   naturality of `β` at its two adapted arrows prove that `v : H ⟶ Qh ⋙ T` is natural.
   Naturality at `r_K` gives `α0_K ≫ v_K = β.app K`. Lift `φ.hom ≫ v` through
   localization to obtain `u : RG ⟶ T` with `α ≫ whiskerLeft Qh u = β`.
8. If `u'` has the same compatibility, put `w_K = φ.inv.app K ≫ u'.app (Qh.obj K)`.
   Naturality at `r_K`, together with `H.map r_K = α0_(I_K)`, forces
   `w_K = β.app I_K ≫ inv (T.map (Qh.map r_K)) = v_K`. Hence `u'` and `u` agree
   after precomposition by `Qh`; uniqueness for localization makes them equal.
-/
theorem exists_rightDerivedFunctor_of_adapted_complexes
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (G : HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory B)
    [G.CommShift ℤ] [G.IsTriangulated]
    (𝓘 : Set (HomotopyCategory A (ComplexShape.up ℤ)))
    (h_replacements : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      ∃ (I : HomotopyCategory A (ComplexShape.up ℤ)) (r : K ⟶ I),
        I ∈ 𝓘 ∧ HomotopyCategory.quasiIso A (ComplexShape.up ℤ) r)
    (h_inverts : ∀ (I J : HomotopyCategory A (ComplexShape.up ℤ)),
      I ∈ 𝓘 → J ∈ 𝓘 → ∀ (s : I ⟶ J),
        HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s → IsIso (G.map s)) :
    ∃ (RG : DerivedCategory A ⥤ DerivedCategory B)
      (α : G ⟶ (DerivedCategory.Qh (C := A)) ⋙ RG),
      RG.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ∧
        ∀ (I : HomotopyCategory A (ComplexShape.up ℤ)), I ∈ 𝓘 → IsIso (α.app I) := by
  let W := HomotopyCategory.quasiIso A (ComplexShape.up ℤ)
  let P : ObjectProperty (HomotopyCategory A (ComplexShape.up ℤ)) := fun K ↦ K ∈ 𝓘
  let Φ := adaptedLocalizer W P
  have := adaptedDerivability W P h_replacements
  have h : Φ.Derives G := fun I J s hs ↦
    h_inverts I.obj J.obj I.property J.property s.hom hs
  have := h.hasPointwiseRightDerivedFunctor
  refine ⟨G.totalRightDerived (DerivedCategory.Qh (C := A)) W,
    G.totalRightDerivedUnit (DerivedCategory.Qh (C := A)) W, inferInstance, ?_⟩
  intro I hI
  exact h.isIso_of_isRightDerivedFunctor _ (⟨I, hI⟩ : P.FullSubcategory)

end CategoryTheory.Functor
