/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.Mathlib.Topology.NoetherianSpace
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The divisor sequence of a punctured curve

Let `C̄` be a smooth proper connected curve over an algebraically closed field `k`, let
`S ⊆ C̄` be a finite set of closed points and `j : C = C̄ ∖ S ⟶ C̄` the open immersion of its
complement. Then

```
  0 ──▶ 𝔾ₘ ──▶ j_* 𝔾ₘ ──▶ ⨁_{P ∈ S} i_{P*} ℤ ──▶ 0
```

is a short exact sequence of étale sheaves on `C̄`, the third map sending a function on `C`
to its orders of vanishing at the punctures.

The proof follows that of the divisor sequence of an integral regular scheme
(`AlgebraicGeometry.Scheme.nonempty_cokernel_toGenericGm_iso`): both `j_* 𝔾ₘ` and
`⨁_{P ∈ S} i_{P*} ℤ` map to the sheaf `V ↦ (V → ℤ)` of functions on points, the first by the
orders of vanishing at the points over `S` and the second by extension by zero, and the
cokernel of `𝔾ₘ ⟶ j_* 𝔾ₘ` is identified on geometric stalks
(`AlgebraicGeometry.Scheme.nonempty_cokernel_iso_of_sheafFiber`). The local inputs are that a
function on the punctured neighbourhood of a point over `S` of order zero there extends to a
unit, and that a uniformiser at a point over `S` is a unit on the punctured neighbourhood.

## Main definitions

- `AlgebraicGeometry.Scheme.lowerStarGmSheafMap`: the restriction `g_* 𝔾ₘ ⟶ (h ≫ g)_* 𝔾ₘ` of
  units along a morphism `h`.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_shortExact_divisorSequence`: the divisor sequence of a
  punctured curve is short exact.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Order TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme

variable {X Z Z' : Scheme.{u}} (g : Z ⟶ X) (h : Z' ⟶ Z) (g' : Z' ⟶ X) (hh : h ≫ g = g')

/-- The restriction of units `g_* 𝔾ₘ ⟶ g'_* 𝔾ₘ` along a morphism `h : Z' ⟶ Z` with
`h ≫ g = g'`: on an étale `X`-scheme `V` it is the map `Γ(V ×_X Z, 𝒪)ˣ ⟶ Γ(V ×_X Z', 𝒪)ˣ`
induced by `V ×_X Z' ⟶ V ×_X Z`. -/
noncomputable def lowerStarGmSheafMap :
    (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj Z.gmSheaf ⟶
      (Etale.lowerStar AddCommGrpCat.{u + 1} g').obj Z'.gmSheaf :=
  ⟨{ app V := CommRingCat.unitsAddCommGrpULift.map
        (pullback.map V.unop.hom g' V.unop.hom g (𝟙 _) h (𝟙 _) (by simp) (by simp [hh])).appTop
     naturality {V W} φ := by
      change CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _ =
        CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      change ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ.unop).left.appTop ≫ _ =
        _ ≫ ((MorphismProperty.Over.pullback @Etale ⊤ g').map φ.unop).left.appTop
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
        show ((MorphismProperty.Over.pullback @Etale ⊤ g).map φ.unop).left =
          pullback.map _ _ _ _ φ.unop.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
        show ((MorphismProperty.Over.pullback @Etale ⊤ g').map φ.unop).left =
          pullback.map _ _ _ _ φ.unop.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
        pullback.map_comp, pullback.map_comp]
      congr 1 }⟩

@[reassoc (attr := simp)]
lemma gmSheafToLowerStarGmSheaf_comp_lowerStarGmSheafMap :
    gmSheafToLowerStarGmSheaf g ≫ lowerStarGmSheafMap g h g' hh = gmSheafToLowerStarGmSheaf g' := by
  ext V : 3
  change CommRingCat.unitsAddCommGrpULift.map _ ≫ CommRingCat.unitsAddCommGrpULift.map _ =
    CommRingCat.unitsAddCommGrpULift.map _
  rw [← Functor.map_comp]
  congr 1
  change (pullback.fst V.unop.hom g).appTop ≫
      (pullback.map V.unop.hom g' V.unop.hom g (𝟙 _) h (𝟙 _) (by simp) (by simp [hh])).appTop =
      (pullback.fst V.unop.hom g').appTop
  rw [← Scheme.Hom.comp_appTop, pullback.lift_fst, Category.comp_id]

/-- **Isolating a point of a fibre and a uniformiser.** Let `g : V ⟶ X` be locally quasi-finite
with `V` locally noetherian, `y` a point of `V` with `g y` closed, at which the local ring is a
discrete valuation ring with uniformiser `π`. Then `π` extends to a section `s` on an open
neighbourhood `W` of `y` such that every other point of `W` lies outside the fibre of `g y` and in
`D(s)`. The other generisation of `y` lies in `D(s)` since `π ≠ 0`, and a noetherian argument
(`TopologicalSpace.NoetherianSpace.exists_isOpen_inter_eq_singleton`) isolates `y`. -/
lemma exists_opens_isolate {V X : Scheme.{u}} (g : V ⟶ X) [LocallyQuasiFinite g]
    [IsLocallyNoetherian V] (y : V) (hyc : IsClosed {g y})
    [IsDomain (V.presheaf.stalk y)] [IsDiscreteValuationRing (V.presheaf.stalk y)]
    {π : V.presheaf.stalk y} (hπ : Irreducible π) :
    ∃ (W : V.Opens) (hyW : y ∈ W) (s : Γ(V, W)), V.presheaf.germ W y hyW s = π ∧
      ∀ y' ∈ W, y' ≠ y → g y' ≠ g y ∧ y' ∈ V.basicOpen s := by
  obtain ⟨U₁, hyU₁, s₁, hs₁⟩ := TopCat.Presheaf.exists_germ_eq V.presheaf (x := y) π
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hyU₀, hU₀U₁⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open hyU₁ U₁.2
  let s := V.presheaf.map (homOfLE hU₀U₁).op s₁
  have hs : V.presheaf.germ U₀ y hyU₀ s = π := by
    exact (V.presheaf.germ_res_apply (homOfLE hU₀U₁) y hyU₀ s₁).trans hs₁
  -- `y` is a closed point
  have hy : IsClosed ({y} : Set V) := by
    refine isClosed_iff_clusterPt.2 fun z hz ↦ ?_
    have hyz : y ⤳ z := by
      rw [specializes_iff_mem_closure]; exact mem_closure_iff_clusterPt.2 hz
    have hgz : g z = g y := (hyz.map g.continuous).mem_closed hyc rfl
    exact (g.eq_of_specializes_of_apply_eq hyz hgz.symm).symm
  -- the generisations of `y` other than `y` lie in `D(s)` and not over `g y`
  have hgen : ∀ z : V, z ⤳ y → z ≠ y → g z ≠ g y ∧ z ∈ V.basicOpen s := by
    intro z hzy hne
    refine ⟨fun h ↦ hne (g.eq_of_specializes_of_apply_eq hzy h), ?_⟩
    have hzU₀ : z ∈ U₀ := hzy.mem_open U₀.2 hyU₀
    have hz : z ∈ Set.range (V.fromSpecStalk y) := by
      rw [Scheme.range_fromSpecStalk]; exact hzy
    obtain ⟨p, rfl⟩ := hz
    have hp : p.asIdeal = ⊥ := by
      by_contra hbot
      have hmax := p.isPrime.isMaximal hbot
      exact hne (by
        rw [show p = IsLocalRing.closedPoint _ from
          PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax), Scheme.fromSpecStalk_closedPoint])
    have hmem : p ∈ V.fromSpecStalk y ⁻¹ᵁ V.basicOpen s := by
      rw [Scheme.preimage_basicOpen, Scheme.fromSpecStalk_app hyU₀]
      change p ∈ (Spec _).basicOpen ((Spec _).presheaf.map _ ((Scheme.ΓSpecIso _).inv
        (V.presheaf.germ U₀ y hyU₀ s)))
      rw [Scheme.basicOpen_res, hs]
      refine ⟨hzU₀, ?_⟩
      change p ∈ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv π)
      rw [basicOpen_eq_of_affine]
      change π ∉ p.asIdeal
      rw [hp]
      exact hπ.ne_zero
    exact hmem
  -- isolate `y` in the noetherian space `U₀`
  have : NoetherianSpace U₀ := @noetherianSpace_of_isAffineOpen _ U₀ hU₀
    (IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩)
  let y₀ : U₀ := ⟨y, hyU₀⟩
  let Z : Set U₀ := {q | g q.1 = g y ∨ q.1 ∉ V.basicOpen s}
  have hZ : IsClosed Z := by
    refine IsClosed.union ?_ ?_
    · exact hyc.preimage (g.continuous.comp continuous_subtype_val)
    · exact ((V.basicOpen s).2.preimage continuous_subtype_val).isClosed_compl
  have hy₀ : IsClosed ({y₀} : Set U₀) := by
    have e : ({y₀} : Set U₀) = Subtype.val ⁻¹' {y} := by
      ext q
      exact ⟨fun h ↦ h ▸ rfl, fun h ↦ Subtype.ext h⟩
    rw [e]
    exact hy.preimage continuous_subtype_val
  obtain ⟨W₀, hW₀, hy₀W₀, hW₀Z⟩ := NoetherianSpace.exists_isOpen_inter_eq_singleton
    (α := U₀) hZ (y := y₀) (Or.inl rfl) hy₀ fun q hq hqy ↦ by
      by_contra hne
      have := hgen q.1 (hqy.map continuous_subtype_val) fun h ↦ hne (Subtype.ext h)
      rcases hq with hq | hq
      · exact this.1 hq
      · exact hq this.2
  let W : V.Opens := ⟨Subtype.val '' W₀, U₀.2.isOpenMap_subtype_val W₀ hW₀⟩
  have hWU₀ : W ≤ U₀ := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  refine ⟨W, ⟨y₀, hy₀W₀, rfl⟩, V.presheaf.map (homOfLE hWU₀).op s,
    (V.presheaf.germ_res_apply (homOfLE hWU₀) y _ s).trans hs, ?_⟩
  rintro _ ⟨q, hq, rfl⟩ hne
  have hqZ : q ∉ Z := fun hqZ ↦ hne (by
    have : q ∈ W₀ ∩ Z := ⟨hq, hqZ⟩
    rw [hW₀Z] at this
    rw [this])
  have hqZ' : g q.1 ≠ g y ∧ q.1 ∈ V.basicOpen s :=
    ⟨fun h ↦ hqZ (Or.inl h), of_not_not fun h ↦ hqZ (Or.inr h)⟩
  refine ⟨hqZ'.1, ?_⟩
  rw [Scheme.basicOpen_res]
  exact ⟨⟨q, hq, rfl⟩, hqZ'.2⟩
end Scheme

namespace IsCurve

variable {C : Scheme.{u}} [IsIntegral C] [IsLocallyNoetherian C] [IsRegular C]
  {U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] (iU : Spec C.functionField ⟶ U)
  (hiU : iU ≫ j = C.fromSpecFunctionField)

omit [IsLocallyNoetherian C] [IsRegular C] [IsOpenImmersion j] in
/-- The generic point of a one-dimensional integral scheme is not a closed point. -/
lemma genericPoint_notMem (hC : topologicalKrullDim C = 1) {S : Set C}
    (hSc : ∀ P ∈ S, IsClosed {P}) : genericPoint C ∉ S := by
  intro hη
  have h₁ : (Set.univ : Set C) = {genericPoint C} := by
    rw [← genericPoint_spec C, (hSc _ hη).closure_eq]
  have : Subsingleton C := ⟨fun a b ↦ by
    have ha : a ∈ ({genericPoint C} : Set C) := h₁ ▸ Set.mem_univ a
    have hb : b ∈ ({genericPoint C} : Set C) := h₁ ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]⟩
  have h₂ := topologicalKrullDim_zero_of_discreteTopology C
  rw [hC] at h₂
  exact absurd h₂ (by decide)

omit [IsLocallyNoetherian C] [IsRegular C] [IsOpenImmersion j] in
/-- A closed point of a one-dimensional integral scheme has codimension one. -/
lemma coheight_eq_one_of_mem (hC : topologicalKrullDim C = 1) {S : Set C}
    (hSc : ∀ P ∈ S, IsClosed {P}) {P : C} (hP : P ∈ S) : coheight P = 1 := by
  have hle : (coheight P : WithBot ℕ∞) ≤ 1 := hC ▸ coheight_le_topologicalKrullDim P
  have hne : coheight P ≠ 0 := by
    intro h0
    have hmax : IsMax P := Order.coheight_eq_zero.1 h0
    have h₁ : P ≤ genericPoint C :=
      Scheme.le_iff_specializes.2 ((genericPoint_spec C).specializes (Set.mem_univ P))
    have h₂ := hmax h₁
    rw [Scheme.le_iff_specializes] at h₁ h₂
    exact genericPoint_notMem hC hSc ((h₁.antisymm h₂).eq ▸ hP)
  have hle' : coheight P ≤ 1 := by exact_mod_cast hle
  exact le_antisymm hle' (Order.one_le_iff_ne_zero.2 hne)


omit [IsLocallyNoetherian C] in
/-- On an irreducible étale `C`-scheme `W`, a function on `W ×_C U` is determined by its image in
the local generic ring at a point `y` of codimension one: its basic open, if nonempty, contains
the generic point of `W ×_C U`, which is the image of the generic fibre of `Spec 𝒪_{W,y}`. -/
lemma injective_toLocalGenericRing_appTop (W : C.Etale) [PreirreducibleSpace W.left]
    {y : W.left} (hy : coheight (W.hom y) = 1) :
    Function.Injective (fun a : Γ(pullback W.hom j, ⊤) ↦ Scheme.Etale.toLocalGenericRing W y
      ((pullback.map W.hom C.fromSpecFunctionField W.hom j (𝟙 _) iU (𝟙 _) (by simp)
        (by simp [hiU])).appTop a)) := by
  let X := pullback W.hom j
  let P := pullback (W.left.fromSpecStalk y ≫ W.hom) C.fromSpecFunctionField
  let m : P ⟶ X := pullback.map _ _ _ _ (W.left.fromSpecStalk y) (𝟙 _) (𝟙 _) (by simp)
    (by simp) ≫ pullback.map W.hom C.fromSpecFunctionField W.hom j (𝟙 _) iU (𝟙 _) (by simp)
      (by simp [hiU])
  have hm : (fun a : Γ(pullback W.hom j, ⊤) ↦ Scheme.Etale.toLocalGenericRing W y
      ((pullback.map W.hom C.fromSpecFunctionField W.hom j (𝟙 _) iU (𝟙 _) (by simp)
        (by simp [hiU])).appTop a)) = m.appTop.hom := by
    funext a
    simp only [m, Scheme.Hom.comp_appTop]
    rfl
  rw [hm]
  refine (injective_iff_map_eq_zero _).2 fun a ha ↦ ?_
  by_contra hne
  -- `P` is nonempty, its local generic ring being a field
  have : IsDiscreteValuationRing (W.left.presheaf.stalk y) :=
    Scheme.Etale.isDiscreteValuationRing_stalk W hy
  let := (Scheme.Etale.stalkToLocalGenericRing W y).hom.toAlgebra
  have := Scheme.Etale.isFractionRing_localGenericRing W y
  have hP : Nonempty P := by
    by_contra hP
    rw [not_nonempty_iff] at hP
    have : Nontrivial (Scheme.Etale.localGenericRing W y) :=
      (IsLocalization.algEquiv (nonZeroDivisors (W.left.presheaf.stalk y))
        (Scheme.Etale.localGenericRing W y)
        (FractionRing (W.left.presheaf.stalk y))).toEquiv.nontrivial
    have hs : Subsingleton Γ(P, ⊤) := inferInstance
    exact @not_subsingleton (Scheme.Etale.localGenericRing W y) _ hs
  obtain ⟨t₀⟩ := hP
  -- `X` is reduced and irreducible
  have hst : ∀ x : W.left, _root_.IsReduced (W.left.presheaf.stalk x) := fun _ ↦ inferInstance
  have : IsReduced ((𝟭 Scheme).obj W.left) :=
    @isReduced_of_isReduced_stalk ((𝟭 Scheme).obj W.left) hst
  have : IsReduced X := isReduced_of_isOpenImmersion (pullback.fst W.hom j)
  have : PreirreducibleSpace ((𝟭 Scheme).obj W.left) := ‹PreirreducibleSpace W.left›
  have : PreirreducibleSpace X :=
    (pullback.fst W.hom j).isOpenEmbedding.preirreducibleSpace
  have : IrreducibleSpace X := ⟨⟨m t₀⟩⟩
  -- `m t₀` is a maximal point of `X`
  let h : X ⟶ C := pullback.fst W.hom j ≫ W.hom
  have hgen (z : X) (hz : h z ⤳ genericPoint C) : h z = genericPoint C :=
    (hz.antisymm ((genericPoint_spec C).specializes (Set.mem_univ _))).eq
  have hmt : h (m t₀) ⤳ genericPoint C := by
    have : h (m t₀) = C.fromSpecFunctionField
        (pullback.snd (W.left.fromSpecStalk y ≫ W.hom) C.fromSpecFunctionField t₀) := by
      change (m ≫ h) t₀ = _
      have e : m ≫ h = pullback.snd (W.left.fromSpecStalk y ≫ W.hom) C.fromSpecFunctionField ≫
          C.fromSpecFunctionField := by
        rw [← pullback.condition]
        simp [m, h]
      rw [e]
      rfl
    rw [this]
    have := Set.mem_range_self (f := C.fromSpecStalk (genericPoint C))
      (pullback.snd (W.left.fromSpecStalk y ≫ W.hom) C.fromSpecFunctionField t₀)
    rwa [Scheme.range_fromSpecStalk] at this
  have hmax : ∀ z : X, z ⤳ m t₀ → z = m t₀ := fun z hz ↦
    h.eq_of_specializes_of_apply_eq hz
      ((hgen z ((hz.map h.continuous).trans hmt)).trans (hgen _ hmt).symm)
  -- the basic open of `a` contains the generic point, hence `m t₀`
  have hne' : X.basicOpen a ≠ ⊥ := fun h' ↦ hne ((basicOpen_eq_bot_iff a).1 h')
  have hξ : genericPoint X ∈ X.basicOpen a :=
    ((genericPoint_spec X).mem_open_set_iff (X.basicOpen a).2).2 (by
      obtain ⟨w, hw⟩ : (X.basicOpen a : Set X).Nonempty :=
        Set.nonempty_iff_ne_empty.2 fun h' ↦ hne'
          (TopologicalSpace.Opens.ext (h'.trans TopologicalSpace.Opens.coe_bot.symm))
      exact ⟨w, Set.mem_univ _, hw⟩)
  have hz : m t₀ ∈ X.basicOpen a := by
    have hspec : m t₀ ⤳ genericPoint X := by
      rw [hmax (genericPoint X) ((genericPoint_spec X).specializes (Set.mem_univ _))]
    exact hspec.mem_open (X.basicOpen a).2 hξ
  have : t₀ ∈ m ⁻¹ᵁ X.basicOpen a := hz
  rw [Scheme.preimage_basicOpen_top] at this
  change t₀ ∈ P.basicOpen (m.appTop.hom a) at this
  have h0 : t₀ ∈ P.basicOpen (0 : Γ(P, ⊤)) := ha ▸ this
  simp at h0


/-- **Units of order zero at the punctures extend.** Let `C` be an integral regular noetherian
scheme of dimension one, `S` a finite set of closed points, `j : U ⟶ C` the open immersion of
the complement of `S`, and `V` an étale `C`-scheme. A unit `f` on `V ×_C U` whose order at the
points of `V` over `S` vanishes extends, near every point of `V`, to a unit of `𝒪_V`: at a point
over `S` the local ring is a discrete valuation ring and `f` is a unit of it
(`Ring.exists_eq_algebraMap_of_ordOf_eq_zero`); its extension agrees with `f` on the punctured
neighbourhood by `AlgebraicGeometry.IsCurve.injective_toLocalGenericRing_appTop`.
(blueprint: `lemma-cohomology-multiplicative-group--6`, exactness in the middle) -/
lemma exists_eq_of_ord_eq_zero (hC : topologicalKrullDim C = 1) {S : Set C} (hS : S.Finite)
    (hSc : ∀ P ∈ S, IsClosed {P}) (hj : Set.range j = Sᶜ) (V : C.Etale) (y : V.left)
    (f : Γ(pullback V.hom j, ⊤)ˣ)
    (hf : ∀ y', V.hom y' ∈ S → Scheme.Etale.ord V y'
      ((pullback.map V.hom C.fromSpecFunctionField V.hom j (𝟙 _) iU (𝟙 _) (by simp)
        (by simp [hiU])).appTop f.val) = 0) :
    ∃ (W : V.left.Opens) (_ : y ∈ W) (u : Γ(Scheme.Etale.ofOpens V W |>.left, ⊤)ˣ),
      (pullback.fst (Scheme.Etale.ofOpens V W).hom j).appTop u.val =
        ((MorphismProperty.Over.pullback @Etale ⊤ j).map
          (Scheme.Etale.ofOpensι V W)).left.appTop f.val := by
  have hSclosed (T : Set C) (hT : T ⊆ S) : IsClosed T := by
    rw [← Set.biUnion_of_singleton T]
    exact (hS.subset hT).isClosed_biUnion fun P hP ↦ hSc P (hT hP)
  by_cases hyS : V.hom y ∈ S
  swap
  · -- away from the punctures `V ×_C U ⟶ V` is an isomorphism
    let W : V.left.Opens :=
      ⟨V.hom ⁻¹' Sᶜ, ((hSclosed S le_rfl).preimage V.hom.continuous).isOpen_compl⟩
    let W' := Scheme.Etale.ofOpens V W
    have : IsIso (pullback.fst W'.hom j) := by
      rw [isIso_iff_isOpenImmersion_and_surjective]
      refine ⟨inferInstance, ⟨fun w ↦ ?_⟩⟩
      have hw : W'.hom w ∈ Set.range j := by rw [hj]; exact w.2
      exact (Set.ext_iff.1 (Scheme.Pullback.range_fst W'.hom j) w).2 hw
    let res : Γ(pullback V.hom j, ⊤) →+* Γ(pullback W'.hom j, ⊤) :=
      ((MorphismProperty.Over.pullback @Etale ⊤ j).map (Scheme.Etale.ofOpensι V W)).left.appTop.hom
    let inv' : Γ(pullback W'.hom j, ⊤) →+* Γ(W'.left, ⊤) :=
      (inv (pullback.fst W'.hom j)).appTop.hom
    refine ⟨W, hyS, Units.map inv'.toMonoidHom (Units.map res.toMonoidHom f), ?_⟩
    change ((inv (pullback.fst W'.hom j)).appTop ≫ (pullback.fst W'.hom j).appTop) _ = _
    rw [← Scheme.Hom.comp_appTop, IsIso.hom_inv_id, Scheme.Hom.id_appTop]
    rfl
  -- at a puncture, `f` is a unit of the discrete valuation ring `𝒪_{V,y}`
  have hcoh : coheight (V.hom y) = 1 := coheight_eq_one_of_mem hC hSc hyS
  have : IsDiscreteValuationRing (V.left.presheaf.stalk y) :=
    Scheme.Etale.isDiscreteValuationRing_stalk V hcoh
  let := (Scheme.Etale.stalkToLocalGenericRing V y).hom.toAlgebra
  have := Scheme.Etale.isFractionRing_localGenericRing V y
  let genV : Γ(pullback V.hom j, ⊤) ⟶ Γ(pullback V.hom C.fromSpecFunctionField, ⊤) :=
    (pullback.map V.hom C.fromSpecFunctionField V.hom j (𝟙 _) iU (𝟙 _) (by simp)
      (by simp [hiU])).appTop
  have hf₀ := hf y hyS
  rw [Scheme.Etale.ord, ite_eq_left hcoh] at hf₀
  obtain ⟨r, hr⟩ := Ring.exists_eq_algebraMap_of_ordOf_eq_zero
    (Units.map ((Scheme.Etale.toLocalGenericRing V y).hom.comp genV.hom).toMonoidHom f) hf₀
  -- spread `r` to a unit on an irreducible neighbourhood avoiding the other punctures
  let g : V.left ⟶ C := V.hom
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨U₁, hyU₁, s₁, hs₁⟩ := TopCat.Presheaf.exists_germ_eq V.left.presheaf (x := y) r.val
  have hyD : y ∈ V.left.basicOpen s₁ := (V.left.mem_basicOpen s₁ y hyU₁).2 (hs₁ ▸ r.isUnit)
  obtain ⟨W₁, hyW₁, hW₁⟩ := Scheme.exists_opens_isPreirreducible y
  let T : V.left.Opens := ⟨(V.hom ⁻¹' (S \ {V.hom y}))ᶜ,
    ((hSclosed _ Set.sdiff_subset).preimage V.hom.continuous).isOpen_compl⟩
  let W : V.left.Opens := W₁ ⊓ V.left.basicOpen s₁ ⊓ T
  have hyW : y ∈ W := ⟨⟨hyW₁, hyD⟩, fun h ↦ h.2 rfl⟩
  let W' := Scheme.Etale.ofOpens V W
  have hWirr : IsPreirreducible (W : Set V.left) :=
    hW₁.open_subset W.2 fun _ hw ↦ hw.1.1
  have : PreirreducibleSpace W'.left := Subtype.preirreducibleSpace hWirr
  let y₀ : W'.left := ⟨y, hyW⟩
  -- the unit `s₁` on `W`
  have hWD : W ≤ V.left.basicOpen s₁ := fun _ hw ↦ hw.1.2
  have hDU : V.left.basicOpen s₁ ≤ U₁ := V.left.basicOpen_le s₁
  let t : Γ(W'.left, ⊤) := W.topIso.inv (V.left.presheaf.map (homOfLE (hWD.trans hDU)).op s₁)
  have ht : IsUnit t := by
    have h₁ := V.left.toRingedSpace.isUnit_res_basicOpen s₁
    have h₂ := (h₁.map (V.left.presheaf.map (homOfLE hWD).op).hom).map W.topIso.inv.hom
    have key : ∀ {A B D : V.left.Opens} (f₁ : B ⟶ A) (f₂ : D ⟶ B) (f₃ : D ⟶ A)
        (b : Γ(V.left, A)), V.left.presheaf.map f₂.op (V.left.presheaf.map f₁.op b) =
          V.left.presheaf.map f₃.op b := by
      intro A B D f₁ f₂ f₃ b
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        Subsingleton.elim (f₂ ≫ f₁) f₃]
    have e : t = W.topIso.inv.hom ((V.left.presheaf.map (homOfLE hWD).op).hom
        ((V.left.presheaf.map (homOfLE hDU).op).hom s₁)) :=
      congrArg W.topIso.inv.hom (key _ _ _ s₁).symm
    rw [e]
    exact h₂
  refine ⟨W, hyW, ht.unit, ?_⟩
  refine injective_toLocalGenericRing_appTop j iU hiU W' (y := y₀) hcoh ?_
  simp only [IsUnit.unit_spec]
  let φ : W' ⟶ V := Scheme.Etale.ofOpensι V W
  -- both sides are the image of `r` in the local generic ring of `W` at `y`
  have hgerm : W'.left.presheaf.germ ⊤ y₀ trivial t = W.ι.stalkMap y₀ r.val := by
    have h₁ := congrArg (fun ψ ↦ ψ.hom t) (Scheme.Opens.germ_stalkIso_inv W ⊤ y₀ trivial)
    have h₂ : V.left.presheaf.germ (W.ι ''ᵁ ⊤) y ⟨y₀, trivial, rfl⟩ t = r.val := by
      simp only [t, Scheme.Opens.topIso_inv]
      exact (V.left.presheaf.germ_res_apply _ _ _ _).trans
        ((V.left.presheaf.germ_res_apply _ _ _ _).trans hs₁)
    refine h₁.symm.trans ?_
    change (W.stalkIso y₀).inv.hom (V.left.presheaf.germ (W.ι ''ᵁ ⊤) y _ t) = _
    rw [h₂, Scheme.Opens.stalkIso_inv]
    rfl
  have hL : Scheme.Etale.toLocalGenericRing W' y₀
      ((pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _) (by simp)
        (by simp [hiU])).appTop ((pullback.fst W'.hom j).appTop t)) =
      Scheme.Etale.stalkToLocalGenericRing W' y₀ (W.ι.stalkMap y₀ r.val) := by
    have hgen : (pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _) (by simp)
        (by simp [hiU])).appTop ((pullback.fst W'.hom j).appTop t) =
        (pullback.fst W'.hom C.fromSpecFunctionField).appTop t := by
      change ((pullback.fst W'.hom j).appTop ≫ (pullback.map W'.hom C.fromSpecFunctionField
        W'.hom j (𝟙 _) iU (𝟙 _) (by simp) (by simp [hiU])).appTop) t = _
      rw [← Scheme.Hom.comp_appTop, pullback.lift_fst, Category.comp_id]
    rw [hgen, Scheme.Etale.toLocalGenericRing_fst_appTop, hgerm]
  have hR : Scheme.Etale.toLocalGenericRing W' y₀
      ((pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _) (by simp)
        (by simp [hiU])).appTop (((MorphismProperty.Over.pullback @Etale ⊤ j).map
          (Scheme.Etale.ofOpensι V W)).left.appTop f.val)) =
      Scheme.Etale.stalkToLocalGenericRing W' y₀ (W.ι.stalkMap y₀ r.val) := by
    have e : pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _) (by simp)
        (by simp [hiU]) ≫ ((MorphismProperty.Over.pullback @Etale ⊤ j).map φ).left =
        ((MorphismProperty.Over.pullback @Etale ⊤ C.fromSpecFunctionField).map φ).left ≫
          pullback.map V.hom C.fromSpecFunctionField V.hom j (𝟙 _) iU (𝟙 _) (by simp)
            (by simp [hiU]) := by
      rw [show ((MorphismProperty.Over.pullback @Etale ⊤ j).map φ).left =
          pullback.map _ _ _ _ φ.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
        show ((MorphismProperty.Over.pullback @Etale ⊤ C.fromSpecFunctionField).map φ).left =
          pullback.map _ _ _ _ φ.left (𝟙 _) (𝟙 _) (by simp) (by simp) from rfl,
        pullback.map_comp, pullback.map_comp]
      congr 1
    have h₁ : (pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _) (by simp)
        (by simp [hiU])).appTop (((MorphismProperty.Over.pullback @Etale ⊤ j).map
          φ).left.appTop f.val) =
        ((MorphismProperty.Over.pullback @Etale ⊤ C.fromSpecFunctionField).map
          φ).left.appTop (genV f.val) := by
      exact congrArg (fun m ↦ (Scheme.Hom.appTop m).hom f.val) e
    have h₂ := congrArg (fun ψ ↦ ψ.hom (genV f.val))
      (Scheme.Etale.toLocalGenericRing_comp_localGenericRingMap φ y₀)
    have h₃ : Scheme.Etale.toLocalGenericRing V y (genV f.val) =
        Scheme.Etale.stalkToLocalGenericRing V y r.val := hr.symm
    have h₄ := congrArg (fun ψ ↦ ψ.hom r.val)
      (Scheme.Etale.stalkToLocalGenericRing_comp_localGenericRingMap φ y₀)
    rw [h₁]
    refine h₂.symm.trans ?_
    change Scheme.Etale.localGenericRingMap φ y₀
      (Scheme.Etale.toLocalGenericRing V y (genV f.val)) = _
    rw [h₃]
    exact h₄
  exact hL.trans hR.symm


omit [IsOpenImmersion j] in
open Classical in
/-- **Uniformisers at the punctures.** In the situation of
`AlgebraicGeometry.IsCurve.exists_eq_of_ord_eq_zero`, let `P ∈ S` and let `c` be an
integer-valued function on the points of `V` over `P`. Near every point of `V` there is a unit on
`V ×_C U` whose order is `c` at the points over `P` and `0` at the other points over `S`: a
power of a uniformiser of the discrete valuation ring `𝒪_{V,y}`, which near `y` vanishes only
at `y` (`AlgebraicGeometry.Scheme.exists_opens_isolate`).
(blueprint: `lemma-cohomology-multiplicative-group--6`, surjectivity) -/
lemma exists_ord_eq_extendByZero (hC : topologicalKrullDim C = 1) {S : Set C}
    (hSc : ∀ P ∈ S, IsClosed {P}) (hj : Set.range j = Sᶜ) (V : C.Etale)
    (y : V.left) {P : C} (hP : P ∈ S)
    (c : ↥(pullback V.hom (C.fromSpecResidueField P)) → ULift.{u + 1} ℤ) :
    ∃ (W : V.left.Opens) (_ : y ∈ W)
      (f : Γ(pullback (Scheme.Etale.ofOpens V W).hom j, ⊤)ˣ),
      ∀ y' : W, (if (Scheme.Etale.ofOpens V W).hom y' ∈ S then
          ULift.up (Scheme.Etale.ord (Scheme.Etale.ofOpens V W) y'
            ((pullback.map _ C.fromSpecFunctionField _ j (𝟙 _) iU (𝟙 _) (by simp)
              (by simp [hiU])).appTop f.val)) else 0) =
        Scheme.extendByZero (AddCommGrpCat.of (ULift.{u + 1} ℤ)) (C.fromSpecResidueField P) c
          (W.ι y') := by
  by_cases hy : V.hom y = P
  swap
  · let W : V.left.Opens := ⟨(V.hom ⁻¹' {P})ᶜ,
      ((hSc P hP).preimage V.hom.continuous).isOpen_compl⟩
    refine ⟨W, hy, 1, fun y' ↦ ?_⟩
    have hy' : V.hom (W.ι y') ∉ Set.range (C.fromSpecResidueField P) := by
      rw [Scheme.range_fromSpecResidueField]
      exact y'.2
    rw [Scheme.extendByZero_of_notMem _ hy']
    split_ifs
    · rw [Units.val_one, map_one, Scheme.Etale.ord_one]
      rfl
    · rfl
  have hcoh : coheight (V.hom y) = 1 := hy ▸ coheight_eq_one_of_mem hC hSc hP
  have : IsDiscreteValuationRing (V.left.presheaf.stalk y) :=
    Scheme.Etale.isDiscreteValuationRing_stalk V hcoh
  let g : V.left ⟶ C := V.hom
  have : IsLocallyNoetherian V.left := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (V.left.presheaf.stalk y)
  obtain ⟨W, hyW, t, ht, hW⟩ := Scheme.exists_opens_isolate g y (hy ▸ hSc P hP) hπ
  obtain ⟨z₀, hz₀⟩ : ∃ z, pullback.fst V.hom (C.fromSpecResidueField P) z = y :=
    (Set.ext_iff.1 (Scheme.Pullback.range_fst V.hom (C.fromSpecResidueField P)) y).2 (by
      change V.hom y ∈ Set.range (C.fromSpecResidueField P)
      rw [Scheme.range_fromSpecResidueField, hy]
      rfl)
  let W' := Scheme.Etale.ofOpens V W
  let tW : Γ(W'.left, ⊤) := W.topIso.inv t
  have hgerm (y' : W) : (W.stalkIso y').hom (W'.left.presheaf.germ ⊤ y' trivial tW) =
      V.left.presheaf.germ W y'.1 y'.2 t := by
    refine (congrArg (fun φ ↦ φ.hom tW)
      (Scheme.Opens.germ_stalkIso_hom W (V := ⊤) y' trivial)).trans ?_
    exact V.left.presheaf.germ_res_apply _ _ _ t
  have hunit_at (q : W) (hq : q.1 ≠ y) : IsUnit (W'.left.presheaf.germ ⊤ q trivial tW) := by
    have h₁ := (V.left.mem_basicOpen t q.1 q.2).1 (hW q.1 q.2 hq).2
    rw [← hgerm] at h₁
    have h₂ := h₁.map (W.stalkIso q).inv.hom
    rwa [← ConcreteCategory.comp_apply, Iso.hom_inv_id, CategoryTheory.id_apply] at h₂
  let a : Γ(pullback W'.hom j, ⊤) := (pullback.fst W'.hom j).appTop tW
  have hb : (pullback W'.hom j).basicOpen a = ⊤ := by
    rw [← Scheme.preimage_basicOpen_top]
    rw [eq_top_iff]
    intro p _
    change pullback.fst W'.hom j p ∈ W'.left.basicOpen tW
    rw [Scheme.mem_basicOpen_top]
    refine hunit_at _ fun h ↦ ?_
    have h₁ : W'.hom (pullback.fst W'.hom j p) = j (pullback.snd W'.hom j p) :=
      congrArg (fun f ↦ f p) (pullback.condition (f := W'.hom) (g := j))
    have h₂ : j (pullback.snd W'.hom j p) ∈ Sᶜ := hj ▸ Set.mem_range_self _
    apply h₂
    rw [← h₁]
    change V.hom (pullback.fst W'.hom j p).1 ∈ S
    rw [h, hy]
    exact hP
  have ha : IsUnit a := by
    let X := pullback W'.hom j
    have key : ∀ {B : X.Opens} (f₁ : (⊤ : X.Opens) ⟶ B) (f₂ : B ⟶ ⊤) (b : Γ(X, ⊤)),
        X.presheaf.map f₁.op (X.presheaf.map f₂.op b) = b := by
      intro B f₁ f₂ b
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
        Subsingleton.elim (f₁ ≫ f₂) (𝟙 _), op_id, CategoryTheory.Functor.map_id,
        CategoryTheory.id_apply]
    have h₁ := X.toRingedSpace.isUnit_res_basicOpen a
    have h₂ := h₁.map (X.presheaf.map (homOfLE (by rw [hb]) :
      (⊤ : X.Opens) ⟶ X.basicOpen a).op).hom
    convert h₂ using 1
    exact (key _ _ a).symm
  -- the order of `t` at the points of `W`
  have hord (y' : W) : Scheme.Etale.ord W' y'
      ((pullback.fst W'.hom C.fromSpecFunctionField).appTop tW) = if y'.1 = y then 1 else 0 := by
    obtain ⟨y', hy'W⟩ := y'
    by_cases hy'c : coheight (W'.hom ⟨y', hy'W⟩) = 1
    · rw [Scheme.Etale.ord, ite_eq_left hy'c, Scheme.Etale.toLocalGenericRing_fst_appTop]
      have := Scheme.Etale.isDiscreteValuationRing_stalk W' hy'c
      let := (Scheme.Etale.stalkToLocalGenericRing W' ⟨y', hy'W⟩).hom.toAlgebra
      have := Scheme.Etale.isFractionRing_localGenericRing W' ⟨y', hy'W⟩
      split_ifs with hy'
      · change y' = y at hy'
        subst hy'
        refine Ring.ordOf_algebraMap_of_irreducible ?_
        have h₁ : (W.stalkIso ⟨y', hy'W⟩).hom
            (W'.left.presheaf.germ ⊤ ⟨y', hy'W⟩ trivial tW) = π := by
          rw [hgerm]
          exact ht
        have h₂ : Irreducible ((W.stalkIso ⟨y', hy'W⟩).commRingCatIsoToRingEquiv
            (W'.left.presheaf.germ ⊤ ⟨y', hy'W⟩ trivial tW)) := h₁ ▸ hπ
        exact (MulEquiv.irreducible_iff
          (W.stalkIso ⟨y', hy'W⟩).commRingCatIsoToRingEquiv.toMulEquiv).1 h₂
      · exact Ring.ordOf_algebraMap_of_isUnit (hunit_at ⟨y', hy'W⟩ hy')
    · have hy' : y' ≠ y := fun h ↦ hy'c (by
        change coheight (V.hom y') = 1
        rw [h, hcoh])
      rw [Scheme.Etale.ord_of_coheight_ne_one W' hy'c, ite_eq_right hy']
  refine ⟨W, hyW, ha.unit ^ (c z₀).down, fun y' ↦ ?_⟩
  have hgen : (pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _) (by simp)
      (by simp [hiU])).appTop a = (pullback.fst W'.hom C.fromSpecFunctionField).appTop tW := by
    change ((pullback.fst W'.hom j).appTop ≫ (pullback.map W'.hom C.fromSpecFunctionField
      W'.hom j (𝟙 _) iU (𝟙 _) (by simp) (by simp [hiU])).appTop) tW = _
    rw [← Scheme.Hom.comp_appTop, pullback.lift_fst, Category.comp_id]
  have hpow : (pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _) (by simp)
      (by simp [hiU])).appTop ↑(ha.unit ^ (c z₀).down) =
      ↑((Units.map (pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _)
        (by simp) (by simp [hiU])).appTop.hom.toMonoidHom ha.unit) ^ (c z₀).down) := by
    rw [← map_zpow, Units.coe_map]
    rfl
  rw [hpow, Scheme.Etale.ord_zpow]
  change (if W'.hom y' ∈ S then ULift.up ((c z₀).down * Scheme.Etale.ord W' y'
    ((pullback.map W'.hom C.fromSpecFunctionField W'.hom j (𝟙 _) iU (𝟙 _) (by simp)
      (by simp [hiU])).appTop a)) else 0) = _
  rw [hgen, hord]
  by_cases hy' : y'.1 = y
  · have hS' : W'.hom y' ∈ S := by
      change V.hom y'.1 ∈ S
      rw [hy', hy]
      exact hP
    rw [ite_eq_left hS', ite_eq_left hy', mul_one]
    change _ = Scheme.extendByZero (AddCommGrpCat.of (ULift.{u + 1} ℤ))
      (C.fromSpecResidueField P) c y'.1
    rw [hy', ← hz₀, Scheme.extendByZero_fst]
  · rw [ite_eq_right hy', mul_zero]
    have hne : V.hom (W.ι y') ∉ Set.range (C.fromSpecResidueField P) := by
      rw [Scheme.range_fromSpecResidueField, Set.mem_singleton_iff, ← hy]
      exact (hW y'.1 y'.2 hy').1
    rw [Scheme.extendByZero_of_notMem _ hne]
    split_ifs <;> rfl


end IsCurve

namespace IsCurve

variable {k : Type u} [Field k] {C : Scheme.{u}}

/-- **The divisor sequence of a punctured curve.** Let `C` be a smooth proper connected curve
over an algebraically closed field `k`, let `S` be a finite set of closed points of `C`, and
let `j : U ⟶ C` be an open immersion with image the complement of `S`. Then there is a map
`d` making

```
  0 ──▶ 𝔾ₘ ──▶ j_* 𝔾ₘ ──d──▶ ⨁_{P ∈ S} i_{P*} ℤ ──▶ 0
```

a short exact sequence of étale sheaves on `C`, where the first map is restriction of units
along `j` and the third term is the vertex of any colimit cocone `c` on the family
`P ↦ i_{P*} ℤ` of `AlgebraicGeometry.Scheme.pointConstantInt`. A connected curve has
dimension exactly one, which is the hypothesis `hC`; without it `S` could be all of
`C = Spec k`, where `j_* 𝔾ₘ = 0` but `𝔾ₘ ≠ 0`.

The curve is regular (`AlgebraicGeometry.IsRegular.of_smooth`), hence integral. The first map
is a monomorphism since its composite with the restriction to the generic point is
(`AlgebraicGeometry.Scheme.mono_gmSheafToLowerStarGmSheaf_fromSpecFunctionField`). For the
cokernel, `j_* 𝔾ₘ` maps to the sheaf `V ↦ (V → ℤ)` of functions on points by the orders of
vanishing at the points over `S`, and `⨁_{P ∈ S} i_{P*} ℤ` maps to it by extension by zero;
on geometric stalks the second map is injective, the two images agree by
`AlgebraicGeometry.IsCurve.exists_ord_eq_extendByZero`, and the kernel of the first is the
image of `𝔾ₘ` by `AlgebraicGeometry.IsCurve.exists_eq_of_ord_eq_zero`.
(blueprint: `lemma-cohomology-multiplicative-group--6`) -/
theorem exists_shortExact_divisorSequence [IsAlgClosed k] (f : C ⟶ Spec (.of k)) [IsCurve f]
    [Smooth f] [IsProper f] [ConnectedSpace C] (hC : topologicalKrullDim C = 1) (S : Set C)
    (hS : S.Finite) (hSc : ∀ P ∈ S, IsClosed {P}) {U : Scheme.{u}} (j : U ⟶ C)
    [IsOpenImmersion j] (hj : Set.range j = Sᶜ)
    (c : Cofan fun P : S ↦ C.pointConstantInt P.1) (hc : IsColimit c) :
    ∃ (d : (Etale.lowerStar AddCommGrpCat.{u + 1} j).obj U.gmSheaf ⟶ c.pt)
      (w : Scheme.gmSheafToLowerStarGmSheaf j ≫ d = 0),
      (ShortComplex.mk (Scheme.gmSheafToLowerStarGmSheaf j) d w).ShortExact := by
  classical
  have : IsRegular C := IsRegular.of_smooth f
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : IrreducibleSpace C := IsRegular.irreducibleSpace C
  have : IsReduced C := isReduced_of_isReduced_stalk C
  have : IsIntegral C := isIntegral_of_irreducibleSpace_of_isReduced C
  -- the generic point lies in `U`
  have hη : genericPoint C ∉ S := by
    intro hη
    have h₁ : (Set.univ : Set C) = {genericPoint C} := by
      rw [← genericPoint_spec C, (hSc _ hη).closure_eq]
    have : Subsingleton C := ⟨fun a b ↦ by
      have ha : a ∈ ({genericPoint C} : Set C) := h₁ ▸ Set.mem_univ a
      have hb : b ∈ ({genericPoint C} : Set C) := h₁ ▸ Set.mem_univ b
      rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]⟩
    have h₂ := topologicalKrullDim_zero_of_discreteTopology C
    rw [hC] at h₂
    exact absurd h₂ (by decide)
  have hrange : Set.range C.fromSpecFunctionField ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    have hz : C.fromSpecFunctionField z ⤳ genericPoint C := by
      have := Set.mem_range_self (f := C.fromSpecStalk (genericPoint C)) z
      rwa [Scheme.range_fromSpecStalk] at this
    exact hz.mem_open j.isOpenEmbedding.isOpen_range (by rw [hj]; exact hη)
  let iU : Spec C.functionField ⟶ U := IsOpenImmersion.lift j C.fromSpecFunctionField hrange
  have hiU : iU ≫ j = C.fromSpecFunctionField := IsOpenImmersion.lift_fac _ _ _
  let M := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let dS : (Etale.lowerStar AddCommGrpCat.{u + 1} j).obj U.gmSheaf ⟶ C.pointFunctionSheaf M :=
    Scheme.lowerStarGmSheafMap j iU _ hiU ≫ C.divisorMap ≫ Scheme.pointFunctionSheafIndicator M S
  let ψ := Cofan.IsColimit.desc hc fun P ↦ C.pointConstantIntToPointFunctionSheaf P.1
  have hmono : Mono (Scheme.gmSheafToLowerStarGmSheaf j) := by
    have := C.mono_gmSheafToLowerStarGmSheaf_fromSpecFunctionField
    rw [← Scheme.gmSheafToLowerStarGmSheaf_comp_lowerStarGmSheafMap j iU _ hiU] at this
    exact mono_of_mono _ (Scheme.lowerStarGmSheafMap j iU _ hiU)
  have w : Scheme.gmSheafToLowerStarGmSheaf j ≫ dS = 0 := by
    simp only [dS, Scheme.gmSheafToLowerStarGmSheaf_comp_lowerStarGmSheafMap_assoc]
    rw [reassoc_of% C.gmSheafToLowerStarGmSheaf_comp_divisorMap, zero_comp]
  have h₁ := C.exists_sheafFiber_eq_of_sheafFiber_map_eq_zero
    (Scheme.gmSheafToLowerStarGmSheaf j) dS (fun V y b hb ↦ by
    obtain ⟨W, hyW, u, hu⟩ := exists_eq_of_ord_eq_zero j iU hiU hC hS hSc hj V y
      (Additive.toMul b.down) (fun y' hy' ↦ by
        have h₀ : (if V.hom y' ∈ S then ULift.up (Scheme.Etale.ord V y'
            ((pullback.map V.hom C.fromSpecFunctionField V.hom j (𝟙 _) iU (𝟙 _) (by simp)
              (by simp [hiU])).appTop (Additive.toMul b.down).val)) else 0) = 0 :=
          congrFun hb y'
        rw [ite_eq_left hy'] at h₀
        exact congrArg ULift.down h₀)
    exact ⟨W, hyW, ULift.up (Additive.ofMul u),
      ULift.ext (congrArg Additive.ofMul (Units.ext hu))⟩)
  have h₄ (x : C) := C.exists_sheafFiber_eq_desc dS c hc x fun P a ↦
    C.exists_sheafFiber_eq_pointConstantIntToPointFunctionSheaf dS P.1 (fun V y cf ↦ by
      obtain ⟨W, hyW, g, hg⟩ := exists_ord_eq_extendByZero j iU hiU hC hSc hj V y P.2 cf
      exact ⟨W, hyW, ULift.up (Additive.ofMul g), funext hg⟩) x a
  have h₃ (x : C) (b) : ∃ p, (C.uliftPointSmallEtale x).sheafFiber.map ψ p =
      (C.uliftPointSmallEtale x).sheafFiber.map dS b := by
    have : Fintype S := hS.fintype
    let Φ := C.uliftPointSmallEtale x
    let F := Φ.sheafFiber (A := AddCommGrpCat.{u + 1})
    obtain ⟨V, v, b₀, rfl⟩ := Φ.toPresheafFiber_jointly_surjective
      (P := ((Etale.lowerStar AddCommGrpCat.{u + 1} j).obj U.gmSheaf).obj) b
    let D : V.left → M := (Scheme.lowerStarGmSheafMap j iU _ hiU ≫ C.divisorMap).hom.app
      (op V) b₀
    have hD : dS.hom.app (op V) b₀ = ∑ P : S, Scheme.extendByZero M (C.fromSpecResidueField P.1)
        (fun z ↦ D (pullback.fst V.hom (C.fromSpecResidueField P.1) z)) := by
      funext y'
      rw [Finset.sum_apply]
      simp only [Scheme.extendByZero_fromSpecResidueField_fst]
      change (if V.hom y' ∈ S then D y' else 0) = _
      by_cases hy' : V.hom y' ∈ S
      · rw [ite_eq_left hy', Finset.sum_eq_single_of_mem (⟨_, hy'⟩ : S) (Finset.mem_univ _),
          ite_eq_left rfl]
        intro P _ hP
        rw [ite_eq_right fun e ↦ hP (Subtype.ext e.symm)]
      · rw [ite_eq_right hy']
        exact (Finset.sum_eq_zero fun P _ ↦
          ite_eq_right fun (e : V.hom y' = P.1) ↦ hy' (e ▸ P.2)).symm
    refine ⟨∑ P : S, F.map (c.inj P) (Φ.toPresheafFiber V v (C.pointConstantInt P.1).obj
      ((C.pointFunctionSheafToPointConstantInt P.1).hom.app (op V) D)), ?_⟩
    have hterm (P : S) : F.map ψ (F.map (c.inj P) (Φ.toPresheafFiber V v
        (C.pointConstantInt P.1).obj
          ((C.pointFunctionSheafToPointConstantInt P.1).hom.app (op V) D))) =
        Φ.toPresheafFiber V v (C.pointFunctionSheaf M).obj
          (Scheme.extendByZero M (C.fromSpecResidueField P.1)
            (fun z ↦ D (pullback.fst V.hom (C.fromSpecResidueField P.1) z))) := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp, Cofan.IsColimit.fac]
      change Φ.presheafFiber.map (C.pointConstantIntToPointFunctionSheaf P.1).hom _ = _
      have e : (C.pointConstantIntToPointFunctionSheaf P.1).hom.app (op V)
          ((C.pointFunctionSheafToPointConstantInt P.1).hom.app (op V) D) =
          Scheme.extendByZero M (C.fromSpecResidueField P.1)
            (fun z ↦ D (pullback.fst V.hom (C.fromSpecResidueField P.1) z)) :=
        congrArg (fun φ ↦ (φ.hom.app (op V)).hom D)
          (Scheme.pointFunctionSheafToPointConstantInt_comp C P.1)
      rw [Φ.toPresheafFiber_naturality_apply, e]
    calc _ = ∑ P : S, Φ.toPresheafFiber V v (C.pointFunctionSheaf M).obj
          (Scheme.extendByZero M (C.fromSpecResidueField P.1)
            (fun z ↦ D (pullback.fst V.hom (C.fromSpecResidueField P.1) z))) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun P _ ↦ hterm P
      _ = Φ.toPresheafFiber V v (C.pointFunctionSheaf M).obj (dS.hom.app (op V) b₀) := by
          rw [← map_sum, ← hD]
      _ = _ := by
          change _ = Φ.presheafFiber.map dS.hom _
          rw [Φ.toPresheafFiber_naturality_apply]
  obtain ⟨e⟩ := Scheme.nonempty_cokernel_iso_of_sheafFiber (Scheme.gmSheafToLowerStarGmSheaf j)
    dS ψ w h₁ (C.injective_sheafFiber_map_desc_pointConstantIntToPointFunctionSheaf
      Subtype.val_injective c hc) h₃ h₄
  refine ⟨cokernel.π _ ≫ e.hom, by simp, { mono_f := hmono, epi_g := epi_comp _ _, exact := ?_ }⟩
  exact ShortComplex.exact_of_g_is_cokernel _
    (IsColimit.ofIsoColimit (cokernelIsCokernel _) (Cofork.ext e (by simp)))

end IsCurve

end AlgebraicGeometry
