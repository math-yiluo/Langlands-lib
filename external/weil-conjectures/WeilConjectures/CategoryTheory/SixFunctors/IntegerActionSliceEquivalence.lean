/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Shift.ShiftedHom
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Slices of the integer action site

Source: Stacks Project, Sites, Tags 00VH, 00XZ and 00Y0; the agent-formulated twisted
variant of Tag 00W0 and its explicit normalization proof
(blueprint: lem-sf-integer-action-slice-equivalence).

`HasShift C ℤ` is Mathlib's coherent integer action, with no additive structure on `C`.
It includes the chosen inverse and all power comparisons. All construction data below
are explicit; only category laws and the slice-equivalence assertion are postponed.
-/

@[expose] public section

universe u v w r

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The objects of the integer action category are precisely the objects of `C`.
Source: the twisted action construction preceding the slice normalization, Stacks Sites
00W0 motivation (blueprint: lem-sf-integer-action-slice-equivalence). -/
structure IntegerActionSite (C : Type u) where
  /-- The underlying object, without additional data. -/
  obj : C

variable {C : Type u} [Category.{v} C] [HasShift C ℤ]

/-- Arrows are pairs `(n,f : U ⟶ V⟦n⟧)`; composition uses the coherent power comparison.
Source: category calculation, step 1 of the agent slice-normalization proof
(blueprint: lem-sf-integer-action-slice-equivalence). -/
noncomputable instance integerActionCategoryStruct : CategoryStruct (IntegerActionSite C) where
  Hom X Y := Σ n : ℤ, ShiftedHom X.obj Y.obj n
  id X := ⟨0, ShiftedHom.mk₀ 0 rfl (𝟙 X.obj)⟩
  comp f g := ⟨f.1 + g.1, f.2.comp g.2 (Int.add_comm g.1 f.1)⟩

private theorem integerActionComp_heq {X Y Z : C} {a b c d : ℤ}
    (f : ShiftedHom X Y a) (g : ShiftedHom Y Z b) (hc : b + a = c)
    (hd : b + a = d) : HEq (f.comp g hc) (f.comp g hd) := by
  cases hc
  cases hd
  rfl

/-- The displayed identity and composition obey the category laws.
Source: step 1 of the agent slice-normalization proof, motivated by Stacks Sites 00W0
(blueprint: lem-sf-integer-action-slice-equivalence).
Proof: the zero-power comparisons give both unit laws. Both parenthesizations of three
arrows have degree `n+m+l` and map `s^(n+m)(a) ∘ s^n(h) ∘ f`; the coherence law for the
power comparisons identifies their final comparison maps. Sigma extensionality gives
associativity. These are exactly `ShiftedHom`'s unit and associativity identities. -/
theorem integerActionCategoryLaws :
    (∀ (X Y : IntegerActionSite C) (f : X ⟶ Y), 𝟙 X ≫ f = f) ∧
    (∀ (X Y : IntegerActionSite C) (f : X ⟶ Y), f ≫ 𝟙 Y = f) ∧
    (∀ (X Y Z T : IntegerActionSite C) (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
      (f ≫ g) ≫ h = f ≫ (g ≫ h)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y f
    rcases f with ⟨n, f⟩
    change Sigma.mk (0 + n) _ = Sigma.mk n f
    apply Sigma.ext (Int.zero_add n)
    exact (integerActionComp_heq _ _ _ _).trans
      (ShiftedHom.mk₀_id_comp 0 rfl f).heq
  · intro X Y f
    rcases f with ⟨n, f⟩
    change Sigma.mk (n + 0) _ = Sigma.mk n f
    apply Sigma.ext (Int.add_zero n)
    exact (integerActionComp_heq _ _ _ _).trans
      (ShiftedHom.comp_mk₀_id f 0 rfl).heq
  · intro X Y Z T f g h
    rcases f with ⟨n, f⟩
    rcases g with ⟨m, g⟩
    rcases h with ⟨l, h⟩
    change Sigma.mk ((n + m) + l) _ = Sigma.mk (n + (m + l)) _
    apply Sigma.ext (Int.add_assoc n m l)
    have e := ShiftedHom.comp_assoc f g h (Int.add_comm m n)
      (Int.add_comm l m) (show l + m + n = n + (m + l) by omega)
    exact (integerActionComp_heq _ _ _ _).trans e.heq

/-- The integer action category, using the explicit pair composition.
Source: step 1 of the slice normalization (blueprint: lem-sf-integer-action-slice-equivalence).
Its data are the displayed `CategoryStruct`; only the named category-law theorem is used. -/
noncomputable instance integerActionCategory : Category (IntegerActionSite C) where
  toCategoryStruct := integerActionCategoryStruct
  id_comp := (integerActionCategoryLaws (C := C)).1 _ _
  comp_id := (integerActionCategoryLaws (C := C)).2.1 _ _
  assoc := (integerActionCategoryLaws (C := C)).2.2 _ _ _ _

/-- The zero-degree inclusion respects identities and composition.
Source: steps 1 and 7 of the agent normalization proof, Stacks Sites 00XZ terminology
(blueprint: lem-sf-integer-action-slice-equivalence).
Proof: the zero-power unit comparison identifies the identity with `(0,1)`.
The zero/zero power comparison gives `(0,g) ∘ (0,f) = (0,g ∘ f)`, by the two unit
coherence identities, equivalently `ShiftedHom.mk₀_comp_mk₀`. -/
theorem integerActionInclusionLaws :
    (∀ X : C, (⟨0, ShiftedHom.mk₀ 0 rfl (𝟙 X)⟩ :
      (IntegerActionSite.mk X : IntegerActionSite C) ⟶ IntegerActionSite.mk X) =
        𝟙 (IntegerActionSite.mk X)) ∧
    (∀ (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z),
      (⟨0, ShiftedHom.mk₀ 0 rfl (f ≫ g)⟩ :
        (IntegerActionSite.mk X : IntegerActionSite C) ⟶ IntegerActionSite.mk Z) =
      @CategoryStruct.comp (IntegerActionSite C) integerActionCategoryStruct
        (IntegerActionSite.mk X) (IntegerActionSite.mk Y) (IntegerActionSite.mk Z)
        ⟨0, ShiftedHom.mk₀ 0 rfl f⟩ ⟨0, ShiftedHom.mk₀ 0 rfl g⟩) := by
  refine ⟨fun X ↦ rfl, ?_⟩
  intro X Y Z f g
  change Sigma.mk 0 _ = Sigma.mk (0 + 0) _
  apply congrArg (Sigma.mk (0 : ℤ))
  exact (ShiftedHom.mk₀_comp_mk₀ f g (Int.add_comm 0 0) rfl rfl).symm

/-- The ordinary degree-zero inclusion, with no change of object data.
Source: step 7 of the slice normalization, Stacks Sites 00XZ terminology
(blueprint: lem-sf-integer-action-slice-equivalence). -/
noncomputable def integerActionInclusion : C ⥤ IntegerActionSite C where
  obj X := ⟨X⟩
  map f := ⟨0, ShiftedHom.mk₀ 0 rfl f⟩
  map_id := (integerActionInclusionLaws (C := C)).1
  map_comp := (integerActionInclusionLaws (C := C)).2 _ _ _

/-- The action-site topology is generated by the images of degree-zero covering presieves.
Source: steps 3--5 of the normalization proof, Stacks Sites 00VH and 00ZC
(blueprint: lem-sf-integer-action-slice-equivalence).
This is an actual infimum of topologies containing precisely the prescribed generators. -/
noncomputable def integerActionTopology (J : Precoverage C) :
    GrothendieckTopology (IntegerActionSite C) :=
  sInf {K | ∀ (X : C) (R : Presieve X), R ∈ J X →
    Sieve.generate (R.map (integerActionInclusion (C := C))) ∈ K (IntegerActionSite.mk X)}

/-- The degree-zero functor on slices is postcomposition with the ordinary inclusion.
Source: step 7 of the slice normalization, Stacks Sites 00XZ
(blueprint: lem-sf-integer-action-slice-equivalence). -/
noncomputable def integerActionSliceInclusion (V : C) :
    Over V ⥤ Over (IntegerActionSite.mk V : IntegerActionSite C) :=
  Over.post (integerActionInclusion (C := C))

/-- Normalize an action-site slice object by applying the inverse integer power.
Source: step 6 of the slice normalization, Stacks Sites 00XZ
(blueprint: lem-sf-integer-action-slice-equivalence). -/
noncomputable def integerActionSliceNormalize {V : C}
    (X : Over (IntegerActionSite.mk V : IntegerActionSite C)) : Over V :=
  Over.mk ((shiftFunctor C (-X.hom.1)).map X.hom.2 ≫
    (shiftFunctorCompIsoId C X.hom.1 (-X.hom.1) (add_neg_cancel X.hom.1)).hom.app V)

private noncomputable def integerActionPowerIso (X : C) (n : ℤ) :
    IntegerActionSite.mk (X⟦n⟧) ≅ IntegerActionSite.mk X where
  hom := ⟨n, 𝟙 _⟩
  inv := ⟨-n, (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).inv.app X⟩
  hom_inv_id := by
    apply Sigma.ext (add_neg_cancel n)
    refine (integerActionComp_heq _ _ _ (neg_add_cancel n)).trans ?_
    apply heq_of_eq
    change _ = ShiftedHom.mk₀ 0 rfl (𝟙 _)
    simp only [ShiftedHom.comp, Category.id_comp]
    rw [shift_shiftFunctorCompIsoId_add_neg_cancel_inv_app]
    simp [shiftFunctorCompIsoId, ShiftedHom.mk₀, shiftFunctorZero']
  inv_hom_id := by
    apply Sigma.ext (neg_add_cancel n)
    refine (integerActionComp_heq _ _ _ (add_neg_cancel n)).trans ?_
    apply heq_of_eq
    change _ = ShiftedHom.mk₀ 0 rfl (𝟙 _)
    simp [ShiftedHom.comp, shiftFunctorCompIsoId, ShiftedHom.mk₀, shiftFunctorZero']

private theorem integerActionInclusion_faithful :
    (integerActionInclusion (C := C)).Faithful where
  map_injective := by
    intro X Y f g h
    have e := Sigma.mk.inj h
    exact (ShiftedHom.homEquiv 0 rfl).injective (eq_of_heq e.2)

private theorem integerActionInclusion_zero {X Y : C}
    (f : (IntegerActionSite.mk X : IntegerActionSite C) ⟶ IntegerActionSite.mk Y)
    (hn : f.1 = 0) :
    (integerActionInclusion (C := C)).map
      ((ShiftedHom.homEquiv 0 rfl).symm (hn ▸ f.2)) = f := by
  rcases f with ⟨n, f⟩
  dsimp at hn
  subst n
  change Sigma.mk 0 ((ShiftedHom.homEquiv 0 rfl)
    ((ShiftedHom.homEquiv 0 rfl).symm f)) = Sigma.mk 0 f
  rw [Equiv.apply_symm_apply]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def integerActionSliceCounitObj {V : C}
    (X : Over (IntegerActionSite.mk V : IntegerActionSite C)) :
    (integerActionSliceInclusion V).obj (integerActionSliceNormalize X) ≅ X :=
  Over.isoMk (integerActionPowerIso X.left.obj (-X.hom.1)) (by
    change Sigma.mk (-X.hom.1 + X.hom.1) _ = Sigma.mk 0 _
    apply Sigma.ext (neg_add_cancel X.hom.1)
    refine (integerActionComp_heq _ _ _ (add_neg_cancel X.hom.1)).trans ?_
    apply heq_of_eq
    simp [ShiftedHom.comp, ShiftedHom.mk₀, shiftFunctorZero', integerActionSliceNormalize,
      integerActionPowerIso, shiftFunctorCompIsoId, integerActionInclusion,
      integerActionSliceInclusion])

private theorem integerActionPower_naturality {X Y : C} (f : X ⟶ Y) (n : ℤ) :
    (integerActionPowerIso X n).hom ≫ (integerActionInclusion (C := C)).map f =
      (integerActionInclusion (C := C)).map ((shiftFunctor C n).map f) ≫
        (integerActionPowerIso Y n).hom := by
  change Sigma.mk (n + 0) _ = Sigma.mk (0 + n) _
  trans Sigma.mk n ((shiftFunctor C n).map f)
  · apply Sigma.ext (add_zero n)
    refine (integerActionComp_heq _ _ _ (zero_add n)).trans ?_
    simpa only [integerActionPowerIso, integerActionInclusion, Category.id_comp] using
      (ShiftedHom.comp_mk₀ (𝟙 (X⟦n⟧)) 0 rfl f).heq
  · symm
    apply Sigma.ext (zero_add n)
    refine (integerActionComp_heq _ _ _ (add_zero n)).trans ?_
    simpa only [integerActionPowerIso, integerActionInclusion, Category.comp_id] using
      (ShiftedHom.mk₀_comp 0 rfl ((shiftFunctor C n).map f) (𝟙 (Y⟦n⟧))).heq

private theorem integerActionPower_pullback (X : C) (n : ℤ)
    (S : Sieve (IntegerActionSite.mk X : IntegerActionSite C)) :
    ((S.pullback (integerActionPowerIso X n).hom).functorPullback
      (integerActionInclusion (C := C))).functorPullback (shiftFunctor C n) =
        S.functorPullback (integerActionInclusion (C := C)) := by
  ext Y f
  change S ((integerActionInclusion (C := C)).map ((shiftFunctor C n).map f) ≫
    (integerActionPowerIso X n).hom) ↔ S ((integerActionInclusion (C := C)).map f)
  rw [← integerActionPower_naturality, Sieve.comp_mem_iff]

private theorem integerActionShiftContinuous (J : Precoverage C)
    (hcover : ∀ (n : ℤ) (X : C) (R : Presieve X),
      R ∈ J X ↔ R.map (shiftFunctor C n) ∈ J ((shiftFunctor C n).obj X)) (n : ℤ) :
    (shiftFunctor C n).IsContinuous J.toGrothendieck J.toGrothendieck := by
  rw [← Functor.le_inducedTopology_iff]
  nth_rw 1 [J.toGrothendieck_eq_sInf]
  apply sInf_le
  intro X R hR
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    ← Sieve.generate_map_eq_functorPushforward]
  exact Precoverage.generate_mem_toGrothendieck ((hcover n X R).mp hR)

private theorem integerActionInclusion_push_pull (X : C)
    (S : Sieve (IntegerActionSite.mk X : IntegerActionSite C)) :
    (S.functorPullback (integerActionInclusion (C := C))).functorPushforward
      (integerActionInclusion (C := C)) = S := by
  apply le_antisymm
  · exact Sieve.functorPullback_pushforward_le _ _
  · intro Y f hf
    let T : Over (IntegerActionSite.mk X : IntegerActionSite C) := Over.mk f
    let Q := integerActionSliceNormalize T
    let e := integerActionSliceCounitObj T
    have hw : e.hom.left ≫ f = (integerActionInclusion (C := C)).map Q.hom := Over.w e.hom
    refine ⟨Q.left, Q.hom, e.inv.left, ?_, ?_⟩
    · change S ((integerActionInclusion (C := C)).map Q.hom)
      rw [← hw]
      exact S.downward_closed hf _
    · rw [← hw, ← Category.assoc]
      have hi : e.inv.left ≫ e.hom.left = 𝟙 _ := by
        exact Over.inv_left_hom_left e
      rw [hi]
      change f = 𝟙 Y ≫ f
      exact (Category.id_comp f).symm

private theorem integerActionInclusion_pull_push (X : C) (S : Sieve X) :
    (S.functorPushforward (integerActionInclusion (C := C))).functorPullback
      (integerActionInclusion (C := C)) = S := by
  apply le_antisymm
  · intro Y f hf
    obtain ⟨Z, g, h, hg, hh⟩ := hf
    have hn := congrArg Sigma.fst hh
    change 0 = h.1 + 0 at hn
    have hn' : h.1 = 0 := by omega
    let a : Y ⟶ Z := (ShiftedHom.homEquiv 0 rfl).symm (hn' ▸ h.2)
    have ha : (integerActionInclusion (C := C)).map a = h :=
      integerActionInclusion_zero h hn'
    have hcomp : a ≫ g = f := by
      let := integerActionInclusion_faithful (C := C)
      apply (integerActionInclusion (C := C)).map_injective
      simpa [ha] using hh.symm
    rw [← hcomp]
    exact S.downward_closed hg a
  · exact Sieve.le_functorPushforward_pullback _ _

private noncomputable def integerActionTransportTopology (J : GrothendieckTopology C)
    (hs : ∀ n : ℤ, (shiftFunctor C n).IsContinuous J J) :
    GrothendieckTopology (IntegerActionSite C) where
  sieves X := {S | S.functorPullback (integerActionInclusion (C := C)) ∈ J X.obj}
  top_mem' X := by
    change (⊤ : Sieve X).functorPullback (integerActionInclusion (C := C)) ∈ J X.obj
    rw [Sieve.functorPullback_top]
    exact J.top_mem X.obj
  pullback_stable' {X Y S} f hS := by
    let P := (S.pullback (integerActionPowerIso X.obj f.1).hom).functorPullback
      (integerActionInclusion (C := C))
    have hP : P ∈ J (X.obj⟦f.1⟧) := by
      have := hs f.1
      rw [← (Sieve.essSurjFullFunctorGaloisInsertion (shiftFunctor C f.1) X.obj).l_u_eq P,
        integerActionPower_pullback]
      exact (CoverPreserving.of_isContinuous (shiftFunctor C f.1) J J).cover_preserve hS
    have hf : f = (integerActionInclusion (C := C)).map f.2 ≫
        (integerActionPowerIso X.obj f.1).hom := by
      change Sigma.mk f.1 f.2 = Sigma.mk (0 + f.1) _
      apply Sigma.ext (zero_add f.1).symm
      exact HEq.symm (by
        refine (integerActionComp_heq _ _ _ (add_zero f.1)).trans ?_
        simpa only [integerActionPowerIso, integerActionInclusion, Category.comp_id] using
          (ShiftedHom.mk₀_comp 0 rfl f.2 (𝟙 (X.obj⟦f.1⟧))).heq)
    change (S.pullback f).functorPullback (integerActionInclusion (C := C)) ∈ J Y.obj
    rw [hf, Sieve.pullback_comp, Sieve.functorPullback_pullback]
    exact J.pullback_stable f.2 hP
  transitive' {X S} hS R hR := by
    apply J.transitive hS (R.functorPullback (integerActionInclusion (C := C)))
    intro Y f hf
    have h := hR hf
    change (R.pullback ((integerActionInclusion (C := C)).map f)).functorPullback
      (integerActionInclusion (C := C)) ∈ J Y at h
    rwa [Sieve.functorPullback_pullback] at h

private theorem integerActionInclusion_push_pullback {X Y : C} (f : Y ⟶ X)
    (S : Sieve X) :
    (S.functorPushforward (integerActionInclusion (C := C))).pullback
      ((integerActionInclusion (C := C)).map f) =
        (S.pullback f).functorPushforward (integerActionInclusion (C := C)) := by
  rw [← integerActionInclusion_push_pull Y
    ((S.functorPushforward (integerActionInclusion (C := C))).pullback
      ((integerActionInclusion (C := C)).map f)),
    Sieve.functorPullback_pullback, integerActionInclusion_pull_push]

private noncomputable def integerActionRestrictTopology
    (K : GrothendieckTopology (IntegerActionSite C)) : GrothendieckTopology C where
  sieves X := {S | S.functorPushforward (integerActionInclusion (C := C)) ∈
    K (IntegerActionSite.mk X)}
  top_mem' X := by
    change (⊤ : Sieve X).functorPushforward (integerActionInclusion (C := C)) ∈
      K (IntegerActionSite.mk X)
    have he := integerActionInclusion_push_pull X
      (⊤ : Sieve (IntegerActionSite.mk X : IntegerActionSite C))
    rw [Sieve.functorPullback_top] at he
    rw [he]
    exact K.top_mem _
  pullback_stable' {X Y S} f hS := by
    rw [Set.mem_ofPred_eq, ← integerActionInclusion_push_pullback]
    exact K.pullback_stable ((integerActionInclusion (C := C)).map f) hS
  transitive' {X S} hS R hR := by
    apply K.transitive hS (R.functorPushforward (integerActionInclusion (C := C)))
    rintro Y _ ⟨Z, g, h, hg, rfl⟩
    rw [Sieve.pullback_comp, integerActionInclusion_push_pullback]
    exact K.pullback_stable h (hR hg)

private theorem integerActionTopology_mem (J : Precoverage C)
    (hcover : ∀ (n : ℤ) (X : C) (R : Presieve X),
      R ∈ J X ↔ R.map (shiftFunctor C n) ∈ J ((shiftFunctor C n).obj X))
    (X : C) (S : Sieve (IntegerActionSite.mk X : IntegerActionSite C)) :
    S ∈ integerActionTopology J (IntegerActionSite.mk X) ↔
      S.functorPullback (integerActionInclusion (C := C)) ∈ J.toGrothendieck X := by
  let K := integerActionTransportTopology J.toGrothendieck
    (integerActionShiftContinuous J hcover)
  have hle : integerActionTopology J ≤ K := by
    apply sInf_le
    intro Y R hR
    change (Sieve.generate (R.map (integerActionInclusion (C := C)))).functorPullback
      (integerActionInclusion (C := C)) ∈ J.toGrothendieck Y
    rw [Sieve.generate_map_eq_functorPushforward, integerActionInclusion_pull_push]
    exact Precoverage.generate_mem_toGrothendieck hR
  have hle' : J.toGrothendieck ≤ integerActionRestrictTopology (integerActionTopology J) := by
    rw [J.toGrothendieck_eq_sInf]
    apply sInf_le
    intro Y R hR
    change (Sieve.generate R).functorPushforward (integerActionInclusion (C := C)) ∈
      integerActionTopology J (IntegerActionSite.mk Y)
    rw [← Sieve.generate_map_eq_functorPushforward]
    apply (GrothendieckTopology.mem_sInf _ _).mpr
    intro L hL
    exact hL Y R hR
  constructor
  · intro hS
    exact hle _ hS
  · intro hS
    have h := hle' _ hS
    change (S.functorPullback (integerActionInclusion (C := C))).functorPushforward
      (integerActionInclusion (C := C)) ∈ integerActionTopology J (IntegerActionSite.mk X) at h
    rwa [integerActionInclusion_push_pull] at h

set_option backward.defeqAttrib.useBackward true in
private theorem integerActionInclusion_compatible
    (K : GrothendieckTopology (IntegerActionSite C)) :
    CompatiblePreserving.{w} K (integerActionInclusion (C := C)) := by
  constructor
  intro P Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ he
  let V : Over (IntegerActionSite.mk Z : IntegerActionSite C) :=
    Over.mk (f₁ ≫ (integerActionInclusion (C := C)).map g₁)
  let e := integerActionSliceCounitObj V
  have hdeg : f₁.1 = f₂.1 := by
    have hh := congrArg Sigma.fst he
    change f₁.1 + 0 = f₂.1 + 0 at hh
    omega
  let q₁ := e.hom.left ≫ f₁
  let q₂ := e.hom.left ≫ f₂
  have hq₁ : q₁.1 = 0 := by
    change -(f₁.1 + 0) + f₁.1 = 0
    omega
  have hq₂ : q₂.1 = 0 := by
    change -(f₁.1 + 0) + f₂.1 = 0
    omega
  let b₁ := (ShiftedHom.homEquiv 0 rfl).symm (hq₁ ▸ q₁.2)
  let b₂ := (ShiftedHom.homEquiv 0 rfl).symm (hq₂ ▸ q₂.2)
  have hb₁ : (integerActionInclusion (C := C)).map b₁ = q₁ :=
    integerActionInclusion_zero q₁ hq₁
  have hb₂ : (integerActionInclusion (C := C)).map b₂ = q₂ :=
    integerActionInclusion_zero q₂ hq₂
  have hb : b₁ ≫ g₁ = b₂ ≫ g₂ := by
    let := integerActionInclusion_faithful (C := C)
    apply (integerActionInclusion (C := C)).map_injective
    rw [Functor.map_comp, Functor.map_comp, hb₁, hb₂]
    change (e.hom.left ≫ f₁) ≫ _ = (e.hom.left ≫ f₂) ≫ _
    rw [Category.assoc, Category.assoc, he]
  apply (P.obj.mapIso ((Over.forget _).mapIso e).op).toEquiv.injective
  change P.obj.map e.hom.left.op (P.obj.map f₁.op (x g₁ hg₁)) =
    P.obj.map e.hom.left.op (P.obj.map f₂.op (x g₂ hg₂))
  have hh := hx b₁ b₂ hg₁ hg₂ hb
  change P.obj.map ((integerActionInclusion (C := C)).map b₁).op (x g₁ hg₁) =
    P.obj.map ((integerActionInclusion (C := C)).map b₂).op (x g₂ hg₂) at hh
  have h₁ : ((integerActionInclusion (C := C)).map b₁).op =
      f₁.op ≫ e.hom.left.op := congrArg Quiver.Hom.op hb₁
  have h₂ : ((integerActionInclusion (C := C)).map b₂).op =
      f₂.op ≫ e.hom.left.op := congrArg Quiver.Hom.op hb₂
  exact (P.obj.map_comp_apply f₁.op e.hom.left.op (x g₁ hg₁)).symm.trans
    ((congrArg (fun k ↦ P.obj.map k (x g₁ hg₁)) h₁.symm).trans
      (hh.trans ((congrArg (fun k ↦ P.obj.map k (x g₂ hg₂)) h₂).trans
        (P.obj.map_comp_apply f₂.op e.hom.left.op (x g₂ hg₂)))))

/-- Cover normalization and the sheaf criterion on the existing integer action site.
Source: the slice normalization in the proof above, Stacks Sites 00W0 motivation.
(blueprint: lem-sf-integer-action-topology-criterion).

Proof: normalize labelled arrows by their power isomorphisms. Pulling a sieve back
along inclusion and generating its image are inverse operations, and the generated
topology consists exactly of sieves whose pullbacks cover. Compatibility of families
is tested after precomposition with the normalization isomorphism; both resulting
arrows have degree zero and hence are base arrows. This proves continuity. In the
reverse direction restrict a compatible family to degree zero and glue in the base
site. The normalization isomorphism and compatibility show that the resulting
section glues every labelled arrow. Uniqueness is already detected in degree zero.
No nonempty-cover or nonempty-category assumption is used. -/
theorem integerActionTopologyCriterion
    (J : Precoverage C)
    (hcover : ∀ (n : ℤ) (X : C) (R : Presieve X),
      R ∈ J X ↔ R.map (shiftFunctor C n) ∈ J ((shiftFunctor C n).obj X)) :
    (∀ (X : C) (S : Sieve (IntegerActionSite.mk X : IntegerActionSite C)),
      S ∈ integerActionTopology J (IntegerActionSite.mk X) ↔
        S.functorPullback (integerActionInclusion (C := C)) ∈ J.toGrothendieck X) ∧
    (integerActionInclusion (C := C)).IsContinuous J.toGrothendieck
      (integerActionTopology J) ∧
    (∀ P : (IntegerActionSite C)ᵒᵖ ⥤ Type w,
      Presieve.IsSheaf (integerActionTopology J) P ↔
        Presieve.IsSheaf J.toGrothendieck
          ((integerActionInclusion (C := C)).op ⋙ P)) := by
  have hc : (integerActionInclusion (C := C)).IsContinuous J.toGrothendieck
      (integerActionTopology J) :=
    Functor.isContinuous_of_coverPreserving
      (integerActionInclusion_compatible (integerActionTopology J))
      ⟨fun {X S} hS ↦ (integerActionTopology_mem J hcover X _).mpr (by
        rwa [integerActionInclusion_pull_push])⟩
  refine ⟨integerActionTopology_mem J hcover, hc, ?_⟩
  let := hc
  intro P
  constructor
  · intro h
    exact (integerActionInclusion (C := C)).op_comp_isSheaf_of_isSheaf_type
      J.toGrothendieck h
  · intro h X S hS x hx
    obtain ⟨X⟩ := X
    let T := S.functorPullback (integerActionInclusion (C := C))
    have hT : T ∈ J.toGrothendieck X := (integerActionTopology_mem J hcover X S).mp hS
    let y : Presieve.FamilyOfElements
        ((integerActionInclusion (C := C)).op ⋙ P) T.arrows :=
      fun _ f hf ↦ x ((integerActionInclusion (C := C)).map f) hf
    have hy : y.Compatible := by
      intro Y₁ Y₂ Z f₁ f₂ g₁ g₂ hg₁ hg₂ he
      exact hx ((integerActionInclusion (C := C)).map f₁)
        ((integerActionInclusion (C := C)).map f₂) hg₁ hg₂ (by
          simpa only [← Functor.map_comp] using
            congrArg (integerActionInclusion (C := C)).map he)
    let t := (h T hT).amalgamate y hy
    refine ⟨t, ?_, ?_⟩
    · intro Y f hf
      let V : Over (IntegerActionSite.mk X : IntegerActionSite C) := Over.mk f
      let Q := integerActionSliceNormalize V
      let e := integerActionSliceCounitObj V
      have hw : e.hom.left ≫ f = (integerActionInclusion (C := C)).map Q.hom := Over.w e.hom
      have hQ : T Q.hom := by
        change S ((integerActionInclusion (C := C)).map Q.hom)
        rw [← hw]
        exact S.downward_closed hf _
      apply (P.mapIso ((Over.forget _).mapIso e).op).toEquiv.injective
      change P.map e.hom.left.op (P.map f.op t) = P.map e.hom.left.op (x f hf)
      have hw' : f.op ≫ e.hom.left.op =
          ((integerActionInclusion (C := C)).map Q.hom).op :=
        congrArg Quiver.Hom.op hw
      exact (P.map_comp_apply f.op e.hom.left.op t).symm.trans
        ((congrArg (fun k ↦ P.map k t) hw').trans
          (((h T hT).isAmalgamation hy Q.hom hQ).trans (by
            change x ((integerActionInclusion (C := C)).map Q.hom) hQ = _
            apply Eq.trans ?_ (hx.to_sieveCompatible f e.hom.left hf)
            congr 1
            exact hw.symm)))
    · intro t' ht'
      apply (h T hT).isSeparatedFor.ext
      intro Y f hf
      exact (ht' ((integerActionInclusion (C := C)).map f) hf).trans
        ((h T hT).isAmalgamation hy f hf).symm

end CategoryTheory
