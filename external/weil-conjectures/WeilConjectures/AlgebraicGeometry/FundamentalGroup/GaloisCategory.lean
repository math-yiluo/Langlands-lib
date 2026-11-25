/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.ColimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber

/-!
# The Galois category axioms for finite étale schemes

Let `Y` be a scheme. We verify the axioms of a (pre-)Galois category for the category
`FÉt(Y)` of finite étale `Y`-schemes, and, for connected `Y` and a geometric point `s`, the axioms
of a fibre functor for the geometric fibre functor `F_s`
(blueprint `lem-fet-finite-limits`, `lem-fet-galois-category`).

* Finite limits are computed in schemes.
* Finite coproducts are disjoint unions.
* The quotient of a finite étale `Y`-scheme `P` by a finite group `G` is glued from the spectra
  of the rings of invariants over the affine opens of `Y`
  (`AlgebraicGeometry.Scheme.hasColimitsOfShape_singleObj`); it is finite étale by
  `AlgHom.finite_and_etale_fixedPoints`, and its geometric points are the `G`-orbits of the
  geometric points of `P` (`AlgHom.surjective_comap_fixedPoints_val_and_iff`).
* A monomorphism is an open and closed immersion, hence the inclusion of a direct summand.
* The fibre functor is conservative: a morphism inducing a bijection on geometric fibres is a
  surjective monomorphism, by a clopen-image argument over the connected base.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}}

/-- The category of affine `Y`-schemes. -/
local instance :
    Category (MorphismProperty.Over (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ Y) :=
  MorphismProperty.Comma.instCategory _ _ _ _ _

local instance : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.inf

local instance : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).HasOfPostcompProperty
    (@IsFinite ⊓ @Etale) := by
  refine ⟨fun {X Y Z} f g hg hfg ↦ ?_⟩
  have := hg.1; have := hg.2; have := hfg.1; have := hfg.2
  exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩

variable (Y) in
/-- A finite étale `Y`-scheme as an affine `Y`-scheme. -/
@[simps]
noncomputable def toAffineOver :
    Y.FiniteEtale ⥤ MorphismProperty.Over (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ Y where
  obj P := MorphismProperty.Over.mk ⊤ P.obj.hom
    (by have : IsFinite P.obj.hom := P.property; infer_instance)
  map f := MorphismProperty.Over.homMk f.hom.left (hom_left_comp f) trivial

/-- The functor `FÉt(Y) ⥤ AffOver(Y)` is fully faithful. -/
noncomputable def toAffineOverFullyFaithful : (toAffineOver Y).FullyFaithful where
  preimage f :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk f.left (MorphismProperty.Over.w f))
  map_preimage f := MorphismProperty.Over.Hom.ext rfl
  preimage_map f := hom_ext rfl

instance : (toAffineOver Y).Full := toAffineOverFullyFaithful.full
instance : (toAffineOver Y).Faithful := toAffineOverFullyFaithful.faithful

/-- Two open immersions with disjoint images covering the target exhibit it as a coproduct. -/
lemma _root_.AlgebraicGeometry.isIso_coprodDesc_of_isOpenImmersion {X X' Z : Scheme.{u}}
    (a : X ⟶ Z) (b : X' ⟶ Z) [IsOpenImmersion a] [IsOpenImmersion b]
    (hdisj : ∀ x x', a x ≠ b x') (hcov : ∀ z, z ∈ Set.range a ∨ z ∈ Set.range b) :
    IsIso (coprod.desc a b) := by
  have hinl (x : X) : coprod.desc a b ((coprod.inl : X ⟶ X ⨿ X') x) = a x := by
    rw [← Scheme.Hom.comp_apply, coprod.inl_desc]
  have hinr (x : X') : coprod.desc a b ((coprod.inr : X' ⟶ X ⨿ X') x) = b x := by
    rw [← Scheme.Hom.comp_apply, coprod.inr_desc]
  have hpt (p : (X ⨿ X' : Scheme.{u})) :
      (∃ x, p = (coprod.inl : X ⟶ X ⨿ X') x) ∨ ∃ x', p = (coprod.inr : X' ⟶ X ⨿ X') x' := by
    obtain ⟨(x | x), rfl⟩ := (coprodMk X X').surjective p
    · exact .inl ⟨x, coprodMk_inl X X' x⟩
    · exact .inr ⟨x, coprodMk_inr X X' x⟩
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨IsOpenImmersion.iff_isIso_stalkMap.mpr ⟨?_, fun p ↦ ?_⟩, ⟨fun z ↦ ?_⟩⟩
  · refine .of_continuous_injective_isOpenMap (coprod.desc a b).continuous ?_ ?_
    · intro p q hpq
      rcases hpt p with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rcases hpt q with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · rw [hinl, hinl] at hpq; rw [a.isOpenEmbedding.injective hpq]
      · rw [hinl, hinr] at hpq; exact (hdisj _ _ hpq).elim
      · rw [hinr, hinl] at hpq; exact (hdisj _ _ hpq.symm).elim
      · rw [hinr, hinr] at hpq; rw [b.isOpenEmbedding.injective hpq]
    · intro U hU
      have : (coprod.desc a b) '' U =
          a '' ((coprod.inl : X ⟶ X ⨿ X') ⁻¹' U) ∪ b '' ((coprod.inr : X' ⟶ X ⨿ X') ⁻¹' U) := by
        ext z
        constructor
        · rintro ⟨p, hp, rfl⟩
          rcases hpt p with ⟨x, rfl⟩ | ⟨x, rfl⟩
          · exact .inl ⟨x, hp, (hinl x).symm⟩
          · exact .inr ⟨x, hp, (hinr x).symm⟩
        · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
          · exact ⟨_, hx, hinl x⟩
          · exact ⟨_, hx, hinr x⟩
      rw [this]
      exact (a.isOpenEmbedding.isOpenMap _ (hU.preimage (coprod.inl : X ⟶ X ⨿ X').continuous)).union
        (b.isOpenEmbedding.isOpenMap _ (hU.preimage (coprod.inr : X' ⟶ X ⨿ X').continuous))
  · rcases hpt p with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have h := Scheme.Hom.stalkMap_comp (coprod.inl : X ⟶ X ⨿ X') (coprod.desc a b) x
      rw [Scheme.Hom.stalkMap_congr_hom _ _ (coprod.inl_desc a b) x] at h
      have : IsIso ((coprod.desc a b).stalkMap ((coprod.inl : X ⟶ X ⨿ X') x) ≫
          (coprod.inl : X ⟶ X ⨿ X').stalkMap x) := by rw [← h]; infer_instance
      exact IsIso.of_isIso_comp_right _ ((coprod.inl : X ⟶ X ⨿ X').stalkMap x)
    · have h := Scheme.Hom.stalkMap_comp (coprod.inr : X' ⟶ X ⨿ X') (coprod.desc a b) x
      rw [Scheme.Hom.stalkMap_congr_hom _ _ (coprod.inr_desc a b) x] at h
      have : IsIso ((coprod.desc a b).stalkMap ((coprod.inr : X' ⟶ X ⨿ X') x) ≫
          (coprod.inr : X' ⟶ X ⨿ X').stalkMap x) := by rw [← h]; infer_instance
      exact IsIso.of_isIso_comp_right _ ((coprod.inr : X' ⟶ X ⨿ X').stalkMap x)
  · rcases hcov z with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · exact ⟨_, hinl x⟩
    · exact ⟨_, hinr x⟩

section Limits

/-- A coproduct of two étale morphisms is étale. -/
lemma _root_.AlgebraicGeometry.Etale.coprodDesc {X X' Z : Scheme.{u}} (f : X ⟶ Z) (g : X' ⟶ Z)
    [Etale f] [Etale g] : Etale (coprod.desc f g) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Etale) (coprodOpenCover.{_, 0} X X')]
  rintro (⟨⟩ | ⟨⟩)
  · simpa [coprodOpenCover] using ‹Etale f›
  · simpa [coprodOpenCover] using ‹Etale g›

variable (Y) in
/-- `FÉt(Y)` as the category of `Y`-schemes with finite étale structure morphism. -/
@[simps]
noncomputable def toFiniteEtaleOver :
    Y.FiniteEtale ⥤ (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).Over ⊤ Y where
  obj P := MorphismProperty.Over.mk ⊤ P.obj.hom ⟨P.property, P.obj.prop⟩
  map f := MorphismProperty.Over.homMk f.hom.left (hom_left_comp f) trivial

/-- `FÉt(Y) ⥤ (finite ⊓ étale).Over Y` is fully faithful. -/
noncomputable def toFiniteEtaleOverFullyFaithful : (toFiniteEtaleOver Y).FullyFaithful where
  preimage f :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk f.left (MorphismProperty.Over.w f))
  map_preimage f := MorphismProperty.Over.Hom.ext rfl
  preimage_map f := hom_ext rfl

instance : (toFiniteEtaleOver Y).Full := toFiniteEtaleOverFullyFaithful.full
instance : (toFiniteEtaleOver Y).Faithful := toFiniteEtaleOverFullyFaithful.faithful
instance : (toFiniteEtaleOver Y).EssSurj where
  mem_essImage A := ⟨⟨MorphismProperty.Over.mk ⊤ A.hom A.prop.2, A.prop.1⟩,
    ⟨MorphismProperty.Over.isoMk (Iso.refl _)⟩⟩
instance : (toFiniteEtaleOver Y).IsEquivalence where

instance : HasFiniteLimits Y.FiniteEtale :=
  ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence (toFiniteEtaleOver Y)⟩

variable (Y) in
/-- The underlying scheme of a finite étale `Y`-scheme. -/
noncomputable abbrev forgetScheme : Y.FiniteEtale ⥤ Scheme.{u} :=
  toFiniteEtaleOver Y ⋙ MorphismProperty.Over.forget _ ⊤ Y ⋙ Over.forget Y

instance : PreservesLimitsOfShape WalkingCospan (forgetScheme Y) := inferInstance

instance {P Q : Y.FiniteEtale} (i : P ⟶ Q) [Mono i] : Mono i.hom.left :=
  (forgetScheme Y).map_mono i

/-- The initial finite étale `Y`-scheme: the empty scheme. -/
noncomputable def empty : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (Scheme.emptyTo Y) inferInstance,
    show IsFinite (Scheme.emptyTo Y) from inferInstance⟩

/-- The empty scheme is initial in `FÉt(Y)`. -/
noncomputable def isInitialEmpty : IsInitial (empty (Y := Y)) :=
  IsInitial.ofUniqueHom
    (fun _ ↦ ObjectProperty.homMk (MorphismProperty.Over.homMk (Scheme.emptyTo _)
      (_root_.AlgebraicGeometry.emptyIsInitial.hom_ext _ _) trivial))
    (fun _ _ ↦ hom_ext (_root_.AlgebraicGeometry.emptyIsInitial.hom_ext _ _))

/-- The disjoint union of two finite étale `Y`-schemes. -/
noncomputable def coprod (P Q : Y.FiniteEtale) : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ (Limits.coprod.desc P.obj.hom Q.obj.hom)
    (by have := P.obj.prop; have := Q.obj.prop; exact Etale.coprodDesc _ _),
    by
      have : IsFinite P.obj.hom := P.property
      have : IsFinite Q.obj.hom := Q.property
      exact show IsFinite (Limits.coprod.desc P.obj.hom Q.obj.hom) from inferInstance⟩

/-- The disjoint union is a coproduct in `FÉt(Y)`. -/
noncomputable def coprodCofan (P Q : Y.FiniteEtale) : BinaryCofan P Q :=
  BinaryCofan.mk
    (ObjectProperty.homMk (MorphismProperty.Over.homMk Limits.coprod.inl
      (Limits.coprod.inl_desc _ _)) : P ⟶ coprod P Q)
    (ObjectProperty.homMk (MorphismProperty.Over.homMk Limits.coprod.inr
      (Limits.coprod.inr_desc _ _)) : Q ⟶ coprod P Q)

/-- The disjoint union is a coproduct in `FÉt(Y)`. -/
noncomputable def isColimitCoprodCofan (P Q : Y.FiniteEtale) : IsColimit (coprodCofan P Q) :=
  BinaryCofan.IsColimit.mk _
    (fun f g ↦ ObjectProperty.homMk (MorphismProperty.Over.homMk
      (Limits.coprod.desc f.hom.left g.hom.left)
      (by
        apply Limits.coprod.hom_ext
        · exact (Limits.coprod.inl_desc_assoc _ _ _).trans
            ((hom_left_comp f).trans (Limits.coprod.inl_desc _ _).symm)
        · exact (Limits.coprod.inr_desc_assoc _ _ _).trans
            ((hom_left_comp g).trans (Limits.coprod.inr_desc _ _).symm))))
    (fun f g ↦ hom_ext (Limits.coprod.inl_desc _ _))
    (fun f g ↦ hom_ext (Limits.coprod.inr_desc _ _))
    (fun f g m h₁ h₂ ↦ hom_ext (by
      apply Limits.coprod.hom_ext
      · exact congr(($h₁).hom.left).trans (Limits.coprod.inl_desc _ _).symm
      · exact congr(($h₂).hom.left).trans (Limits.coprod.inr_desc _ _).symm))

instance : HasBinaryCoproducts Y.FiniteEtale :=
  @hasBinaryCoproducts_of_hasColimit_pair _ _ (fun {P Q} ↦ ⟨⟨_, isColimitCoprodCofan P Q⟩⟩)

instance : HasInitial Y.FiniteEtale := isInitialEmpty.hasInitial

instance : HasFiniteCoproducts Y.FiniteEtale :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- Two morphisms of finite étale `Y`-schemes which are open immersions with disjoint images
covering the target exhibit it as a coproduct. -/
noncomputable def isColimitOfIsOpenImmersion {X X' Z : Y.FiniteEtale} (i : X ⟶ Z) (j : X' ⟶ Z)
    [IsOpenImmersion i.hom.left] [IsOpenImmersion j.hom.left]
    (hdisj : ∀ x x', i.hom.left x ≠ j.hom.left x')
    (hcov : ∀ z, z ∈ Set.range i.hom.left ∨ z ∈ Set.range j.hom.left) :
    IsColimit (BinaryCofan.mk i j) :=
  have : IsIso ((forgetScheme Y).map
      ((isColimitCoprodCofan X X').desc (BinaryCofan.mk i j))) := by
    change IsIso (coprod.desc i.hom.left j.hom.left)
    exact isIso_coprodDesc_of_isOpenImmersion _ _ hdisj hcov
  have : IsIso ((isColimitCoprodCofan X X').desc (BinaryCofan.mk i j)) :=
    isIso_of_reflects_iso _ (forgetScheme Y)
  IsColimit.ofPointIso (isColimitCoprodCofan X X')

instance (Z : Y.FiniteEtale) (V : Z.obj.left.Opens) (hV : IsClosed (V : Set Z.obj.left)) :
    IsOpenImmersion (ofIsClopenι Z V hV).hom.left :=
  inferInstanceAs (IsOpenImmersion V.ι)

/-- An open and closed subscheme and its complement form a coproduct decomposition. -/
noncomputable def isColimitOfIsClopen (Z : Y.FiniteEtale) (V : Z.obj.left.Opens)
    (hV : IsClosed (V : Set Z.obj.left)) :
    IsColimit (BinaryCofan.mk (ofIsClopenι Z V hV)
      (ofIsClopenι Z ⟨(V : Set Z.obj.left)ᶜ, hV.isOpen_compl⟩
        (isClosed_compl_iff.mpr V.isOpen))) := by
  refine isColimitOfIsOpenImmersion _ _ (fun x w hxw ↦ ?_) (fun z ↦ ?_)
  · let x' : V := x
    let w' : (⟨_, hV.isOpen_compl⟩ : Z.obj.left.Opens) := w
    have hxw' : x'.1 = w'.1 := hxw
    exact w'.2 (hxw' ▸ x'.2)
  · by_cases hz : z ∈ V
    · exact .inl ⟨⟨z, hz⟩, rfl⟩
    · exact .inr ⟨⟨z, hz⟩, rfl⟩

/-- **Monomorphisms are inclusions of direct summands** in `FÉt(Y)`: a monomorphism of finite
étale `Y`-schemes is an étale monomorphism, hence an open immersion, and it is finite, hence
closed; its image is open and closed, and the complement is the other summand. -/
lemma monoInducesIsoOnDirectSummand {X Z : Y.FiniteEtale} (i : X ⟶ Z) [Mono i] :
    ∃ (Z' : Y.FiniteEtale) (u : Z' ⟶ Z), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  have : IsOpenImmersion i.hom.left := IsOpenImmersion.of_flat_of_mono _
  let V : Z.obj.left.Opens := i.hom.left.opensRange
  have hVc : IsClosed (V : Set Z.obj.left) := i.hom.left.isClosedMap.isClosed_range
  let W : Z.obj.left.Opens := ⟨(V : Set Z.obj.left)ᶜ, hVc.isOpen_compl⟩
  have hW : IsClosed (W : Set Z.obj.left) := isClosed_compl_iff.mpr V.isOpen
  refine ⟨ofIsClopen Z W hW, ofIsClopenι Z W hW, ⟨isColimitOfIsOpenImmersion _ _
    (fun x w hxw ↦ ?_) (fun z ↦ ?_)⟩⟩
  · have : W.ι w ∈ W := by simp
    exact this ⟨x, hxw⟩
  · by_cases hz : z ∈ V
    · exact .inl hz
    · exact .inr ⟨⟨z, hz⟩, rfl⟩

end Limits

section FiberLimits

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The fibre functor followed by the inclusion into types is corepresented by `s` on
`Y`-schemes. -/
noncomputable def fiberCompInclIso : fiber s ⋙ FintypeCat.incl ≅
    toFiniteEtaleOver Y ⋙ MorphismProperty.Over.forget _ ⊤ Y ⋙ coyoneda.obj (.op (Over.mk s)) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

instance : PreservesFiniteLimits (fiber s ⋙ FintypeCat.incl) :=
  preservesFiniteLimits_of_natIso (fiberCompInclIso s).symm

instance : PreservesFiniteLimits (fiber s) :=
  preservesFiniteLimits_of_reflects_of_preserves (fiber s) FintypeCat.incl

omit [IsSepClosed Ω] in
/-- A geometric point of a disjoint union factors through one of the summands. -/
lemma _root_.AlgebraicGeometry.exists_eq_comp_inl_or_inr {X X' : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X ⨿ X') :
    (∃ y, x = y ≫ (coprod.inl : X ⟶ X ⨿ X')) ∨ ∃ y, x = y ≫ (coprod.inr : X' ⟶ X ⨿ X') := by
  have hpt (p : Spec (.of Ω)) : p = default := Subsingleton.elim _ _
  obtain ⟨(a | a), ha⟩ := (coprodMk X X').surjective (x default)
  · left
    have h : Set.range x ⊆ Set.range (coprod.inl : X ⟶ X ⨿ X') := by
      rintro _ ⟨p, rfl⟩
      exact ⟨a, by rw [hpt p, ← ha, coprodMk_inl]⟩
    exact ⟨IsOpenImmersion.lift _ x h, (IsOpenImmersion.lift_fac _ _ h).symm⟩
  · right
    have h : Set.range x ⊆ Set.range (coprod.inr : X' ⟶ X ⨿ X') := by
      rintro _ ⟨p, rfl⟩
      exact ⟨a, by rw [hpt p, ← ha, coprodMk_inr]⟩
    exact ⟨IsOpenImmersion.lift _ x h, (IsOpenImmersion.lift_fac _ _ h).symm⟩

lemma isColimit_binaryCofan_fiber (P Q : Y.FiniteEtale) :
    Nonempty (IsColimit (BinaryCofan.mk ((fiber s ⋙ FintypeCat.incl).map (coprodCofan P Q).inl)
      ((fiber s ⋙ FintypeCat.incl).map (coprodCofan P Q).inr))) := by
  rw [Types.binaryCofan_isColimit_iff]
  have hinl (y y' : (fiber s).obj P) (h : (fiber s).map (coprodCofan P Q).inl y =
      (fiber s).map (coprodCofan P Q).inl y') : y = y' := by
    apply fiber_ext
    have := congr_arg (fun z : (fiber s).obj (coprod P Q) ↦ z.left) h
    simp only [fiber_map_left] at this
    exact (cancel_mono (coprod.inl : P.obj.left ⟶ P.obj.left ⨿ Q.obj.left)).mp this
  have hinr (y y' : (fiber s).obj Q) (h : (fiber s).map (coprodCofan P Q).inr y =
      (fiber s).map (coprodCofan P Q).inr y') : y = y' := by
    apply fiber_ext
    have := congr_arg (fun z : (fiber s).obj (coprod P Q) ↦ z.left) h
    simp only [fiber_map_left] at this
    exact (cancel_mono (coprod.inr : Q.obj.left ⟶ P.obj.left ⨿ Q.obj.left)).mp this
  refine ⟨hinl, hinr, ⟨?_, ?_⟩⟩
  · rw [Set.disjoint_iff]
    rintro _ ⟨⟨y, rfl⟩, ⟨y', hy'⟩⟩
    change (fiber s).obj P at y
    change (fiber s).obj Q at y'
    change (fiber s).map (coprodCofan P Q).inr y' = (fiber s).map (coprodCofan P Q).inl y at hy'
    have := congr_arg (fun z : (fiber s).obj (coprod P Q) ↦ z.left) hy'
    simp only [fiber_map_left] at this
    have := congr_arg (fun g : Spec (.of Ω) ⟶ P.obj.left ⨿ Q.obj.left ↦ g (default : Spec (.of Ω)))
      this
    simp only [Scheme.Hom.comp_apply] at this
    exact inr_ne_inl _ _ _ _ this
  · refine codisjoint_iff.mpr (Set.eq_univ_of_forall fun x ↦ ?_)
    change (fiber s).obj (coprod P Q) at x
    rcases exists_eq_comp_inl_or_inr x.left with ⟨y, hy⟩ | ⟨y, hy⟩
    · refine .inl ⟨Over.homMk y ?_, fiber_ext s ?_⟩
      · change y ≫ P.obj.hom = s
        rw [← fiber_left_comp s x, hy, Category.assoc]
        exact congr_arg (y ≫ ·) (coprod.inl_desc _ _).symm
      · exact hy.symm
    · refine .inr ⟨Over.homMk y ?_, fiber_ext s ?_⟩
      · change y ≫ Q.obj.hom = s
        rw [← fiber_left_comp s x, hy, Category.assoc]
        exact congr_arg (y ≫ ·) (coprod.inr_desc _ _).symm
      · exact hy.symm

instance (P Q : Y.FiniteEtale) : PreservesColimit (pair P Q) (fiber s) :=
  preservesColimit_of_preserves_colimit_cocone (isColimitCoprodCofan P Q)
    (isColimitOfReflects FintypeCat.incl
      ((isColimitMapCoconeBinaryCofanEquiv (fiber s ⋙ FintypeCat.incl) _ _).symm
        (isColimit_binaryCofan_fiber s P Q).some))

lemma isEmpty_fiber_empty : IsEmpty ((fiber s).obj (empty (Y := Y))) :=
  ⟨fun x ↦ (inferInstance : IsEmpty (∅ : Scheme.{u})).false (x.left (default : Spec (.of Ω)))⟩

instance : PreservesColimit (Functor.empty.{0} Y.FiniteEtale) (fiber s) := by
  have := isEmpty_fiber_empty s
  obtain ⟨h⟩ := (Types.initial_iff_empty ((fiber s ⋙ FintypeCat.incl).obj empty)).mpr this
  exact preservesColimit_of_preserves_colimit_cocone isInitialEmpty
    ((isColimitMapCoconeEmptyCoconeEquiv _ _).symm (IsInitial.isInitialOfObj FintypeCat.incl _ h))

instance : PreservesColimitsOfShape (Discrete WalkingPair) (fiber s) :=
  ⟨fun {K} ↦ preservesColimit_of_iso_diagram _ (diagramIsoPair K).symm⟩

instance : PreservesColimitsOfShape (Discrete PEmpty.{1}) (fiber s) :=
  preservesColimitsOfShape_pempty_of_preservesInitial (fiber s)

instance : PreservesFiniteCoproducts (fiber s) :=
  ⟨fun n ↦ PreservesFiniteCoproducts.of_preserves_binary_and_initial (fiber s) (Fin n)⟩

omit [IsSepClosed Ω] in
/-- An epimorphism of finite étale `Y`-schemes is surjective: its image is open and closed, and
the two maps to `Q ⊔ Q` which agree on the image and differ on its complement are equalised by
it. -/
lemma surjective_of_epi {P Q : Y.FiniteEtale} (f : P ⟶ Q) [Epi f] :
    Function.Surjective f.hom.left := by
  let V : Q.obj.left.Opens := ⟨Set.range f.hom.left, f.hom.left.isOpenMap.isOpen_range⟩
  have hV : IsClosed (V : Set Q.obj.left) := f.hom.left.isClosedMap.isClosed_range
  let hc := isColimitOfIsClopen Q V hV
  let W : Q.obj.left.Opens := ⟨(V : Set Q.obj.left)ᶜ, hV.isOpen_compl⟩
  have hW : IsClosed (W : Set Q.obj.left) := isClosed_compl_iff.mpr V.isOpen
  have hrange : Set.range f.hom.left ⊆ Set.range (ofIsClopenι Q V hV).hom.left := by
    rintro _ ⟨p, rfl⟩
    exact ⟨⟨_, p, rfl⟩, rfl⟩
  let f' : P ⟶ ofIsClopen Q V hV := ObjectProperty.homMk (MorphismProperty.Over.homMk
    (IsOpenImmersion.lift (ofIsClopenι Q V hV).hom.left f.hom.left hrange) (by
      have h := IsOpenImmersion.lift_fac (ofIsClopenι Q V hV).hom.left f.hom.left hrange
      calc _ = (IsOpenImmersion.lift _ _ hrange ≫ (ofIsClopenι Q V hV).hom.left) ≫
            Q.obj.hom := (Category.assoc _ _ _).symm
        _ = P.obj.hom := by rw [h, hom_left_comp]))
  have hf : f' ≫ ofIsClopenι Q V hV = f :=
    hom_ext (IsOpenImmersion.lift_fac (ofIsClopenι Q V hV).hom.left f.hom.left hrange)
  obtain ⟨g, hg₁, hg₂⟩ := BinaryCofan.IsColimit.desc' hc
    (ofIsClopenι Q V hV ≫ (coprodCofan Q Q).inl) (ofIsClopenι Q W hW ≫ (coprodCofan Q Q).inr)
  simp only [BinaryCofan.mk_inl, BinaryCofan.mk_inr] at hg₁ hg₂
  have hinl : (coprodCofan Q Q).inl = g := by
    rw [← cancel_epi f, ← hf, Category.assoc, Category.assoc, hg₁]
  intro q
  by_contra hq
  let w : (W : Set Q.obj.left) := ⟨q, fun h ↦ hq h⟩
  have := congr_arg (fun φ : ofIsClopen Q W hW ⟶ coprod Q Q ↦ φ.hom.left w)
    (show ofIsClopenι Q W hW ≫ (coprodCofan Q Q).inl = ofIsClopenι Q W hW ≫ (coprodCofan Q Q).inr
      by rw [hinl, hg₂])
  exact inl_ne_inr _ _ _ _ this

instance : (fiber s).PreservesEpimorphisms where
  preserves f _ := by
    have : Epi (FintypeCat.incl.map ((fiber s).map f)) :=
      (epi_iff_surjective _).mpr (surjective_fiber_map_of_surjective s f (surjective_of_epi f))
    exact FintypeCat.incl.epi_of_epi_map this

section Connected

variable [ConnectedSpace Y]

/-- Over a connected base, a morphism of finite étale `Y`-schemes which is surjective on
geometric fibres is surjective: the complement of its image is an open and closed subscheme
with empty geometric fibre, hence empty. -/
lemma surjective_of_surjective_fiber {P Q : Y.FiniteEtale} (f : P ⟶ Q)
    (h : Function.Surjective ((fiber s).map f)) : Function.Surjective f.hom.left := by
  have hV : IsClosed (Set.range f.hom.left) := f.hom.left.isClosedMap.isClosed_range
  let W : Q.obj.left.Opens := ⟨(Set.range f.hom.left)ᶜ, hV.isOpen_compl⟩
  have hW : IsClosed (W : Set Q.obj.left) :=
    isClosed_compl_iff.mpr f.hom.left.isOpenMap.isOpen_range
  intro q
  by_contra hq
  obtain ⟨x⟩ := (nonempty_fiber_iff s (ofIsClopen Q W hW)).mpr
    ⟨(⟨q, hq⟩ : (W : Set Q.obj.left))⟩
  obtain ⟨z, hz⟩ := h ((fiber s).map (ofIsClopenι Q W hW) x)
  have := congr_arg (fun y : (fiber s).obj Q ↦ (y.left : Spec (.of Ω) ⟶ Q.obj.left)
    (default : Spec (.of Ω))) hz
  simp only [fiber_map_left, Scheme.Hom.comp_apply] at this
  let w : (W : Set Q.obj.left) := x.left (default : Spec (.of Ω))
  exact w.2 ⟨_, this⟩

/-- Over a connected base, a monomorphism of finite étale `Y`-schemes which is surjective on
geometric fibres is an isomorphism: it is a surjective open immersion. -/
lemma isIso_of_mono_of_surjective_fiber {P Q : Y.FiniteEtale} (i : P ⟶ Q) [Mono i]
    (h : Function.Surjective ((fiber s).map i)) : IsIso i := by
  have : IsOpenImmersion i.hom.left := IsOpenImmersion.of_flat_of_mono _
  have : IsIso ((forgetScheme Y).map i) :=
    (isIso_iff_isOpenImmersion_and_surjective i.hom.left).mpr
      ⟨inferInstance, ⟨surjective_of_surjective_fiber s i h⟩⟩
  exact isIso_of_reflects_iso i (forgetScheme Y)

/-- Over a connected base, the fibre functor reflects isomorphisms. -/
lemma isIso_of_isIso_fiber_map {P Q : Y.FiniteEtale} (f : P ⟶ Q)
    [IsIso ((fiber s).map f)] : IsIso f := by
  have hbij : Function.Bijective ((fiber s).map f) := ConcreteCategory.bijective_of_isIso _
  -- `f` is a monomorphism: the diagonal `P ⟶ P ×_Q P` is surjective on fibres
  let δ : P ⟶ pullback f f := pullback.lift (𝟙 P) (𝟙 P) rfl
  have : IsSplitMono δ := IsSplitMono.mk' ⟨pullback.fst f f, by simp [δ]⟩
  have hδ : Function.Surjective ((fiber s).map δ) := by
    intro e
    let hD := isLimitOfPreserves (fiber s ⋙ FintypeCat.incl) (pullbackIsPullback f f)
    have hfs : (fiber s).map f ((fiber s).map (pullback.fst f f) e) =
        (fiber s).map f ((fiber s).map (pullback.snd f f) e) := by
      rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
        ← Functor.map_comp, pullback.condition]
    have hab := hbij.1 hfs
    set a := (fiber s).map (pullback.fst f f) e
    have hfst : (fiber s).map (pullback.fst f f) ((fiber s).map δ a) = a := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, pullback.lift_fst,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    have hsnd : (fiber s).map (pullback.snd f f) ((fiber s).map δ a) = a := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, pullback.lift_snd,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    refine ⟨a, (Concrete.isLimit_ext _ hD _ _ ?_).symm⟩
    rintro (_ | _ | _)
    · change (fiber s).map (pullback.fst f f ≫ f) e =
        (fiber s).map (pullback.fst f f ≫ f) ((fiber s).map δ a)
      rw [Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hfst]
    · change (fiber s).map (pullback.fst f f) e =
        (fiber s).map (pullback.fst f f) ((fiber s).map δ a)
      exact hfst.symm
    · change (fiber s).map (pullback.snd f f) e =
        (fiber s).map (pullback.snd f f) ((fiber s).map δ a)
      rw [hsnd]
      exact hab.symm
  have : IsIso δ := isIso_of_mono_of_surjective_fiber s δ hδ
  have hfs : pullback.fst f f = pullback.snd f f := by
    rw [← cancel_epi δ, pullback.lift_fst, pullback.lift_snd]
  have : Mono f := ⟨fun g h hgh ↦ by
    rw [← pullback.lift_fst g h hgh, hfs, pullback.lift_snd]⟩
  exact isIso_of_mono_of_surjective_fiber s f hbij.2

end Connected

end FiberLimits

/-- A cocone over a monoid action on a type is a colimit if its leg is surjective and identifies
exactly the points related by the equivalence relation generated by the action. -/
noncomputable def _root_.CategoryTheory.Limits.Types.isColimitOfSurjectiveOfEqvGen
    {M : Type*} [Monoid M] {J : SingleObj M ⥤ Type*} (c : Cocone J)
    (hs : Function.Surjective (c.ι.app (SingleObj.star M)))
    (hf : ∀ x y, c.ι.app (SingleObj.star M) x = c.ι.app (SingleObj.star M) y →
      Relation.EqvGen (fun x y ↦ ∃ m : M, J.map m x = y) x y) : IsColimit c where
  desc t := ↾fun z ↦ t.ι.app (SingleObj.star M) (Function.surjInv hs z)
  fac t j := by
    obtain rfl : j = SingleObj.star M := rfl
    ext x
    have key : ∀ x y, Relation.EqvGen (fun x y ↦ ∃ m : M, J.map m x = y) x y →
        t.ι.app (SingleObj.star M) x = t.ι.app (SingleObj.star M) y := by
      intro x y h
      induction h with
      | rel x y hxy =>
        obtain ⟨m, rfl⟩ := hxy
        exact (ConcreteCategory.congr_hom
          (t.w (j := SingleObj.star M) (j' := SingleObj.star M) m) x).symm
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact key _ _ (hf _ _ (Function.surjInv_eq hs _))
  uniq t m hm := by
    ext z
    obtain ⟨x, rfl⟩ := hs z
    have := ConcreteCategory.congr_hom (hm (SingleObj.star M)) x
    rw [ConcreteCategory.comp_apply] at this
    have key : ∀ x y, Relation.EqvGen (fun x y ↦ ∃ m : M, J.map m x = y) x y →
        t.ι.app (SingleObj.star M) x = t.ι.app (SingleObj.star M) y := by
      intro x y h
      induction h with
      | rel x y hxy =>
        obtain ⟨m, rfl⟩ := hxy
        exact (ConcreteCategory.congr_hom
          (t.w (j := SingleObj.star M) (j' := SingleObj.star M) m) x).symm
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact this.trans (key _ _ (hf _ _ (Function.surjInv_eq hs _).symm))

section AffinePoints

open RingHom

variable {Ω : Type u} [Field Ω]

/-- Over an affine base `X`, the geometric points of an affine `X`-scheme `W` over a geometric
point `s` of `X` are the points of the `Γ(X)`-algebra `Γ(W)` over the point of `Γ(X)` given by
`s`. -/
noncomputable def _root_.AlgebraicGeometry.Scheme.Hom.geometricFiberEquivPointsOverAppTop
    {X W : Scheme.{u}} [IsAffine X] [IsAffine W] (h : W ⟶ X) [Algebra Γ(X, ⊤) Γ(W, ⊤)]
    (hA : algebraMap Γ(X, ⊤) Γ(W, ⊤) = h.appTop.hom) (s : Spec (.of Ω) ⟶ X) :
    h.GeometricFiber s ≃ PointsOver (s.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom Γ(W, ⊤) where
  toFun x := ⟨(x.1.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom, by
    rw [hA, ← CommRingCat.hom_comp, ← Category.assoc, ← Hom.comp_appTop, x.2]⟩
  invFun t := ⟨homOfAppTop (CommRingCat.ofHom t.1 ≫ (ΓSpecIso (.of Ω)).inv), by
    apply ext_of_isAffine
    have ht : h.appTop ≫ CommRingCat.ofHom t.1 = s.appTop ≫ (ΓSpecIso (.of Ω)).hom :=
      CommRingCat.hom_ext (by rw [CommRingCat.hom_comp, ← hA]; exact t.2)
    rw [Hom.comp_appTop, homOfAppTop_appTop, ← Category.assoc, ht, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]⟩
  left_inv x := Hom.GeometricFiber.ext (ext_of_isAffine (by simp))
  right_inv t := PointsOver.ext fun b ↦ by simp

lemma _root_.AlgebraicGeometry.Scheme.Hom.geometricFiberEquivPointsOverAppTop_apply_coe
    {X W : Scheme.{u}} [IsAffine X] [IsAffine W] (h : W ⟶ X) [Algebra Γ(X, ⊤) Γ(W, ⊤)]
    (hA : algebraMap Γ(X, ⊤) Γ(W, ⊤) = h.appTop.hom) (s : Spec (.of Ω) ⟶ X)
    (x : h.GeometricFiber s) :
    (h.geometricFiberEquivPointsOverAppTop hA s x).1 =
      (x.1.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom :=
  rfl


/-- **Geometric points of a quotient over an affine base.** Let `K` be the action of a finite
monoid `G` on a finite étale scheme `W` over an affine scheme `X`, with quotient `c`. Then the
geometric points of the quotient over `s` are the classes of the geometric points of `W`:
the map is surjective, and two points have the same image iff they are related by the
equivalence relation generated by `x ~ x ∘ g`. -/
theorem _root_.AlgebraicGeometry.Scheme.geometricFiber_quotient_of_isAffine
    {P : MorphismProperty Scheme.{u}} (hP : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), P f → IsAffineHom f)
    (hP' : ∀ {Y Z : Scheme.{u}} (f : Y ⟶ Z), IsAffine Y → IsAffine Z → P f)
    {X : Scheme.{u}} [IsAffine X] {G : Type*} [Monoid G] [Finite G]
    (K : SingleObj G ⥤ P.Over ⊤ X) {c : Cocone K} (hc : IsColimit c)
    [IsFinite (K.obj (SingleObj.star G)).hom] [Etale (K.obj (SingleObj.star G)).hom]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Function.Surjective (fun x : (K.obj (SingleObj.star G)).hom.GeometricFiber s ↦
        (⟨x.1 ≫ (c.ι.app (SingleObj.star G)).left, by
          rw [Category.assoc]
          exact (congr_arg (x.1 ≫ ·) (MorphismProperty.Over.w (c.ι.app (SingleObj.star G)))).trans
            x.2⟩ : c.pt.hom.GeometricFiber s)) ∧
      ∀ x y : (K.obj (SingleObj.star G)).hom.GeometricFiber s,
        x.1 ≫ (c.ι.app (SingleObj.star G)).left = y.1 ≫ (c.ι.app (SingleObj.star G)).left ↔
          Relation.EqvGen (fun x y : (K.obj (SingleObj.star G)).hom.GeometricFiber s ↦
            ∃ g : G, y.1 = x.1 ≫ (K.map g).left) x y := by
  let W := K.obj (SingleObj.star G)
  let Q := c.pt
  have : IsAffine W.left := isAffine_left hP W
  have : IsAffine Q.left := isAffine_left hP Q
  have : IsAffine ((Functor.fromPUnit X).obj W.right) := ‹IsAffine X›
  have : IsAffine ((𝟭 Scheme).obj W.left) := ‹IsAffine W.left›
  let R := Γ(X, ⊤)
  let A := Γ(W.left, ⊤)
  let B := Γ(Q.left, ⊤)
  let : Algebra R A := W.hom.appTop.hom.toAlgebra
  let : Algebra R B := Q.hom.appTop.hom.toAlgebra
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
  have hι : Q.hom.appTop ≫ (c.ι.app (SingleObj.star G)).left.appTop = W.hom.appTop := by
    rw [← Hom.comp_appTop]
    congr 1
    exact MorphismProperty.Over.w _
  let α : B →ₐ[R] A :=
    { (c.ι.app (SingleObj.star G)).left.appTop.hom with
      commutes' r := congr($(hι).hom r) }
  obtain ⟨hinj, hrange⟩ := injective_appTop_of_isColimit hP K hP' hc
  have hrange' : α.range = AlgHom.fixedPoints σ := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      exact AlgHom.mem_fixedPoints.mpr fun g ↦ appTop_map_apply_of_cocone K c g b
    · intro ha
      obtain ⟨b, hb⟩ := hrange a (AlgHom.mem_fixedPoints.mp ha)
      exact ⟨b, hb⟩
  let eα : B ≃ₐ[R] AlgHom.fixedPoints σ :=
    (AlgEquiv.ofInjective α hinj).trans (Subalgebra.equivOfEq _ _ hrange')
  let φ := (s.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom
  let EW := Hom.geometricFiberEquivPointsOverAppTop (X := X) (W := W.left) W.hom rfl s
  let EQ := Hom.geometricFiberEquivPointsOverAppTop (X := X) (W := Q.left) Q.hom rfl s
  let π : W.hom.GeometricFiber s → Q.hom.GeometricFiber s := fun x ↦
    ⟨x.1 ≫ (c.ι.app (SingleObj.star G)).left, by
      rw [Category.assoc]
      exact (congr_arg (x.1 ≫ ·) (MorphismProperty.Over.w (c.ι.app (SingleObj.star G)))).trans
        x.2⟩
  have natQ (x : W.hom.GeometricFiber s) : EQ (π x) = PointsOver.comap α (EW x) :=
    PointsOver.ext fun b ↦ by
      change ((x.1 ≫ (c.ι.app (SingleObj.star G)).left).appTop ≫ (ΓSpecIso (.of Ω)).hom).hom b =
        (x.1.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom (α b)
      rw [Hom.comp_appTop]
      rfl
  have natW (x : W.hom.GeometricFiber s) (g : G) (y : W.hom.GeometricFiber s)
      (hy : y.1 = x.1 ≫ (K.map g).left) : EW y = PointsOver.comap (σ g) (EW x) :=
    PointsOver.ext fun a ↦ by
      change (y.1.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom a =
        (x.1.appTop ≫ (ΓSpecIso (.of Ω)).hom).hom (σ g a)
      rw [hy, Hom.comp_appTop]
      rfl
  have H := AlgHom.surjective_comap_fixedPoints_val_and_iff σ φ
  obtain ⟨H₁, H₂⟩ := Relation.surjective_and_iff_eqvGen_of_equiv EW.symm
    ((PointsOver.comapEquiv eα).trans EQ.symm)
    (PointsOver.comap (AlgHom.fixedPoints σ).val) π
    (r := fun x y : W.hom.GeometricFiber s ↦ ∃ g : G, y.1 = x.1 ≫ (K.map g).left)
    (fun t ↦ by
      apply EQ.injective
      rw [natQ, Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
      exact PointsOver.ext fun b ↦ rfl)
    (fun t t' ↦ by
      refine exists_congr fun g ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · let y : W.hom.GeometricFiber s := ⟨(EW.symm t).1 ≫ (K.map g).left, by
          rw [Category.assoc]
          exact (congr_arg ((EW.symm t).1 ≫ ·) (MorphismProperty.Over.w (K.map g))).trans
            (EW.symm t).2⟩
        have := natW (EW.symm t) g y rfl
        rw [Equiv.apply_symm_apply, ← h] at this
        rw [← this, Equiv.symm_apply_apply]
      · have := natW (EW.symm t) g (EW.symm t') h
        rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
        exact this)
    H
  refine ⟨H₁, fun x y ↦ ?_⟩
  rw [← H₂ x y]
  exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congr_arg Subtype.val h⟩

end AffinePoints

section Quotient

variable {G : Type u} [Monoid G] [Finite G] (D : SingleObj G ⥤ Y.FiniteEtale)

lemma isAffineHom_of_isAffineHom {X Z : Scheme.{u}} (f : X ⟶ Z) (hf : IsAffineHom f) :
    IsAffineHom f :=
  hf

/-- The gluing data for the quotient of a finite étale `Y`-scheme by a finite monoid action. -/
noncomputable abbrev quotientGluingData :
    Y.directedAffineCover.ColimitGluingData (D ⋙ toAffineOver Y) :=
  Scheme.quotientGluingData isAffineHom_of_isAffineHom
    @AlgebraicGeometry.isAffineHom_of_isAffine _

instance preservesColimitsOfShape_pullback_trans {U V : Y.directedAffineCover.I₀} (hUV : U ⟶ V) :
    PreservesColimitsOfShape (SingleObj G)
      (MorphismProperty.Over.pullback (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤
        (Y.directedAffineCover.trans hUV)) :=
  preservesColimitsOfShape_pullback isAffineHom_of_isAffineHom
    @AlgebraicGeometry.isAffineHom_of_isAffine _

/-- The quotient cocone in affine `Y`-schemes is a colimit. -/
noncomputable def isColimitGluedCocone : IsColimit (quotientGluingData D).gluedCocone :=
  (quotientGluingData D).isColimitGluedCocone

lemma isFinite_and_etale_gluedCocone :
    IsFinite (quotientGluingData D).gluedCocone.pt.hom ∧
      Etale (quotientGluingData D).gluedCocone.pt.hom := by
  have : IsFinite ((D ⋙ toAffineOver Y).obj (SingleObj.star G)).hom :=
    (D.obj (SingleObj.star G)).property
  have : Etale ((D ⋙ toAffineOver Y).obj (SingleObj.star G)).hom :=
    (D.obj (SingleObj.star G)).obj.prop
  exact isFinite_and_etale_of_isColimit isAffineHom_of_isAffineHom
    @AlgebraicGeometry.isAffineHom_of_isAffine _
    (isColimitGluedCocone D)

/-- The quotient of a finite étale `Y`-scheme by a finite monoid action, as a cocone in
`FÉt(Y)`. -/
noncomputable def quotientCocone : Cocone D where
  pt := ⟨MorphismProperty.Over.mk ⊤ (quotientGluingData D).gluedCocone.pt.hom
    (isFinite_and_etale_gluedCocone D).2, (isFinite_and_etale_gluedCocone D).1⟩
  ι :=
    { app j := ObjectProperty.homMk (MorphismProperty.Over.homMk
        ((quotientGluingData D).gluedCocone.ι.app j).left
        (MorphismProperty.Over.w ((quotientGluingData D).gluedCocone.ι.app j)))
      naturality j j' g := hom_ext
        congr(($((quotientGluingData D).gluedCocone.ι.naturality g)).left) }

/-- The quotient cocone is a colimit in `FÉt(Y)`. -/
noncomputable def isColimitQuotientCocone : IsColimit (quotientCocone D) :=
  isColimitOfReflects (toAffineOver Y)
    (IsColimit.ofIsoColimit (isColimitGluedCocone D)
      (Cocone.ext (MorphismProperty.Over.isoMk (Iso.refl _)) fun _ ↦
        MorphismProperty.Over.Hom.ext (by simp [quotientCocone])))

variable (Y G) in
/-- **`FÉt(Y)` has quotients by finite monoids.** -/
theorem hasColimitsOfShape_singleObj : HasColimitsOfShape (SingleObj G) Y.FiniteEtale :=
  ⟨fun D ↦ ⟨_, isColimitQuotientCocone D⟩⟩

section QuotientFiber

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

/-- The geometric points of a finite étale `Y`-scheme over `s` are the geometric points of its
base change to an open `U ∋ s` over the induced geometric point of `U`. -/
noncomputable def fiberEquivOfOpen {U : Scheme.{u}} (f : U ⟶ Y) (s' : Spec (.of Ω) ⟶ U)
    (hs' : s' ≫ f = s) (P : Y.FiniteEtale) :
    (pullback.snd P.obj.hom f).GeometricFiber s' ≃ (fiber s).obj P where
  toFun x := Over.homMk (x.1 ≫ pullback.fst _ _) (by
    change (x.1 ≫ pullback.fst _ _) ≫ P.obj.hom = s
    rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, hs'])
  invFun x := ⟨pullback.lift x.left s' ((fiber_left_comp s x).trans hs'.symm),
    pullback.lift_snd _ _ _⟩
  left_inv x := Hom.GeometricFiber.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans x.2.symm))
  right_inv x := fiber_ext s (pullback.lift_fst _ _ _)

lemma fiberEquivOfOpen_apply_left {U : Scheme.{u}} (f : U ⟶ Y) (s' : Spec (.of Ω) ⟶ U)
    (hs' : s' ≫ f = s) (P : Y.FiniteEtale) (x : (pullback.snd P.obj.hom f).GeometricFiber s') :
    (fiberEquivOfOpen s f s' hs' P x).left = x.1 ≫ pullback.fst _ _ :=
  rfl


/-- **The fibre functor preserves quotients**: the geometric points of the quotient of a finite
étale `Y`-scheme by a finite monoid are the classes of its geometric points under the equivalence
relation generated by the action. -/
theorem fiber_quotientCocone :
    Function.Surjective ((fiber s).map ((quotientCocone D).ι.app (SingleObj.star G))) ∧
      ∀ x y, (fiber s).map ((quotientCocone D).ι.app (SingleObj.star G)) x =
        (fiber s).map ((quotientCocone D).ι.app (SingleObj.star G)) y ↔
          Relation.EqvGen (fun x y ↦ ∃ g : G, (fiber s).map (D.map g) x = y) x y := by
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset (x := s default)
    (U := ⊤) trivial
  let i : Y.directedAffineCover.I₀ := ⟨U, hU⟩
  let f := Y.directedAffineCover.f i
  have hrange : Set.range s ⊆ Set.range f := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p default]
    exact ⟨⟨_, hsU⟩, rfl⟩
  let s' := IsOpenImmersion.lift f s hrange
  have hs' : s' ≫ f = s := IsOpenImmersion.lift_fac _ _ _
  have := preservesColimit_pullback_directedAffineCover isAffineHom_of_isAffineHom
    @AlgebraicGeometry.isAffineHom_of_isAffine (D ⋙ toAffineOver Y) i
  let F := MorphismProperty.Over.pullback (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ f
  let K' := (D ⋙ toAffineOver Y) ⋙ F
  let hc' := isColimitOfPreserves F (isColimitGluedCocone D)
  have : IsFinite (K'.obj (SingleObj.star G)).hom :=
    have : IsFinite ((D ⋙ toAffineOver Y).obj (SingleObj.star G)).hom :=
      (D.obj (SingleObj.star G)).property
    inferInstanceAs (IsFinite (pullback.snd _ _))
  have : Etale (K'.obj (SingleObj.star G)).hom :=
    have : Etale ((D ⋙ toAffineOver Y).obj (SingleObj.star G)).hom :=
      (D.obj (SingleObj.star G)).obj.prop
    inferInstanceAs (Etale (pullback.snd _ _))
  obtain ⟨H₁, H₂⟩ := geometricFiber_quotient_of_isAffine isAffineHom_of_isAffineHom
    @AlgebraicGeometry.isAffineHom_of_isAffine K' hc' s'
  let EW : (K'.obj (SingleObj.star G)).hom.GeometricFiber s' ≃
      (fiber s).obj (D.obj (SingleObj.star G)) :=
    fiberEquivOfOpen s f s' hs' (D.obj (SingleObj.star G))
  let EQ : (F.mapCocone (quotientGluingData D).gluedCocone).pt.hom.GeometricFiber s' ≃
      (fiber s).obj (quotientCocone D).pt :=
    fiberEquivOfOpen s f s' hs' (quotientCocone D).pt
  have hι : ∀ x : (K'.obj (SingleObj.star G)).hom.GeometricFiber s',
      (x.1 ≫ ((F.mapCocone (quotientGluingData D).gluedCocone).ι.app
        (SingleObj.star G)).left) ≫ pullback.fst _ _ =
      (x.1 ≫ pullback.fst _ _) ≫ ((quotientGluingData D).gluedCocone.ι.app
        (SingleObj.star G)).left := fun x ↦ by
    rw [Category.assoc, Category.assoc]
    exact congr_arg (x.1 ≫ ·) (pullback.lift_fst _ _ _)
  have hK (g : G) : ∀ x : (K'.obj (SingleObj.star G)).hom.GeometricFiber s',
      (x.1 ≫ (K'.map g).left) ≫ pullback.fst _ _ =
      (x.1 ≫ pullback.fst _ _) ≫ (D.map g).hom.left := fun x ↦ by
    rw [Category.assoc, Category.assoc]
    exact congr_arg (x.1 ≫ ·) (pullback.lift_fst _ _ _)
  refine Relation.surjective_and_iff_eqvGen_of_equiv EW EQ
    (fun x : (K'.obj (SingleObj.star G)).hom.GeometricFiber s' ↦
      (⟨x.1 ≫ ((F.mapCocone (quotientGluingData D).gluedCocone).ι.app (SingleObj.star G)).left,
        by
          rw [Category.assoc]
          exact (congr_arg (x.1 ≫ ·) (MorphismProperty.Over.w
            ((F.mapCocone (quotientGluingData D).gluedCocone).ι.app (SingleObj.star G)))).trans
            x.2⟩ :
        (F.mapCocone (quotientGluingData D).gluedCocone).pt.hom.GeometricFiber s'))
    ((fiber s).map ((quotientCocone D).ι.app (SingleObj.star G)))
    (fun x ↦ fiber_ext s (hι x))
    (fun x y ↦ exists_congr fun g ↦ ⟨fun h ↦ fiber_ext s ?_, fun h ↦ ?_⟩)
    ⟨H₁, fun x y ↦ (Subtype.ext_iff).trans (H₂ x y)⟩
  · rw [fiber_map_left]
    change (x.1 ≫ pullback.fst _ _) ≫ (D.map g).hom.left = y.1 ≫ pullback.fst _ _
    rw [h, hK]
  · let z : (K'.obj (SingleObj.star G)).hom.GeometricFiber s' := ⟨x.1 ≫ (K'.map g).left, by
      rw [Category.assoc]
      exact (congr_arg (x.1 ≫ ·) (MorphismProperty.Over.w (K'.map g))).trans x.2⟩
    have hz : EW z = EW y := by
      rw [← h]
      apply fiber_ext s
      rw [fiber_map_left]
      exact hK g x
    rw [← EW.injective hz]

end QuotientFiber

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

instance (G : Type u) [Monoid G] [Finite G] : PreservesColimitsOfShape (SingleObj G) (fiber s) :=
  ⟨fun {D} ↦ preservesColimit_of_preserves_colimit_cocone (isColimitQuotientCocone D)
    (isColimitOfReflects FintypeCat.incl
      (Types.isColimitOfSurjectiveOfEqvGen _ (fiber_quotientCocone D s).1
        fun x y h ↦ ((fiber_quotientCocone D s).2 x y).mp h))⟩

end Quotient

end AlgebraicGeometry.Scheme.FiniteEtale
