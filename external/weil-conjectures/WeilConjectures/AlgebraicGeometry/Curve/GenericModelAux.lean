/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.AlgebraicGeometry.GenericFiber.SpreadSmooth

/-!
# Auxiliary lemmas for the generic curve model

General facts used in the construction of the generic curve model
(`proposition-proper-direct-image-finite-coefficients`):

* `AlgebraicGeometry.isPullback_sigmaDesc`: finite coproducts of cartesian squares over a common
  base change are cartesian;
* `AlgebraicGeometry.IsPullback.exists_isPullback_morphismRestrict`: restricting a cartesian
  square over an open of the base;
* `AlgebraicGeometry.pullback_snd_iff_morphismRestrict`: a base change along an open immersion
  is a restriction;
* `AlgebraicGeometry.exists_genericPoint_mem_forall_notMem`: removing the closed image of an
  open set missing the generic fibre;
* `AlgebraicGeometry.smoothOfRelativeDimension_of_pullback_snd`: the relative dimension of a
  smooth morphism to an irreducible base is read off on the generic fibre;
* `AlgebraicGeometry.exists_comp_nilradical_subschemeι`: morphisms from reduced schemes factor
  through the reduction;
* `finite_compl_of_dense_of_topologicalKrullDim_le_one`: dense opens of a noetherian space of
  dimension at most one have finite complement.
-/

@[expose] public section

universe u

open CategoryTheory Limits Topology

/-- In a `T0` space, if `w ⤳ x ⤳ ξ` are proper specializations (`x ⤳ w`, `ξ ⤳ x`), the space
has Krull dimension at least two. -/
lemma two_le_topologicalKrullDim_of_specializes {X : Type*} [TopologicalSpace X] [T0Space X]
    {w x ξ : X} (hxw : x ⤳ w) (hξx : ξ ⤳ x) (hw : w ≠ x) (hx : x ≠ ξ) :
    (2 : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let C (y : X) : TopologicalSpace.IrreducibleCloseds X :=
    ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hlt {a b : X} (hab : b ⤳ a) (hne : a ≠ b) : C a < C b := by
    refine lt_of_le_of_ne (specializes_iff_closure_subset.mp hab) fun h ↦ hne ?_
    have h' : closure ({a} : Set X) = closure {b} :=
      congrArg (fun Z : TopologicalSpace.IrreducibleCloseds X ↦ (Z : Set X)) h
    exact (inseparable_iff_closure_eq.mpr h').eq
  let s : LTSeries (TopologicalSpace.IrreducibleCloseds X) :=
    ((RelSeries.singleton _ (C w)).snoc (C x) (hlt hxw hw)).snoc (C ξ)
      (by rw [RelSeries.last_snoc]; exact hlt hξx hx)
  have := Order.LTSeries.length_le_krullDim s
  simpa [s, topologicalKrullDim] using this

/-- A dense open subset of a noetherian quasi-sober `T0` space of dimension at most one has
finite complement: the points outside it have no proper generalization outside it, so they are
generic points of the finitely many irreducible components of the complement. -/
lemma finite_compl_of_dense_of_topologicalKrullDim_le_one {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] [QuasiSober X] [T0Space X]
    (hX : topologicalKrullDim X ≤ 1) {U : Set X} (hU : Dense U) (hUo : IsOpen U) :
    Uᶜ.Finite := by
  have hfin : (irreducibleComponents X).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  -- a point outside `U` has no proper specialization outside `U`
  have key (x w : X) (hx : x ∉ U) (hxw : x ⤳ w) : w = x := by
    by_contra hw
    obtain ⟨ξ, hξ, hξx⟩ := exists_mem_irreducibleComponents_specializes x
    have hξU : ξ ∈ U := mem_of_dense_of_closure_mem_irreducibleComponents
      hfin hU hUo hξ
    have hxξ : x ≠ ξ := fun h ↦ hx (h ▸ hξU)
    have := two_le_topologicalKrullDim_of_specializes hxw hξx hw hxξ
    have h2 := this.trans hX
    norm_num at h2
  let Z : Set X := Uᶜ
  have : QuasiSober Z := hUo.isClosed_compl.isClosedEmbedding_subtypeVal.quasiSober
  have hZfin : (irreducibleComponents Z).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hgen : (Set.univ : Set Z) ⊆ genericPoints Z := by
    intro z _
    obtain ⟨ζ, hζ, hζz⟩ := exists_mem_irreducibleComponents_specializes z
    have : z = ζ := by
      have h1 := key ζ.1 z.1 ζ.2 (hζz.map continuous_subtype_val)
      exact Subtype.ext h1
    rw [this]
    exact hζ
  have : (Set.univ : Set Z).Finite := (genericPoints.finite hZfin).subset hgen
  have hZ : Finite Z := Set.finite_univ_iff.mp this
  exact Set.toFinite Z

namespace AlgebraicGeometry

/-- **Finite coproducts of cartesian squares.** If the squares `Y'ₐ ⟶ Yₐ` over `X' ⟶ X` are
cartesian, so is the induced square `∐ Y'ₐ ⟶ ∐ Yₐ` over `X' ⟶ X` (schemes form an extensive
category). -/
lemma isPullback_sigmaDesc {ι : Type*} [Finite ι] {X X' : Scheme.{u}} {Y Y' : ι → Scheme.{u}}
    (g : ∀ a, Y a ⟶ X) (g' : ∀ a, Y' a ⟶ X') (h : ∀ a, Y' a ⟶ Y a) (b : X' ⟶ X)
    (H : ∀ a, IsPullback (h a) (g' a) (g a) b) :
    IsPullback (Limits.Sigma.map h) (Sigma.desc g') (Sigma.desc g) b := by
  let P := pullback (Sigma.desc g) b
  let l (a : ι) : Y' a ⟶ P :=
    pullback.lift (h a ≫ Sigma.ι Y a) (g' a) (by simp [(H a).w])
  have hl (a : ι) : IsPullback (l a) (h a) (pullback.fst (Sigma.desc g) b) (Sigma.ι Y a) := by
    refine IsPullback.of_right ?_ (by simp [l]) (IsPullback.of_hasPullback (Sigma.desc g) b).flip
    simpa [l] using (H a).flip
  have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)
  have hc : Nonempty (IsColimit (Cofan.mk P l)) := by
    apply hau (Cofan.mk P l) (Discrete.natTrans fun i ↦ h i.as) (pullback.fst _ _)
    · ext i
      simp [l]
    · exact NatTrans.Equifibered.of_discrete _
    · intro i
      exact hl i.as
  have hiso : IsIso (Sigma.desc l) := (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hc
  refine IsPullback.of_iso_pullback ⟨Sigma.hom_ext _ _ fun a ↦ by simp [(H a).w]⟩
    (asIso (Sigma.desc l)) (Sigma.hom_ext _ _ fun a ↦ by simp [l])
    (Sigma.hom_ext _ _ fun a ↦ by simp [l])

/-- **Restricting a cartesian square over an open.** If `ZL ⟶ Z` over `YL ⟶ Y` is cartesian
and `W ⊆ Y` is open, the restricted square over `W` is cartesian. -/
lemma IsPullback.exists_isPullback_morphismRestrict {Z Y ZL YL : Scheme.{u}} {a : ZL ⟶ Z}
    {γL : ZL ⟶ YL} {γ : Z ⟶ Y} {b : YL ⟶ Y} (H : IsPullback a γL γ b) (W : Y.Opens) :
    ∃ a' : (γL ⁻¹ᵁ (b ⁻¹ᵁ W)).toScheme ⟶ (γ ⁻¹ᵁ W).toScheme,
      a' ≫ (γ ⁻¹ᵁ W).ι = (γL ⁻¹ᵁ (b ⁻¹ᵁ W)).ι ≫ a ∧
      IsPullback a' (γL ∣_ (b ⁻¹ᵁ W)) (γ ∣_ W) (b ∣_ W) := by
  have hr : Set.range ((γL ⁻¹ᵁ (b ⁻¹ᵁ W)).ι ≫ a) ⊆ Set.range (γ ⁻¹ᵁ W).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change γ (a ((γL ⁻¹ᵁ (b ⁻¹ᵁ W)).ι x)) ∈ W
    rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
    exact x.2
  refine ⟨IsOpenImmersion.lift (γ ⁻¹ᵁ W).ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  refine IsPullback.of_right ?_ ?_ (isPullback_morphismRestrict γ W).flip
  · rw [IsOpenImmersion.lift_fac, morphismRestrict_ι]
    exact (isPullback_morphismRestrict γL (b ⁻¹ᵁ W)).flip.paste_horiz H
  · rw [← cancel_mono W.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.lift_fac_assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
      Category.assoc, H.w]

/-- **Base change along an open immersion is restriction.** For a property `P` respecting
isomorphisms and an open immersion `j`, `P` holds for the base change of `g` along `j` if and
only if it holds for the restriction of `g` over the image of `j`. -/
lemma pullback_snd_iff_morphismRestrict (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y V : Scheme.{u}} (g : X ⟶ Y) (j : V ⟶ Y) [IsOpenImmersion j] :
    P (pullback.snd g j) ↔ P (g ∣_ j.opensRange) := by
  let e : V ≅ j.opensRange.toScheme :=
    IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by simp)
  have he : e.hom ≫ j.opensRange.ι = j := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have H : IsPullback (g ⁻¹ᵁ j.opensRange).ι (g ∣_ j.opensRange ≫ e.inv) g j := by
    refine IsPullback.of_iso (isPullback_morphismRestrict g j.opensRange).flip (Iso.refl _)
      (Iso.refl _) e.symm (Iso.refl _) (by simp) (by simp) (by simp) ?_
    simp [← he]
  let i := (IsPullback.of_hasPullback g j).isoIsPullback _ _ H
  have hi : i.hom ≫ g ∣_ j.opensRange ≫ e.inv = pullback.snd g j :=
    by simp [i]
  rw [← hi, MorphismProperty.cancel_left_of_respectsIso P,
    MorphismProperty.cancel_right_of_respectsIso P]

/-- If `ξ ⤳ η` where `η` is the generic point of an irreducible scheme, then `ξ = η`. -/
lemma eq_genericPoint_of_specializes {S : Scheme.{u}} [IrreducibleSpace S] {ξ : S}
    (h : ξ ⤳ genericPoint S) : ξ = genericPoint S := by
  have hg : IsGenericPoint ξ Set.univ := by
    rw [isGenericPoint_iff_specializes]
    exact fun x ↦ iff_of_true (h.trans ((genericPoint_spec S).specializes (Set.mem_univ x)))
      trivial
  exact hg.eq (genericPoint_spec S)

/-- **Removing the closed image of an open set missing the generic fibre.** Let `g : Z ⟶ S`
be universally closed, with `Z` noetherian and `S` irreducible, and let `O ⊆ Z` be an open set
containing no point over the generic point of `S`. Then some open neighbourhood `V` of the
generic point contains no image of a point of `O`. (Every point of the closure of `O` is a
specialization of a point of `O`.) -/
lemma exists_genericPoint_mem_forall_notMem {Z S : Scheme.{u}} (g : Z ⟶ S)
    [UniversallyClosed g] [TopologicalSpace.NoetherianSpace Z] [IrreducibleSpace S]
    {O : Set Z} (hO : IsOpen O) (h : ∀ z ∈ O, g z ≠ genericPoint S) :
    ∃ V : S.Opens, genericPoint S ∈ V ∧ ∀ z ∈ O, g z ∉ V := by
  let C := closure O
  refine ⟨⟨(g '' C)ᶜ, (g.isClosedMap _ isClosed_closure).isOpen_compl⟩, ?_,
    fun z hz hzV ↦ hzV ⟨z, subset_closure hz, rfl⟩⟩
  rintro ⟨z, hzC, hz⟩
  have : QuasiSober C := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨y, hy, hyz⟩ := exists_mem_irreducibleComponents_specializes (⟨z, hzC⟩ : C)
  have hfin : (irreducibleComponents C).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have hdense : Dense (Subtype.val ⁻¹' O : Set C) := by
    rw [Subtype.dense_iff]
    intro x hx
    refine closure_mono ?_ hx
    intro w hw
    exact ⟨⟨w, subset_closure hw⟩, hw, rfl⟩
  have hyO : y.1 ∈ O :=
    mem_of_dense_of_closure_mem_irreducibleComponents hfin hdense
      (hO.preimage continuous_subtype_val) hy
  have hsp : g y.1 ⤳ genericPoint S := by
    rw [← hz]
    exact (hyz.map continuous_subtype_val).map g.continuous
  exact h _ hyO (eq_genericPoint_of_specializes hsp)

/-- **The relative dimension of a smooth morphism is read off on the generic fibre.** Let
`g : Y ⟶ S` be smooth with `S` irreducible, and `j : Spec L ⟶ S` a morphism from the spectrum
of a field hitting the generic point. If the base change of `g` along `j` is smooth of relative
dimension `d`, so is `g`: every point of `Y` generalizes to a point over the generic point
(flatness), and the local relative dimension is constant on the smooth charts. -/
theorem smoothOfRelativeDimension_of_pullback_snd {Y S : Scheme.{u}} [IrreducibleSpace S]
    (g : Y ⟶ S) [Smooth g] {L : Type u} [Field L] (j : Spec (.of L) ⟶ S)
    (hj : ∀ x, j x = genericPoint S) (d : ℕ)
    [SmoothOfRelativeDimension d (pullback.snd g j)] : SmoothOfRelativeDimension d g := by
  refine smoothOfRelativeDimension_of_forall_exists_mem g d fun y ↦ ?_
  obtain ⟨U, V, -, -, hy, e, d', hd'⟩ := Smooth.exists_smoothOfRelativeDimension_resLE g y
  have hV : SmoothOfRelativeDimension d' (V.ι ≫ g) := by
    rw [← Scheme.Hom.resLE_comp_ι g e]
    exact smoothOfRelativeDimension_comp (n := d') (m := 0) _ _
  refine ⟨V, hy, ?_⟩
  suffices d' = d by
    subst this
    exact hV
  -- a generalization of `y` over the generic point
  obtain ⟨y', hy'y, hy'⟩ := (Flat.generalizingMap g) (genericPoint_specializes (g y))
  have hy'V : y' ∈ V := hy'y.mem_open V.isOpen hy
  obtain ⟨p⟩ : Nonempty (Spec (.of L)) := inferInstance
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := j) y' p
    (by rw [hy', hj])
  let Q := pullback V.ι (pullback.fst g j)
  have : Nonempty Q := by
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.ι)
      (g := pullback.fst g j) ⟨y', hy'V⟩ z (by rw [hz]; rfl)
    exact ⟨w⟩
  let q : Q ⟶ Spec (.of L) := pullback.snd V.ι (pullback.fst g j) ≫ pullback.snd g j
  have h₁ : SmoothOfRelativeDimension d q := by
    have : SmoothOfRelativeDimension (0 + d) q := smoothOfRelativeDimension_comp 0 d _ _
    rwa [zero_add] at this
  have h₂ : SmoothOfRelativeDimension d' q := by
    have hq : (pullbackRightPullbackFstIso g j V.ι).hom ≫ pullback.snd (V.ι ≫ g) j = q :=
      pullbackRightPullbackFstIso_hom_snd _ _ _
    rw [← hq]
    have := smoothOfRelativeDimension_isStableUnderBaseChange (n := d')
    have : SmoothOfRelativeDimension d' (pullback.snd (V.ι ≫ g) j) :=
      MorphismProperty.pullback_snd _ _ hV
    have : SmoothOfRelativeDimension (0 + d') ((pullbackRightPullbackFstIso g j V.ι).hom ≫
      pullback.snd (V.ι ≫ g) j) := smoothOfRelativeDimension_comp 0 d' _ _
    rwa [zero_add] at this
  exact SmoothOfRelativeDimension.eq_of_field q h₂ h₁

/-- Equal morphisms have the same properties after restriction to an open. -/
lemma morphismProperty_restrict_congr (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}}
    {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) : P (f ∣_ U) ↔ P (g ∣_ U) := by
  subst h
  rfl

/-- **Morphisms from reduced schemes factor through the reduction.** -/
lemma exists_comp_nilradical_subschemeι {W X : Scheme.{u}} (g : W ⟶ X) [IsReduced W] :
    ∃ l : W ⟶ X.nilradical.subscheme, l ≫ X.nilradical.subschemeι = g := by
  have h : X.nilradical ≤ g.ker := by
    rw [Scheme.IdealSheafData.le_ker_iff_range_subset_support]
    simp [Scheme.support_nilradical]
  exact ⟨g.toImage ≫ Scheme.IdealSheafData.inclusion h, by simp⟩

end AlgebraicGeometry
