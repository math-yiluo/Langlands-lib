/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Density
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!

# The two formal reductions in the proof of Conrad's Theorem 2.4

The proof of Conrad's Theorem 2.4
(`AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection` in
`WeilConjectures.Blowup.PartialSectionExtension`) ends with two purely formal steps, which
bring the general case back to the case of a quasi-affine target. This file isolates them;
neither uses any of Conrad's mathematics.

* `AlgebraicGeometry.exists_isAdmissible_extend_partialSection_of_blowup`
  (blueprint: `lemma:nagata-conrad-blowup-base-change-reduction`): one may base change the
  whole situation along a `V`-admissible blow-up `q : X' ⟶ X` without leaving the statement
  of the theorem. The blow-up produced downstairs is the composite blow-up supplied by
  `AlgebraicGeometry.IsAdmissible.exists_comp` (Stacks Project Tag 080L);
* `AlgebraicGeometry.exists_isAdmissible_extend_partialSection_of_isClosedImmersion`
  (blueprint: `lemma:nagata-conrad-closed-target-reduction`): one may replace the target `Y`
  by a closed subscheme through which the section factors, e.g. by the scheme-theoretic
  image of `U`.

The base-changed section itself is `AlgebraicGeometry.baseChangeSection`, and the
hypotheses of the theorem are transported along the base change by the lemmas in the
`AlgebraicGeometry.IsAdmissible` namespace at the end of the file. Density is *not*
reproved here: it is `AlgebraicGeometry.IsAdmissible.dense_coe_preimage_blowupMap`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {U V : X.Opens} {p : Y ⟶ X}

/-! ### Range bookkeeping

Three small helpers about ranges of morphisms of schemes, kept private to this file. -/

private lemma range_isIso_comp {A B C : Scheme.{u}} (e : A ⟶ B) [IsIso e] (g : B ⟶ C) :
    Set.range (e ≫ g) = Set.range g := by
  have hsurj : Set.range (e : A → B) = Set.univ :=
    (Scheme.homeoOfIso (asIso e)).surjective.range_eq
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hsurj, Set.image_univ]

private lemma isClosed_range_of_comp_isIso {A B C : Scheme.{u}} (a : A ⟶ B) (e : B ⟶ C)
    [IsIso e] (h : IsClosed (Set.range (a ≫ e))) : IsClosed (Set.range a) := by
  have ha : a = (a ≫ e) ≫ inv e := by simp
  rw [ha, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  exact (inv e).isClosedEmbedding.isClosedMap _ h

/-- The range of the top of a cartesian square of schemes is the preimage of the range of
its bottom. -/
private lemma _root_.CategoryTheory.IsPullback.range_fst {P A B S : Scheme.{u}} {fst : P ⟶ A}
    {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S} (h : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  rw [← h.isoPullback_hom_fst, range_isIso_comp, Scheme.Pullback.range_fst]

/-! ### The base-changed section -/

/-- The base change of a section `f` of `p : Y ⟶ X` over an open `U` along a `V`-admissible
blow-up `π` of `X`: a section of the projection `pullback.fst π p` over the open
`π⁻¹(U)`. -/
def baseChangeSection (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι) (B₁ : IsAdmissible X V) :
    (B₁.I.blowupMap ⁻¹ᵁ U).toScheme ⟶ pullback B₁.I.blowupMap p :=
  pullback.lift (B₁.I.blowupMap ⁻¹ᵁ U).ι ((B₁.I.blowupMap ∣_ U) ≫ f) (by
    rw [Category.assoc, hf, morphismRestrict_ι])

/-- `AlgebraicGeometry.baseChangeSection` is a section of the base-changed morphism. -/
@[reassoc (attr := simp)]
lemma baseChangeSection_comp_fst (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (B₁ : IsAdmissible X V) :
    baseChangeSection f hf B₁ ≫ pullback.fst B₁.I.blowupMap p = (B₁.I.blowupMap ⁻¹ᵁ U).ι :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeSection_comp_snd (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (B₁ : IsAdmissible X V) :
    baseChangeSection f hf B₁ ≫ pullback.snd B₁.I.blowupMap p = (B₁.I.blowupMap ∣_ U) ≫ f :=
  pullback.lift_snd _ _ _

/-- The base-changed section sits in a cartesian square over the original one. -/
lemma isPullback_baseChangeSection (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (B₁ : IsAdmissible X V) :
    IsPullback (baseChangeSection f hf B₁) (B₁.I.blowupMap ∣_ U)
      (pullback.snd B₁.I.blowupMap p) f := by
  refine IsPullback.of_right ?_ (baseChangeSection_comp_snd f hf B₁)
    (IsPullback.of_hasPullback B₁.I.blowupMap p)
  rw [baseChangeSection_comp_fst, hf]
  exact (isPullback_morphismRestrict B₁.I.blowupMap U).flip

/-! ### Transporting the conclusion along an isomorphism of blow-ups -/

/-- The conclusion of Conrad's Theorem 2.4 only depends on the total space of the blow-up up
to isomorphism over `X`. -/
lemma exists_extend_partialSection_of_iso {X' X'' : Scheme.{u}} {f : U.toScheme ⟶ Y}
    {π' : X' ⟶ X} {π'' : X'' ⟶ X} (ε : X' ≅ X'') (hε : ε.hom ≫ π'' = π')
    (H : ∃ (W : X''.Opens) (hUW : π'' ⁻¹ᵁ U ≤ W) (g : W.toScheme ⟶ Y)
           (hg : g ≫ p = W.ι ≫ π''),
           X''.homOfLE hUW ≫ g = (π'' ∣_ U) ≫ f ∧
             IsClosed (Set.range (pullback.lift g W.ι hg))) :
    ∃ (W : X'.Opens) (hUW : π' ⁻¹ᵁ U ≤ W) (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ π'),
      X'.homOfLE hUW ≫ g = (π' ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  subst hε
  obtain ⟨W, hUW, g, hg, hext, hcl⟩ := H
  have hle : ε.hom ⁻¹ᵁ π'' ⁻¹ᵁ U ≤ ε.hom ⁻¹ᵁ W := fun x hx ↦ hUW hx
  have hg' : ((ε.hom ∣_ W) ≫ g) ≫ p = (ε.hom ⁻¹ᵁ W).ι ≫ ε.hom ≫ π'' := by
    rw [Category.assoc, hg, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  refine ⟨ε.hom ⁻¹ᵁ W, hle, (ε.hom ∣_ W) ≫ g, hg', ?_, ?_⟩
  · have hnat : X'.homOfLE hle ≫ (ε.hom ∣_ W) = (ε.hom ∣_ π'' ⁻¹ᵁ U) ≫ X''.homOfLE hUW := by
      rw [← cancel_mono W.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
        Scheme.homOfLE_ι, ← Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
    rw [← Category.assoc, hnat, Category.assoc, hext, ← Category.assoc,
      ← morphismRestrict_comp]
  · -- the two graphs differ by the base change isomorphism along `ε`
    set c : (pullback p (ε.hom ≫ π'') : Scheme.{u}) ⟶ pullback p π'' :=
      pullback.map p (ε.hom ≫ π'') p π'' (𝟙 Y) ε.hom (𝟙 X) (by simp) (by simp) with hc
    have hciso : IsIso c := by
      rw [hc]
      infer_instance
    have hcomp : pullback.lift ((ε.hom ∣_ W) ≫ g) (ε.hom ⁻¹ᵁ W).ι hg' ≫ c
        = (ε.hom ∣_ W) ≫ pullback.lift g W.ι hg := by
      refine pullback.hom_ext ?_ ?_ <;>
        simp [hc, Category.assoc, morphismRestrict_ι]
    refine isClosed_range_of_comp_isIso _ c ?_
    rw [hcomp, range_isIso_comp]
    exact hcl

/-! ### Reduction along an admissible blow-up of the base -/

/-- **Base change along an admissible blow-up** (blueprint:
`lemma:nagata-conrad-blowup-base-change-reduction`). If the conclusion of Conrad's Theorem
2.4 holds for the data base changed along a `V`-admissible blow-up `π` of `X` — that is, for
the projection `pullback.fst π p` and the section `AlgebraicGeometry.baseChangeSection` — then
it holds for the original data.

The blow-up produced is the composite blow-up of
`AlgebraicGeometry.IsAdmissible.exists_comp` (Stacks Project Tag 080L). -/
theorem exists_isAdmissible_extend_partialSection_of_blowup
    [CompactSpace X] [QuasiSeparatedSpace X] (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (B₁ : IsAdmissible X V)
    (H : ∃ (B₂ : IsAdmissible B₁.I.blowup (B₁.I.blowupMap ⁻¹ᵁ V))
           (W : B₂.I.blowup.Opens)
           (hUW : B₂.I.blowupMap ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ U) ≤ W)
           (g : W.toScheme ⟶ pullback B₁.I.blowupMap p)
           (hg : g ≫ pullback.fst B₁.I.blowupMap p = W.ι ≫ B₂.I.blowupMap),
           B₂.I.blowup.homOfLE hUW ≫ g
               = (B₂.I.blowupMap ∣_ (B₁.I.blowupMap ⁻¹ᵁ U)) ≫ baseChangeSection f hf B₁ ∧
             IsClosed (Set.range (pullback.lift g W.ι hg))) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  obtain ⟨B₂, W, hUW, g, hg, hext, hcl⟩ := H
  obtain ⟨K, hKft, hdisj, iso, hiso⟩ := B₁.exists_comp B₂
  -- the conclusion for the composite blow-up `B₂.I.blowupMap ≫ B₁.I.blowupMap`
  have Hcomp : ∃ (W' : B₂.I.blowup.Opens)
      (hUW' : (B₂.I.blowupMap ≫ B₁.I.blowupMap) ⁻¹ᵁ U ≤ W') (g' : W'.toScheme ⟶ Y)
      (hg' : g' ≫ p = W'.ι ≫ (B₂.I.blowupMap ≫ B₁.I.blowupMap)),
      B₂.I.blowup.homOfLE hUW' ≫ g' = ((B₂.I.blowupMap ≫ B₁.I.blowupMap) ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g' W'.ι hg')) := by
    have hg' : (g ≫ pullback.snd B₁.I.blowupMap p) ≫ p
        = W.ι ≫ (B₂.I.blowupMap ≫ B₁.I.blowupMap) := by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hg, Category.assoc]
    refine ⟨W, hUW, g ≫ pullback.snd B₁.I.blowupMap p, hg', ?_, ?_⟩
    · rw [← Category.assoc, hext, Category.assoc, baseChangeSection_comp_snd,
        morphismRestrict_comp, Category.assoc]
    · -- the pasting square identifying `Y ×_X X''` with `(Y ×_X X') ×_{X'} X''`
      have hw : (pullback.snd p (B₂.I.blowupMap ≫ B₁.I.blowupMap) ≫ B₂.I.blowupMap)
            ≫ B₁.I.blowupMap
          = pullback.fst p (B₂.I.blowupMap ≫ B₁.I.blowupMap) ≫ p := by
        rw [Category.assoc, ← pullback.condition]
      set t : (pullback p (B₂.I.blowupMap ≫ B₁.I.blowupMap) : Scheme.{u})
            ⟶ pullback B₁.I.blowupMap p :=
        pullback.lift (pullback.snd p (B₂.I.blowupMap ≫ B₁.I.blowupMap) ≫ B₂.I.blowupMap)
          (pullback.fst p (B₂.I.blowupMap ≫ B₁.I.blowupMap)) hw with ht
      have hsq : IsPullback t (pullback.snd p (B₂.I.blowupMap ≫ B₁.I.blowupMap))
          (pullback.fst B₁.I.blowupMap p) B₂.I.blowupMap := by
        refine IsPullback.of_right ?_ (by rw [ht, pullback.lift_fst])
          (IsPullback.of_hasPullback B₁.I.blowupMap p).flip
        have h1 : t ≫ pullback.snd B₁.I.blowupMap p
            = pullback.fst p (B₂.I.blowupMap ≫ B₁.I.blowupMap) := by
          rw [ht, pullback.lift_snd]
        rw [h1]
        exact IsPullback.of_hasPullback p (B₂.I.blowupMap ≫ B₁.I.blowupMap)
      have hlift : pullback.lift (g ≫ pullback.snd B₁.I.blowupMap p) W.ι hg'
            ≫ hsq.isoPullback.hom
          = pullback.lift g W.ι hg := by
        refine pullback.hom_ext ?_ ?_
        · rw [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst]
          refine pullback.hom_ext ?_ ?_
          · rw [Category.assoc, ht, pullback.lift_fst, ← Category.assoc, pullback.lift_snd, hg]
          · rw [Category.assoc, ht, pullback.lift_snd, pullback.lift_fst]
        · rw [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd,
            pullback.lift_snd]
      refine isClosed_range_of_comp_isIso _ hsq.isoPullback.hom ?_
      rw [hlift]
      exact hcl
  refine ⟨⟨K, hKft, hdisj⟩, ?_⟩
  exact exists_extend_partialSection_of_iso iso.symm (by
    rw [Iso.symm_hom, ← hiso, Iso.inv_hom_id_assoc]) Hcomp

/-! ### Reduction to a closed subscheme of the target -/

/-- **Reduction to a closed subscheme of the target** (blueprint:
`lemma:nagata-conrad-closed-target-reduction`). A quasi-domination extending `f` into a
closed subscheme `Y'` of `Y` is one into `Y`: the graph of the former is the preimage of the
graph of the latter under the closed immersion `Y' ↪ Y`. -/
theorem exists_isAdmissible_extend_partialSection_of_isClosedImmersion {Y' : Scheme.{u}}
    {p' : Y' ⟶ X} (i : Y' ⟶ Y) [IsClosedImmersion i] (hi : i ≫ p = p') (f' : U.toScheme ⟶ Y')
    (H : ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
           (g : W.toScheme ⟶ Y') (hg : g ≫ p' = W.ι ≫ B.I.blowupMap),
           B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f' ∧
             IsClosed (Set.range (pullback.lift g W.ι hg))) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ (f' ≫ i) ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  subst hi
  obtain ⟨B, W, hUW, g, hg, hext, hcl⟩ := H
  set π := B.I.blowupMap with hπ
  have hg' : (g ≫ i) ≫ p = W.ι ≫ π := by rw [Category.assoc, hg]
  refine ⟨B, W, hUW, g ≫ i, hg', ?_, ?_⟩
  · rw [← Category.assoc, hext, Category.assoc]
  · -- the comparison morphism of graphs is a base change of `i`, hence a closed immersion
    set c : (pullback (i ≫ p) π : Scheme.{u}) ⟶ pullback p π :=
      pullback.map (i ≫ p) π p π i (𝟙 _) (𝟙 _) (by simp) (by simp) with hc
    have : IsClosedImmersion c := by
      rw [hc]
      exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
        (isPullback_pullback_map_left i p π) inferInstance
    have hcomp : pullback.lift (g ≫ i) W.ι hg' = pullback.lift g W.ι hg ≫ c := by
      refine pullback.hom_ext ?_ ?_
      · rw [pullback.lift_fst, Category.assoc, hc, pullback.lift_fst, ← Category.assoc,
          pullback.lift_fst]
      · rw [pullback.lift_snd, Category.assoc, hc, pullback.lift_snd, ← Category.assoc,
          pullback.lift_snd, Category.comp_id]
    rw [hcomp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    exact c.isClosedEmbedding.isClosedMap _ hcl

/-! ### Transporting the hypotheses along the base change -/

namespace IsAdmissible

variable (B₁ : IsAdmissible X V)

lemma preimage_blowupMap_mono {W₁ W₂ : X.Opens} (h : W₁ ≤ W₂) :
    B₁.I.blowupMap ⁻¹ᵁ W₁ ≤ B₁.I.blowupMap ⁻¹ᵁ W₂ :=
  fun _ hx ↦ h hx

lemma quasiCompact_blowupMap : QuasiCompact B₁.I.blowupMap :=
  Scheme.IdealSheafData.quasiCompact_blowupMap B₁.finiteType

lemma isCompact_coe_preimage_blowupMap {W : X.Opens} (hW : IsCompact (W : Set X)) :
    IsCompact ((B₁.I.blowupMap ⁻¹ᵁ W : B₁.I.blowup.Opens) : Set B₁.I.blowup) :=
  have := B₁.quasiCompact_blowupMap
  B₁.I.blowupMap.isCompact_preimage hW

lemma compactSpace_pullback_blowupMap [CompactSpace Y] :
    CompactSpace (pullback B₁.I.blowupMap p : Scheme.{u}) :=
  have := B₁.quasiCompact_blowupMap
  inferInstance

lemma isSeparated_pullback_snd_blowupMap : IsSeparated (pullback.snd B₁.I.blowupMap p) :=
  have : IsSeparated B₁.I.blowupMap := B₁.isProper_blowupMap.toIsSeparated
  MorphismProperty.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback B₁.I.blowupMap p) inferInstance

lemma quasiSeparatedSpace_pullback_blowupMap [QuasiSeparatedSpace Y] :
    QuasiSeparatedSpace (pullback B₁.I.blowupMap p : Scheme.{u}) := by
  have := B₁.isSeparated_pullback_snd_blowupMap (p := p)
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd B₁.I.blowupMap p)

lemma isSeparated_pullback_fst_blowupMap [IsSeparated p] :
    IsSeparated (pullback.fst B₁.I.blowupMap p) :=
  MorphismProperty.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback B₁.I.blowupMap p).flip inferInstance

lemma locallyOfFiniteType_pullback_fst_blowupMap [LocallyOfFiniteType p] :
    LocallyOfFiniteType (pullback.fst B₁.I.blowupMap p) :=
  MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (IsPullback.of_hasPullback B₁.I.blowupMap p).flip inferInstance

lemma quasiCompact_pullback_fst_blowupMap [QuasiCompact p] :
    QuasiCompact (pullback.fst B₁.I.blowupMap p) :=
  MorphismProperty.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback B₁.I.blowupMap p).flip inferInstance


/-- The closed-image hypothesis of Conrad's Theorem 2.4 transports to the base-changed
section: the range of `AlgebraicGeometry.baseChangeSection` is closed in the preimage of
`π⁻¹(V)`. -/
lemma isClosed_preimage_range_baseChangeSection (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    IsClosed ((pullback.fst B₁.I.blowupMap p ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ V)).ι ⁻¹'
      Set.range (baseChangeSection f hf B₁)) := by
  set π := B₁.I.blowupMap with hπ
  set O : (pullback π p : Scheme.{u}).Opens := pullback.fst π p ⁻¹ᵁ (π ⁻¹ᵁ V) with hO
  -- the range of the base-changed section is the preimage of the range of `f`
  have hrange : Set.range (baseChangeSection f hf B₁) = pullback.snd π p ⁻¹' Set.range f :=
    (isPullback_baseChangeSection f hf B₁).range_fst
  -- `O` is also the preimage of `p⁻¹(V)` along the second projection
  have hle : O ≤ pullback.snd π p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    rw [hO, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  set q := (pullback.snd π p).resLE (p ⁻¹ᵁ V) O hle with hq
  have hqι : q ≫ (p ⁻¹ᵁ V).ι = O.ι ≫ pullback.snd π p := Scheme.Hom.resLE_comp_ι _ _
  have heq : O.ι ⁻¹' Set.range (baseChangeSection f hf B₁)
      = q ⁻¹' ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f) := by
    rw [hrange, ← Set.preimage_comp, ← Set.preimage_comp, ← TopCat.coe_comp, ← TopCat.coe_comp,
      ← Scheme.Hom.comp_base, ← Scheme.Hom.comp_base, hqι]
  rw [heq]
  exact hfc.preimage q.continuous

end IsAdmissible

end AlgebraicGeometry
