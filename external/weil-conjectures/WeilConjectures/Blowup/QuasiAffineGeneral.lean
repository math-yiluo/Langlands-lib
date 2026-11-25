/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.EliminationOfIndeterminacy
public import WeilConjectures.Blowup.QuasiAffineGeneralReduction
public import WeilConjectures.Mathlib.Topology.Constructions

/-!

# Conrad's Theorem 2.4, Case 3: a quasi-affine target and two nested opens

This file proves Case 3 of Theorem 2.4 in Conrad's *Deligne's notes on Nagata compactifications*
(blueprint: `lemma:nagata-conrad-quasi-affine-general`): the elimination of indeterminacy for a
quasi-affine morphism `p : Y ⟶ X` over a qcqs base, for an arbitrary pair `U ≤ V` of
quasi-compact opens of `X`, with the resulting blow-up centre disjoint from the *larger* open
`V`.

## Main results

- `AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffineHom_of_le`.

## Proof sketch

The two opening reductions are cited from `WeilConjectures.Blowup.QuasiAffineGeneralReduction`
and `WeilConjectures.Mathlib.AlgebraicGeometry.Properties`:

1. `AlgebraicGeometry.exists_isAdmissible_disjoint_closure_range_of_le` produces a
   `V`-admissible blow-up `π₁ : X₁ ⟶ X` after which the closure of the image of the base change
   of `f` no longer meets the part lying over `closure (V ∖ U)`;
2. `AlgebraicGeometry.exists_isCompact_opens_inf_eq_of_disjoint_closure_sdiff` then produces a
   quasi-compact open `X₀` of `X₁` containing that closure's image and meeting `π₁ ⁻¹ V`
   exactly in `π₁ ⁻¹ U`.

Over the smaller base `X₀` the two opens coincide, so Case 2
(`AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffineHom`) applies to the base change
`p₁ ⁻¹ᵁ X₀ ⟶ X₀` of `p`. Its quasi-affineness is `AlgebraicGeometry.IsQuasiAffineHom.of_isPullback`
followed by restriction to the open `X₀` of the base; **no scheme-theoretic image is needed**,
because the closedness of the graph is a purely topological consequence of the closed set
`closure (Set.range f₁)` lying inside `p₁ ⁻¹ X₀`.

The centre found over `X₀` is extended to `X₁` by `IsAdmissible.exists_extend_of_disjoint`
(Stacks Tag 080M), whose hypothesis is that the support of that centre avoids the overlap
`X₀ ⊓ π₁ ⁻¹ V`; the centre is admissible over `X₀ ⊓ π₁ ⁻¹ U`, so it is step 2's equality
`X₀ ⊓ π₁ ⁻¹ V = π₁ ⁻¹ U` that discharges it. The two admissible blow-ups are composed by
`IsAdmissible.exists_comp` (Stacks Tag 080L). Transporting the local extension from the
blow-up of `X₀` to the blow-up of `X₁` is Case 2's own
`AlgebraicGeometry.exists_extend_of_lift`, used here with the open `X₀` of `X₁` in the role of
its affine open.

Density of `U` in `X` is **not** assumed: what the closedness argument needs is that the inverse
image of `U` is topologically dense in the blow-up of `X₀`, and that is the scheme-theoretic
dominance which Case 2 hands back as its third conclusion.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Conrad's Theorem 2.4, Case 3**: elimination of indeterminacy for a quasi-affine
morphism and two nested quasi-compact opens (blueprint:
`lemma:nagata-conrad-quasi-affine-general`).

The centre of the blow-up is disjoint from the *larger* open `V`; that is what makes this
statement stronger than
`AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffineHom`, which is the case
`U = V`. Neither `U` nor `V` is assumed dense in `X`. -/
theorem exists_isAdmissible_extend_of_isQuasiAffineHom_of_le
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p] [IsQuasiAffineHom p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  classical
  have : QuasiCompact p := quasiCompact_of_compactSpace p
  -- Step 1: the disjointness blow-up
  obtain ⟨B₁, hB₁⟩ := exists_isAdmissible_disjoint_closure_range_of_le hUV hU hV f hf hfc
  set X₁ : Scheme.{u} := B₁.I.blowup with hX₁
  set π₁ : X₁ ⟶ X := B₁.I.blowupMap with hπ₁
  have : IsProper π₁ := B₁.isProper_blowupMap
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace π₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated π₁
  -- the base change of `p` along the blow-up
  obtain ⟨Y₁, r, p₁, hpb₁⟩ :
      ∃ (Y₁ : Scheme.{u}) (r : Y₁ ⟶ Y) (p₁ : Y₁ ⟶ X₁), IsPullback r p₁ p π₁ :=
    ⟨_, _, _, IsPullback.of_hasPullback p π₁⟩
  have : IsSeparated p₁ := MorphismProperty.of_isPullback hpb₁ ‹IsSeparated p›
  have : LocallyOfFiniteType p₁ := MorphismProperty.of_isPullback hpb₁ ‹LocallyOfFiniteType p›
  have : QuasiCompact p₁ := MorphismProperty.of_isPullback hpb₁ ‹QuasiCompact p›
  have : IsQuasiAffineHom p₁ := .of_isPullback hpb₁
  have : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace p₁
  have : QuasiSeparatedSpace Y₁ := quasiSeparatedSpace_of_quasiSeparated p₁
  -- the section over the preimage of `U`
  have hfcond : ((π₁ ∣_ U) ≫ f) ≫ p = (π₁ ⁻¹ᵁ U).ι ≫ π₁ := by
    rw [Category.assoc, hf, morphismRestrict_ι]
  set f₁ : (π₁ ⁻¹ᵁ U).toScheme ⟶ Y₁ := hpb₁.lift ((π₁ ∣_ U) ≫ f) (π₁ ⁻¹ᵁ U).ι hfcond with hf₁
  have hf₁r : f₁ ≫ r = (π₁ ∣_ U) ≫ f := hpb₁.lift_fst _ _ _
  have hf₁p : f₁ ≫ p₁ = (π₁ ⁻¹ᵁ U).ι := hpb₁.lift_snd _ _ _
  have hU₁c : IsCompact ((π₁ ⁻¹ᵁ U : X₁.Opens) : Set X₁) := π₁.isCompact_preimage hU
  have hV₁c : IsCompact ((π₁ ⁻¹ᵁ V : X₁.Opens) : Set X₁) := π₁.isCompact_preimage hV
  have : CompactSpace (π₁ ⁻¹ᵁ U).toScheme := isCompact_iff_compactSpace.mp hU₁c
  have : QuasiCompact f₁ := quasiCompact_of_compactSpace f₁
  have hdisj := hB₁ hpb₁.w hf₁r
  -- Step 2: a quasi-compact open of the blow-up meeting the preimage of `V` in that of `U`
  have hScpt : IsCompact (p₁ '' closure (Set.range f₁)) :=
    (isClosed_closure.isCompact).image p₁.continuous
  have hSdisj : Disjoint (p₁ '' closure (Set.range f₁))
      (closure (((π₁ ⁻¹ᵁ V : X₁.Opens) : Set X₁) \ ((π₁ ⁻¹ᵁ U : X₁.Opens) : Set X₁))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨y, hy, rfl⟩ hmem
    exact Set.disjoint_left.mp hdisj hy hmem
  obtain ⟨X₀, hX₀c, hSX₀, hU₁X₀, hX₀V⟩ :=
    exists_isCompact_opens_inf_eq_of_disjoint_closure_sdiff
      (π₁.preimage_mono hUV) hU₁c hScpt hSdisj
  -- Step 3: Case 2 over the smaller base `X₀`
  have : CompactSpace X₀.toScheme := isCompact_iff_compactSpace.mp hX₀c
  have : QuasiSeparatedSpace X₀.toScheme := quasiSeparatedSpace_of_quasiSeparated X₀.ι
  have : QuasiCompact X₀.ι := quasiCompact_of_compactSpace X₀.ι
  set U₀ : X₀.toScheme.Opens := X₀.ι ⁻¹ᵁ (π₁ ⁻¹ᵁ U) with hU₀
  have hU₀c : IsCompact ((U₀ : X₀.toScheme.Opens) : Set X₀.toScheme) :=
    X₀.ι.isCompact_preimage hU₁c
  have hf₀cond : U₀.ι ≫ X₀.ι = ((X₀.ι ∣_ (π₁ ⁻¹ᵁ U)) ≫ f₁) ≫ p₁ := by
    rw [Category.assoc, hf₁p, morphismRestrict_ι]
  set f₀ : U₀.toScheme ⟶ (p₁ ⁻¹ᵁ X₀).toScheme :=
    (isPullback_morphismRestrict p₁ X₀).lift U₀.ι ((X₀.ι ∣_ (π₁ ⁻¹ᵁ U)) ≫ f₁) hf₀cond with hf₀
  have hf₀q : f₀ ≫ (p₁ ∣_ X₀) = U₀.ι := (isPullback_morphismRestrict p₁ X₀).lift_fst _ _ _
  have hf₀ι : f₀ ≫ (p₁ ⁻¹ᵁ X₀).ι = (X₀.ι ∣_ (π₁ ⁻¹ᵁ U)) ≫ f₁ :=
    (isPullback_morphismRestrict p₁ X₀).lift_snd _ _ _
  obtain ⟨C, W₀, hUW₀, g₀, hg₀, hagree₀, hclosed₀, hdom₀⟩ :=
    exists_isAdmissible_extend_of_isQuasiAffineHom hU₀c f₀ hf₀q
  -- Step 4: extend the centre from `X₀` to the blow-up `X₁`
  have hV₀ : X₀.ι ⁻¹ᵁ (π₁ ⁻¹ᵁ V) = U₀ := by
    refine le_antisymm (fun x hx ↦ ?_) (X₀.ι.preimage_mono (π₁.preimage_mono hUV))
    have h1 : X₀.ι x ∈ (X₀ : Set X₁) := by
      rw [← Scheme.Opens.range_ι]
      exact Set.mem_range_self x
    have h2 : X₀.ι x ∈ ((X₀ ⊓ (π₁ ⁻¹ᵁ V) : X₁.Opens) : Set X₁) := ⟨h1, hx⟩
    rw [hX₀V] at h2
    exact h2
  obtain ⟨D, hmap, hmapw, hpbD⟩ :=
    IsAdmissible.exists_extend_of_disjoint (X := X₁) (A := X₀) (B := π₁ ⁻¹ᵁ V) hX₀c hV₁c
      C.I C.finiteType (by rw [hV₀]; exact C.disjoint_support)
  set ρiso : (D.I.blowupMap ⁻¹ᵁ X₀).toScheme ≅ C.I.blowup :=
    (isPullback_morphismRestrict D.I.blowupMap X₀).isoIsPullback _ _ hpbD
    with hρisodef
  have hρ : ρiso.hom ≫ C.I.blowupMap = D.I.blowupMap ∣_ X₀ :=
    (isPullback_morphismRestrict D.I.blowupMap X₀).isoIsPullback_hom_fst _ _ hpbD
  obtain ⟨W', hW'X₀, G, hG, hUW', hagreeG, hclosedG⟩ :=
    exists_extend_of_lift (p := p₁) (π := D.I.blowupMap) (U := π₁ ⁻¹ᵁ U) (V := X₀) (f := f₁)
      (b := C.I.blowupMap) (ρ := ρiso.hom) hρ hUW₀ hg₀ hf₀ι hagree₀ hclosed₀
  -- Step 5: compose the two admissible blow-ups
  obtain ⟨K, hKft, hKdisj, iso, hiso⟩ := IsAdmissible.exists_comp B₁ D
  have hUW'' : D.I.blowupMap ⁻¹ᵁ (π₁ ⁻¹ᵁ U) ≤ W' :=
    le_trans (le_inf le_rfl (D.I.blowupMap.preimage_mono hU₁X₀)) hUW'
  have hKbm : iso.inv ≫ D.I.blowupMap ≫ π₁ = K.blowupMap := by
    rw [← hiso, ← Category.assoc, iso.inv_hom_id, Category.id_comp]
  have hUW : K.blowupMap ⁻¹ᵁ U ≤ iso.inv ⁻¹ᵁ W' := by
    rw [← hKbm]
    simp only [Scheme.Hom.comp_preimage]
    exact iso.inv.preimage_mono hUW''
  have hg : ((iso.inv ∣_ W') ≫ G ≫ r) ≫ p = (iso.inv ⁻¹ᵁ W').ι ≫ K.blowupMap := by
    simp only [Category.assoc]
    rw [hpb₁.w, ← Category.assoc G, hG]
    simp only [Category.assoc]
    rw [← Category.assoc (iso.inv ∣_ W'), morphismRestrict_ι]
    simp only [Category.assoc]
    rw [hKbm]
  refine ⟨⟨K, hKft, hKdisj⟩, iso.inv ⁻¹ᵁ W', hUW, (iso.inv ∣_ W') ≫ G ≫ r, hg, ?_, ?_⟩
  · -- the extension agrees with `f` over `U`
    have hmcond : (K.blowupMap ∣_ U) ≫ U.ι =
        ((K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) ≫ W'.ι ≫ D.I.blowupMap) ≫ π₁ := by
      rw [morphismRestrict_ι]
      simp only [Category.assoc]
      rw [← Category.assoc (iso.inv ∣_ W'), morphismRestrict_ι]
      simp only [Category.assoc]
      rw [hKbm, ← Category.assoc, Scheme.homOfLE_ι]
    have hm1 := (isPullback_morphismRestrict π₁ U).lift_fst (K.blowupMap ∣_ U)
      ((K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) ≫ W'.ι ≫ D.I.blowupMap) hmcond
    have hm2 := (isPullback_morphismRestrict π₁ U).lift_snd (K.blowupMap ∣_ U)
      ((K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) ≫ W'.ι ≫ D.I.blowupMap) hmcond
    have hagr := hagreeG (K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) _ hm2
    calc K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W') ≫ G ≫ r
        = ((K.blowup.homOfLE hUW ≫ (iso.inv ∣_ W')) ≫ G) ≫ r := by
          simp only [Category.assoc]
      _ = _ ≫ f := by rw [hagr, Category.assoc, hf₁r, ← Category.assoc, hm1]
  · -- the graph is closed
    have hGrange : Set.range G ⊆ closure (Set.range f₁) := by
      -- the preimage of `U` is scheme-theoretically, hence topologically, dense in the
      -- blow-up of `X₀`
      have : IsProper C.I.blowupMap := C.isProper_blowupMap
      have : CompactSpace C.I.blowup := QuasiCompact.compactSpace_of_compactSpace C.I.blowupMap
      have : QuasiSeparatedSpace C.I.blowup :=
        quasiSeparatedSpace_of_quasiSeparated C.I.blowupMap
      have : CompactSpace (C.I.blowupMap ⁻¹ᵁ U₀).toScheme :=
        isCompact_iff_compactSpace.mp (C.I.blowupMap.isCompact_preimage hU₀c)
      have : QuasiCompact (C.I.blowupMap ⁻¹ᵁ U₀).ι := quasiCompact_of_compactSpace _
      have := hdom₀
      have hdense₀ : Dense ((C.I.blowupMap ⁻¹ᵁ U₀ : C.I.blowup.Opens) : Set C.I.blowup) := by
        have hdr : DenseRange (C.I.blowupMap ⁻¹ᵁ U₀).ι := Scheme.Hom.denseRange _
        rwa [DenseRange, Scheme.Opens.range_ι] at hdr
      -- transport the density to `W'`
      have hj : (D.I.blowup.homOfLE hW'X₀ ≫ ρiso.hom) ≫ C.I.blowupMap ≫ X₀.ι =
          W'.ι ≫ D.I.blowupMap := by
        rw [Category.assoc, ← Category.assoc ρiso.hom, hρ, morphismRestrict_ι,
          ← Category.assoc, Scheme.homOfLE_ι]
      have hA : Dense (⇑(W'.ι ≫ D.I.blowupMap) ⁻¹' ((π₁ ⁻¹ᵁ U : X₁.Opens) : Set X₁)) := by
        have hd := hdense₀.preimage
          (D.I.blowup.homOfLE hW'X₀ ≫ ρiso.hom).isOpenEmbedding.isOpenMap
        have heq : ⇑(D.I.blowup.homOfLE hW'X₀ ≫ ρiso.hom) ⁻¹'
            ((C.I.blowupMap ⁻¹ᵁ U₀ : C.I.blowup.Opens) : Set C.I.blowup) =
            ⇑(W'.ι ≫ D.I.blowupMap) ⁻¹' ((π₁ ⁻¹ᵁ U : X₁.Opens) : Set X₁) := by
          rw [← hj]
          simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
          rfl
        rwa [heq] at hd
      -- `G` agrees with `f₁` on that dense set
      have hm'cond : (D.I.blowupMap ∣_ (π₁ ⁻¹ᵁ U)) ≫ (π₁ ⁻¹ᵁ U).ι =
          (D.I.blowup.homOfLE hUW'') ≫ W'.ι ≫ D.I.blowupMap := by
        rw [morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
      have hagr := hagreeG (D.I.blowup.homOfLE hUW'') (D.I.blowupMap ∣_ (π₁ ⁻¹ᵁ U)) hm'cond
      have hA' : ⇑(W'.ι ≫ D.I.blowupMap) ⁻¹' ((π₁ ⁻¹ᵁ U : X₁.Opens) : Set X₁) =
          Set.range ⇑(D.I.blowup.homOfLE hUW'') := by
        have h1 : Set.range ⇑(D.I.blowup.homOfLE hUW'') =
            (((D.I.blowup.homOfLE hUW'').opensRange) : Set W'.toScheme) := rfl
        rw [h1, Scheme.opensRange_homOfLE]
        simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
        rfl
      have hGA : ⇑G '' (⇑(W'.ι ≫ D.I.blowupMap) ⁻¹' ((π₁ ⁻¹ᵁ U : X₁.Opens) : Set X₁)) ⊆
          Set.range f₁ := by
        rw [hA', ← Set.range_comp]
        rintro _ ⟨w, rfl⟩
        refine ⟨(D.I.blowupMap ∣_ (π₁ ⁻¹ᵁ U)).base w, ?_⟩
        have := congrArg (fun m : (D.I.blowupMap ⁻¹ᵁ (π₁ ⁻¹ᵁ U)).toScheme ⟶ Y₁ => m.base w) hagr
        simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using this.symm
      rw [← Set.image_univ, ← hA.closure_eq]
      exact (image_closure_subset_closure_image G.continuous).trans (closure_mono hGA)
    -- the comparison of the two fibre products
    have hbig : IsPullback (pullback.fst p₁ D.I.blowupMap ≫ r)
        (pullback.snd p₁ D.I.blowupMap ≫ iso.hom) p K.blowupMap := by
      refine IsPullback.of_iso
        (((IsPullback.of_hasPullback p₁ D.I.blowupMap).flip.paste_vert hpb₁.flip).flip)
        (Iso.refl _) (Iso.refl _) iso (Iso.refl _) (by simp) (by simp) (by simp) ?_
      simpa using hiso.symm
    set Φ : pullback p₁ D.I.blowupMap ≅ pullback p K.blowupMap :=
      hbig.isoIsPullback _ _ (IsPullback.of_hasPullback p K.blowupMap) with hΦdef
    have hΦfst : Φ.hom ≫ pullback.fst p K.blowupMap = pullback.fst p₁ D.I.blowupMap ≫ r :=
      hbig.isoIsPullback_hom_fst _ _ _
    have hΦsnd : Φ.hom ≫ pullback.snd p K.blowupMap =
        pullback.snd p₁ D.I.blowupMap ≫ iso.hom := hbig.isoIsPullback_hom_snd _ _ _
    have hΓ : pullback.lift ((iso.inv ∣_ W') ≫ G ≫ r) (iso.inv ⁻¹ᵁ W').ι hg =
        (iso.inv ∣_ W') ≫ pullback.lift G W'.ι hG ≫ Φ.hom := by
      refine pullback.hom_ext ?_ ?_
      · simp only [pullback.lift_fst, Category.assoc, hΦfst]
        rw [← Category.assoc (pullback.lift G W'.ι hG), pullback.lift_fst]
      · simp only [pullback.lift_snd, Category.assoc, hΦsnd]
        rw [← Category.assoc (pullback.lift G W'.ι hG), pullback.lift_snd,
          ← Category.assoc, morphismRestrict_ι, Category.assoc, iso.inv_hom_id,
          Category.comp_id]
    -- pointwise form of the cartesian square upstairs
    have hcond : ∀ z, p₁.base ((pullback.fst p₁ D.I.blowupMap).base z) =
        D.I.blowupMap.base ((pullback.snd p₁ D.I.blowupMap).base z) := by
      intro z
      have h2 : (pullback.fst p₁ D.I.blowupMap ≫ p₁).base z =
          (pullback.snd p₁ D.I.blowupMap ≫ D.I.blowupMap).base z := by
        rw [pullback.condition]
      simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using h2
    -- the graph upstairs is closed
    have hclosed2 : IsClosed (Set.range (pullback.lift G W'.ι hG)) := by
      refine isClosed_of_isClosed_preimage_subtypeVal
        (TopologicalSpace.Opens.isOpen
          ((pullback.snd p₁ D.I.blowupMap) ⁻¹ᵁ (D.I.blowupMap ⁻¹ᵁ X₀)))
        (N := ⇑(pullback.fst p₁ D.I.blowupMap) ⁻¹' closure (Set.range f₁))
        (isClosed_closure.preimage (pullback.fst p₁ D.I.blowupMap).continuous) ?_ ?_ hclosedG
      · intro z hz
        have : p₁.base ((pullback.fst p₁ D.I.blowupMap).base z) ∈ (X₀ : Set X₁) :=
          hSX₀ ⟨_, hz, rfl⟩
        rwa [hcond z] at this
      · rintro _ ⟨w, rfl⟩
        have hw : (pullback.lift G W'.ι hG ≫ pullback.fst p₁ D.I.blowupMap).base w =
            G.base w := by rw [pullback.lift_fst]
        have hw' : (pullback.fst p₁ D.I.blowupMap).base ((pullback.lift G W'.ι hG).base w) =
            G.base w := by
          simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using hw
        change (pullback.fst p₁ D.I.blowupMap).base _ ∈ closure (Set.range f₁)
        rw [hw']
        exact hGrange ⟨w, rfl⟩
    -- transport along the comparison isomorphism
    rw [hΓ]
    have he : Function.Surjective ⇑(iso.inv ∣_ W') :=
      (Scheme.homeoOfIso (asIso (iso.inv ∣_ W'))).surjective
    have hrange : Set.range ⇑((iso.inv ∣_ W') ≫ pullback.lift G W'.ι hG ≫ Φ.hom) =
        ⇑Φ.hom '' Set.range ⇑(pullback.lift G W'.ι hG) := by
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp]
      rw [Set.range_comp, he.range_eq, Set.image_univ, Set.range_comp]
    rw [hrange]
    exact ((Scheme.homeoOfIso Φ).isClosed_image).mpr hclosed2

end AlgebraicGeometry
