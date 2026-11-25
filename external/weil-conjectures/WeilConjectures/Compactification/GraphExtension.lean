/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.Compactification.EliminationOfIndeterminacy
public import WeilConjectures.Compactification.ImageTransport
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!

# Graph extension of a compactification

This file constructs the **graph extension** of a compactification (Stacks Project
Tag 0F3Z; blueprint `def:proper-extension`, `thm:0F3Z`, `def:nagata-graph-extension`,
`lemma:nagata-graph-extension`; proof order item 33):

- `AlgebraicGeometry.Compactification.ProperExtension`: the data of a graph extension of
  a compactification `c` of a quasi-compact open `V ⊆ U`;
- `AlgebraicGeometry.Compactification.nonempty_properExtension`: such a compactification
  extends, after a `V`-admissible blow-up of the compactification, to a proper morphism
  `V^gr ⟶ U` restricting to the identity on `V`.

The construction takes the graph of the compactification, transports its
scheme-theoretic image through an admissible blow-up
(`WeilConjectures.Compactification.ImageTransport`, Tag 0F3Y) and eliminates the
indeterminacy of the first projection
(`WeilConjectures.Compactification.EliminationOfIndeterminacy`, Tag 081S).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section GraphExtension

variable {S U : Scheme.{u}}

/-- The data of a **graph extension** of a compactification `c` of a quasi-compact open
`V ⊆ U` (Stacks Project Tag 0F3Z; blueprint: `def:nagata-graph-extension`). -/
structure Compactification.ProperExtension (u : U ⟶ S) (V : U.Opens)
    (c : Compactification (V.ι ≫ u)) where
  /-- The `V`-admissible blow-up of the compactification. -/
  B : IsAdmissible c.Z c.i.opensRange
  /-- The open subscheme `V^gr` of the blown-up compactification carrying the
  extension. -/
  Vgr : B.I.blowup.Opens
  /-- The proper extension `V^gr ⟶ U` of the inclusion of `V`. -/
  ψ : Vgr.toScheme ⟶ U
  /-- The open embedding of `V` into `V^gr`. -/
  v : V.toScheme ⟶ Vgr.toScheme
  /-- The extension is proper. -/
  isProper_ψ : IsProper ψ
  /-- The copy of `V` is an open subscheme of `V^gr`. -/
  isOpenImmersion_v : IsOpenImmersion v
  /-- The embedded copy of `V` lifts the open immersion of the compactification. -/
  v_blowupMap : v ≫ Vgr.ι ≫ B.I.blowupMap = c.i
  /-- The extension really extends the inclusion of `V`. -/
  v_ψ : v ≫ ψ = V.ι
  /-- The inverse image of `V` is exactly the embedded copy of `V`. -/
  range_v : ((ψ ⁻¹ᵁ V : Vgr.toScheme.Opens) : Set Vgr.toScheme) = Set.range v
  /-- The extension is an isomorphism over `V`. -/
  isIso_ψ_restrict : IsIso (ψ ∣_ V)
  /-- The extension lies over `S`. -/
  ψ_u : ψ ≫ u = Vgr.ι ≫ B.I.blowupMap ≫ c.g

attribute [instance] Compactification.ProperExtension.isProper_ψ
  Compactification.ProperExtension.isOpenImmersion_v

/-- **Graph extension** (Stacks Project Tag 0F3Z): a compactification of a
quasi-compact open `V ⊆ U` extends, after a `V`-admissible blow-up of the
compactification, to a proper morphism `V^gr ⟶ U` restricting to the identity on `V`.
(Blueprint: `lemma:nagata-graph-extension`; proof order item 33.) -/
theorem Compactification.nonempty_properExtension
    [CompactSpace S] [QuasiSeparatedSpace S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (V : U.Opens) (hV : IsCompact (V : Set U)) (c : Compactification (V.ι ≫ u)) :
    Nonempty (Compactification.ProperExtension u V c) := by
  -- The graph construction of the blueprint: `V^gr` is the open strict transform of
  -- the scheme-theoretic image of the graph `V ⟶ c.Z ×_S U`, supplied by the
  -- partial-section lemma (`partialSectionRestrictIso`), the image transport
  -- lemma (`Scheme.Hom.ker_lift_admissibleBlowup`) and elimination of indeterminacy
  -- (`exists_admissibleBlowup_isOpenImmersion_strictTransformMap`); `ψ` is the second
  -- projection, proper because `c.Z ×_S U ⟶ U` is proper
  -- (`isProper_imageι_comp_fst`).
  -- Step 0: finiteness of the ambient schemes and quasi-compactness of the inclusions.
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : QuasiSeparatedSpace U := quasiSeparatedSpace_of_quasiSeparated u
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : QuasiSeparatedSpace c.Z := quasiSeparatedSpace_of_quasiSeparated c.g
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  -- Step 1: the graph `γ = (c.i, V.ι) : V ⟶ c.Z ×_S U` of the compactification, a
  -- partial section of the first projection over the open immersion `c.i`.
  obtain ⟨γ, hγfst, hγsnd⟩ : ∃ γ : V.toScheme ⟶ pullback c.g u,
      γ ≫ pullback.fst c.g u = c.i ∧ γ ≫ pullback.snd c.g u = V.ι :=
    ⟨pullback.lift c.i V.ι c.comm.symm, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hqcγ : QuasiCompact γ := quasiCompact_of_partialSection c.g u c.i γ hγfst
  -- the two projections of the scheme-theoretic image of the graph
  let p : γ.image ⟶ c.Z := γ.imageι ≫ pullback.fst c.g u
  let ψ₀ : γ.image ⟶ U := γ.imageι ≫ pullback.snd c.g u
  have hψ₀def : ψ₀ = γ.imageι ≫ pullback.snd c.g u := rfl
  have : IsSeparated (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : LocallyOfFiniteType (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : QuasiCompact (pullback.fst c.g u) := MorphismProperty.pullback_fst _ _ ‹_›
  have : IsSeparated p := inferInstanceAs (IsSeparated (γ.imageι ≫ pullback.fst c.g u))
  have : LocallyOfFiniteType p :=
    inferInstanceAs (LocallyOfFiniteType (γ.imageι ≫ pullback.fst c.g u))
  have : QuasiCompact p := inferInstanceAs (QuasiCompact (γ.imageι ≫ pullback.fst c.g u))
  -- Step 2: `p` is an isomorphism over the compact open `V₀ = c.i(V)`
  -- (`isIso_restrict_imageι_comp_fst`), so its indeterminacy can be eliminated.
  have hV₀ : IsCompact ((c.i.opensRange : c.Z.Opens) : Set c.Z) :=
    isCompact_range c.i.continuous
  have hpV₀ : IsIso (p ∣_ c.i.opensRange) := isIso_restrict_imageι_comp_fst c.g u c.i γ hγfst
  obtain ⟨B, hB⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap hV₀ p hpV₀
  let π : B.I.blowup ⟶ c.Z := B.I.blowupMap
  let W : c.Z.Opens := B.preservedOpen
  have hOIst : IsOpenImmersion (strictTransformMap p π W) := hB
  -- `V^gr` is the open strict transform, and `ψ` the projection to `U` through the
  -- scheme-theoretic image of the graph.
  let Vgr : B.I.blowup.Opens := (strictTransformMap p π W).opensRange
  let e : strictTransform p π W ≅ Vgr.toScheme := (strictTransformMap p π W).isoOpensRange
  have he : e.hom ≫ Vgr.ι = strictTransformMap p π W :=
    (strictTransformMap p π W).isoOpensRange_hom_ι
  have hVgrι : Vgr.ι = e.inv ≫ strictTransformMap p π W := by
    rw [← he, Iso.inv_hom_id_assoc]
  let ψ : Vgr.toScheme ⟶ U := e.inv ≫ strictTransformToSource p π W ≫ ψ₀
  have hψdef : ψ = e.inv ≫ strictTransformToSource p π W ≫ ψ₀ := rfl
  -- Step 3: the canonical lift `ℓ` of `c.i` along the blow-up, an open immersion with
  -- range the full preimage of `c.i(V)`.
  have hπV₀ : IsIso (π ∣_ c.i.opensRange) := B.isIso_blowupMap_restrict
  obtain ⟨ℓ, hℓπ⟩ : ∃ ℓ : V.toScheme ⟶ B.I.blowup, ℓ ≫ π = c.i :=
    ⟨(c.i.isoOpensRange.hom ≫ inv (π ∣_ c.i.opensRange)) ≫ (π ⁻¹ᵁ c.i.opensRange).ι, by
      simp only [Category.assoc]
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]⟩
  have hOIℓ : IsOpenImmersion ℓ :=
    isOpenImmersion_of_comp_of_isIso_restrict ℓ π c.i hℓπ hπV₀
  have hrangeℓ : Set.range ℓ = ⇑π ⁻¹' Set.range c.i :=
    range_eq_preimage_of_comp_of_isIso_restrict ℓ π c.i hℓπ hπV₀
  -- the canonical morphism to the image projects back to `c.i` and `V.ι`
  have htoImp : γ.toImage ≫ p = c.i := by
    have h := Scheme.Hom.toImage_imageι_assoc γ (pullback.fst c.g u)
    rw [hγfst] at h
    exact h
  have hψ₀V : γ.toImage ≫ ψ₀ = V.ι := by
    have h := Scheme.Hom.toImage_imageι_assoc γ (pullback.snd c.g u)
    rw [hγsnd] at h
    exact h
  -- Step 4: the embedding `v` of `V` into `V^gr`, through the open strict transform.
  obtain ⟨v, hvι, hvst⟩ : ∃ v : V.toScheme ⟶ Vgr.toScheme,
      v ≫ Vgr.ι = ℓ ∧ v ≫ e.inv ≫ strictTransformToSource p π W = γ.toImage := by
    have hcompk : γ.toImage ≫ p = ℓ ≫ π := by
      rw [htoImp, hℓπ]
    have hkfst : pullback.lift γ.toImage ℓ hcompk ≫ pullback.fst p π = γ.toImage :=
      pullback.lift_fst _ _ _
    have hksnd : pullback.lift γ.toImage ℓ hcompk ≫ pullback.snd p π = ℓ :=
      pullback.lift_snd _ _ _
    have hkrange : Set.range (pullback.lift γ.toImage ℓ hcompk ≫ pullback.fst p π ≫ p) ⊆
        (W : Set c.Z) := by
      rw [← Category.assoc, hkfst, htoImp]
      rintro - ⟨t, rfl⟩
      exact B.le_preservedOpen ⟨t, rfl⟩
    refine ⟨(strictTransformOpenLift p π W (pullback.lift γ.toImage ℓ hcompk) hkrange ≫
        strictTransformFactor p π W) ≫ e.hom, ?_, ?_⟩
    · rw [Category.assoc, he, Category.assoc, strictTransformFactor_strictTransformMap,
        strictTransformOpenLift_ι_assoc, hksnd]
    · rw [Category.assoc, Iso.hom_inv_id_assoc]
      simp only [strictTransformToSource]
      rw [Category.assoc, strictTransformFactor_ι_assoc, strictTransformOpenLift_ι_assoc,
        hkfst]
  -- Step 5: the extension `ψ` is proper: it is a closed immersion into the base change
  -- of the (proper) blow-up followed by the proper projection `SIm(γ) ⟶ U`.
  have hψ₀proper : IsProper ψ₀ := by
    have h1 : IsProper (pullback.snd c.g u) := MorphismProperty.pullback_snd _ _ c.isProper
    exact inferInstanceAs (IsProper (γ.imageι ≫ pullback.snd c.g u))
  have hψproper : IsProper ψ := by
    have h2 : IsProper (pullback.fst p π) :=
      MorphismProperty.pullback_fst _ _ B.isProper_blowupMap
    rw [hψdef]
    simp only [strictTransformToSource]
    infer_instance
  -- Step 6: `v` is an open immersion, since `ℓ` is one.
  have hOIv : IsOpenImmersion v := by
    have : IsOpenImmersion (v ≫ Vgr.ι) := by
      rw [hvι]
      exact hOIℓ
    exact IsOpenImmersion.of_comp v Vgr.ι
  -- Step 7: the compatibilities of `v` and `ψ`.
  have hvblow : v ≫ Vgr.ι ≫ π = c.i := by
    rw [← Category.assoc, hvι, hℓπ]
  have hvψ : v ≫ ψ = V.ι := by
    have h1 : v ≫ ψ = (v ≫ e.inv ≫ strictTransformToSource p π W) ≫ ψ₀ := by
      rw [hψdef]
      simp only [Category.assoc]
    rw [h1, hvst, hψ₀V]
  have hpsq : ψ₀ ≫ u = p ≫ c.g := by
    have h : (γ.imageι ≫ pullback.snd c.g u) ≫ u =
        (γ.imageι ≫ pullback.fst c.g u) ≫ c.g := by
      simp only [Category.assoc, ← pullback.condition]
    exact h
  have hψu : ψ ≫ u = Vgr.ι ≫ π ≫ c.g := by
    calc ψ ≫ u = e.inv ≫ strictTransformToSource p π W ≫ ψ₀ ≫ u := by
          rw [hψdef]
          simp only [Category.assoc]
      _ = e.inv ≫ strictTransformToSource p π W ≫ p ≫ c.g := by rw [hpsq]
      _ = e.inv ≫ (strictTransformToSource p π W ≫ p) ≫ c.g := by
          simp only [Category.assoc]
      _ = e.inv ≫ (strictTransformMap p π W ≫ π) ≫ c.g := by
          rw [strictTransform_condition]
      _ = (e.inv ≫ strictTransformMap p π W) ≫ π ≫ c.g := by
          simp only [Category.assoc]
      _ = Vgr.ι ≫ π ≫ c.g := by rw [← hVgrι]
  -- Step 8: the inverse image of `V` under `ψ` is exactly the embedded copy of `V`.
  have hrangev : ((ψ ⁻¹ᵁ V : Vgr.toScheme.Opens) : Set Vgr.toScheme) = Set.range v := by
    apply subset_antisymm
    · -- a point of `V^gr` over `V` lies on the embedded copy of `V`: its image in
      -- `SIm(γ)` is a limit point of the graph lying over `V`, hence on the graph
      -- (`closure_range_inter_preimage_range_snd_subset`), and the lift `ℓ` then
      -- recovers it as the image of a point of `V`.
      intro t ht
      have htV : ψ t ∈ Set.range V.ι := by
        rw [Scheme.Opens.range_ι]
        exact ht
      have hψt : ψ t = ψ₀ (strictTransformToSource p π W (e.inv t)) := by
        rw [hψdef]
        simp only [Scheme.Hom.comp_apply]
      have hcl : γ.imageι (strictTransformToSource p π W (e.inv t)) ∈
          closure (Set.range γ) := by
        rw [← Scheme.Hom.support_ker γ, ← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨_, rfl⟩
      have hsndz : pullback.snd c.g u
          (γ.imageι (strictTransformToSource p π W (e.inv t))) ∈ Set.range V.ι := by
        rw [← Scheme.Hom.comp_apply, ← hψ₀def, ← hψt]
        exact htV
      obtain ⟨v₀, hv₀⟩ := closure_range_inter_preimage_range_snd_subset c.g u γ V.ι hγsnd
        ⟨hcl, hsndz⟩
      have htoim : γ.imageι (γ.toImage v₀) = γ v₀ := by
        rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]
      have hz₀ : strictTransformToSource p π W (e.inv t) = γ.toImage v₀ :=
        γ.imageι.isClosedEmbedding.injective (by rw [htoim, hv₀])
      have hπVgr : π (Vgr.ι t) = c.i v₀ := by
        calc π (Vgr.ι t) = (Vgr.ι ≫ π) t := (Scheme.Hom.comp_apply _ _ _).symm
          _ = ((e.inv ≫ strictTransformMap p π W) ≫ π) t := by rw [hVgrι]
          _ = (e.inv ≫ strictTransformToSource p π W ≫ p) t := by
              rw [Category.assoc, ← strictTransform_condition]
          _ = p (strictTransformToSource p π W (e.inv t)) := by
              simp only [Scheme.Hom.comp_apply]
          _ = p (γ.toImage v₀) := by rw [hz₀]
          _ = (γ.toImage ≫ p) v₀ := (Scheme.Hom.comp_apply _ _ _).symm
          _ = c.i v₀ := by rw [htoImp]
      have hbmem : Vgr.ι t ∈ Set.range ℓ := by
        rw [hrangeℓ]
        exact ⟨v₀, hπVgr.symm⟩
      obtain ⟨v₁, hv₁⟩ := hbmem
      have hv₁₀ : v₁ = v₀ := by
        apply c.i.isOpenEmbedding.injective
        calc c.i v₁ = (ℓ ≫ π) v₁ := by rw [hℓπ]
          _ = π (ℓ v₁) := Scheme.Hom.comp_apply _ _ _
          _ = π (Vgr.ι t) := by rw [hv₁]
          _ = c.i v₀ := hπVgr
      refine ⟨v₀, Vgr.ι.isOpenEmbedding.injective ?_⟩
      calc Vgr.ι (v v₀) = (v ≫ Vgr.ι) v₀ := (Scheme.Hom.comp_apply _ _ _).symm
        _ = ℓ v₀ := by rw [hvι]
        _ = ℓ v₁ := by rw [hv₁₀]
        _ = Vgr.ι t := hv₁
    · -- conversely the embedded copy of `V` lies over `V`, since `v ≫ ψ = V.ι`
      rintro - ⟨v₀, rfl⟩
      have hmem : ψ (v v₀) ∈ (V : Set U) := by
        rw [← Scheme.Hom.comp_apply, hvψ, ← Scheme.Opens.range_ι]
        exact ⟨v₀, rfl⟩
      exact hmem
  -- Step 9: `ψ` restricts to an isomorphism over `V`.
  have hisoψ : IsIso (ψ ∣_ V) := isIso_morphismRestrict_of_range_eq ψ V v hvψ hrangev
  exact ⟨{ B := B, Vgr := Vgr, ψ := ψ, v := v, isProper_ψ := hψproper,
           isOpenImmersion_v := hOIv, v_blowupMap := hvblow, v_ψ := hvψ,
           range_v := hrangev, isIso_ψ_restrict := hisoψ, ψ_u := hψu }⟩

end GraphExtension

end AlgebraicGeometry
