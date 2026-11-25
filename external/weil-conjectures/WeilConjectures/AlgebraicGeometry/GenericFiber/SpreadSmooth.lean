/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GenericFiber.SpreadingOut
public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.LimitBaseChange
public import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothLimit
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# Spreading out a smooth dense open from the generic fibre

Let `B` be a Noetherian domain with fraction field `L`, `σ : Spec B ⟶ S` and `f : X ⟶ S` of
finite type. Suppose the generic fibre `X_L = X ×_S Spec L` has a dense open `W` with a
surjective closed immersion `Z ⟶ W` from a scheme `Z` smooth over `L`. Then for some nonzero
`r ∈ B`, the base change `X_r = X ×_S Spec B[1/r]` has an open immersed smooth `B[1/r]`-scheme
`V`, and over a nonempty open `O ⊆ Spec B[1/r]` every point of `X_r` is a specialization of a
point of `V` (`AlgebraicGeometry.exists_isImmersion_smooth_of_isFractionRing`).

`Spec L` is the limit of the `Spec B[1/r]`; the data descend to some stage by
`AlgebraicGeometry.exists_open_isClosedImmersion_of_isLimit_pt` and
`AlgebraicGeometry.Scheme.exists_smooth_pullback_snd_of_isLimit`, and `O` is the complement of
the closures of the images of the generic points of `X_r` outside `V`, none of which lies over
the generic point of `Spec B[1/r]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- In a quasi-sober space every point is a specialization of the generic point of an
irreducible component. -/
lemma exists_mem_irreducibleComponents_specializes {X : Type*} [TopologicalSpace X] [QuasiSober X]
    (x : X) : ∃ y : X, closure {y} ∈ irreducibleComponents X ∧ y ⤳ x := by
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := x)).closure
  have hCc : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
  have hirr : IsIrreducible C := hC.1
  have hg : closure {hirr.genericPoint} = C := by
    rw [IsIrreducible.genericPoint_closure_eq hirr, hCc.closure_eq]
  refine ⟨hirr.genericPoint, hg.symm ▸ hC, ?_⟩
  rw [specializes_iff_mem_closure, hg]
  exact hxC (subset_closure rfl)

/-- In a space with finitely many irreducible components, a dense open contains the generic
point of every irreducible component. -/
lemma mem_of_dense_of_closure_mem_irreducibleComponents {X : Type*} [TopologicalSpace X]
    (hX : (irreducibleComponents X).Finite) {U : Set X} (hU : Dense U) (hUo : IsOpen U) {y : X}
    (hy : closure {y} ∈ irreducibleComponents X) : y ∈ U := by
  have h := closure_sUnion_irreducibleComponents_sdiff_singleton hX _ hy
  have hO : IsOpen (⋃₀ (irreducibleComponents X \ {closure {y}}))ᶜ := by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hX.sdiff.isClosed_biUnion fun C hC ↦ isClosed_of_mem_irreducibleComponents C hC.1
  have hne : (⋃₀ (irreducibleComponents X \ {closure {y}}))ᶜ.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at h
    exact (Set.singleton_nonempty y).ne_empty (Set.subset_empty_iff.mp (h ▸ subset_closure))
  obtain ⟨w, hwO, hwU⟩ := hU.inter_open_nonempty _ hO hne
  have hyw : y ⤳ w := by
    rw [specializes_iff_mem_closure, ← h]
    exact subset_closure hwO
  exact hyw.mem_open hUo hwU

namespace AlgebraicGeometry

/-- The localization `B[1/∏ s] ⟶ L` of a domain `B` into its fraction field is injective. -/
lemma injective_awayProd_fractionRing {B L : Type u} [CommRing B] [IsDomain B] [Field L]
    [Algebra B L] [IsFractionRing B L] (s : Finset (⊥ : Ideal B).primeCompl)
    (φ : CommRingCat.AwayProd (⊥ : Ideal B) s →+* L)
    (hφ : φ.comp (algebraMap B _) = algebraMap B L) : Function.Injective φ := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨b, m⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Submonoid.powers (∏ x ∈ s, (x : B))) x
  have h := congrArg φ (IsLocalization.mk'_spec (CommRingCat.AwayProd (⊥ : Ideal B) s) b m)
  rw [map_mul, hx, zero_mul, ← RingHom.comp_apply, hφ, eq_comm,
    IsFractionRing.to_map_eq_zero_iff] at h
  simp [h]

/-- **Spreading out a smooth dense open from the generic fibre.** Let `B` be a Noetherian domain
with fraction field `L`, `σ : Spec B ⟶ S`, `f : X ⟶ S` locally of finite type and
quasi-compact, and `X_L` the generic fibre (a cartesian square `a, b`). Let `W ⊆ X_L` be a dense
open and `z : Z ⟶ W` a surjective closed immersion with `Z` smooth over `L`. Then for some
nonzero `r ∈ B` there are an immersion `v : V ⟶ X_r = X ×_S Spec B[1/r]` with open image and
`V` smooth over `B[1/r]`, and a nonempty open `O ⊆ Spec B[1/r]` over which every point of `X_r`
is a specialization of a point of the image of `v`. -/
theorem exists_isImmersion_smooth_of_isFractionRing {B L : Type u} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] [Field L] [Algebra B L] [IsFractionRing B L] {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (σ : Spec (.of B) ⟶ S)
    {YL : Scheme.{u}} (a : YL ⟶ X) (b : YL ⟶ Spec (.of L))
    (H : IsPullback a b f (Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ σ))
    (W : YL.Opens) (hW : Dense (W : Set YL)) {Z : Scheme.{u}} (z : Z ⟶ W.toScheme)
    [IsClosedImmersion z] [Surjective z] (hz : Smooth (z ≫ W.ι ≫ b)) :
    ∃ (r : B) (_ : r ≠ 0) (V : Scheme.{u})
      (v : V ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r))) ≫ σ))
      (O : (Spec (.of (Localization.Away r))).Opens),
      IsImmersion v ∧ IsOpen (Set.range v) ∧
      Smooth (v ≫ pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r))) ≫ σ)) ∧
      (O : Set (Spec (.of (Localization.Away r)))).Nonempty ∧
      ∀ x, pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r))) ≫ σ)
        x ∈ O → ∃ y ∈ Set.range v, y ⤳ x := by
  classical
  -- `Spec L` as the limit of the `Spec B[1/r]`
  have : IsLocalization (⊥ : Ideal B).primeCompl L := by
    rw [Ideal.primeCompl_bot]; infer_instance
  let eK : CommRingCat.of (Localization.AtPrime (⊥ : Ideal B)) ≅ CommRingCat.of L :=
    (IsLocalization.algEquiv (⊥ : Ideal B).primeCompl (Localization.AtPrime (⊥ : Ideal B))
      L).toRingEquiv.toCommRingCatIso
  let cR := (CommRingCat.awayProdCocone (⊥ : Ideal B)).extend eK.hom
  have hR : IsColimit cR := (CommRingCat.isColimitAwayProdCocone _).ofIsoColimit
    (Cocone.ext eK fun _ ↦ rfl)
  have hRA (s : Finset (⊥ : Ideal B).primeCompl) :
      CommRingCat.ofHom (algebraMap B (CommRingCat.AwayProd ⊥ s)) ≫ cR.ι.app s =
        CommRingCat.ofHom (algebraMap B L) := by
    change _ ≫ _ ≫ eK.hom = _
    rw [CommRingCat.ofHom_algebraMap_comp_awayProdCocone_ι_app_assoc]
    ext x
    exact (IsLocalization.algEquiv (⊥ : Ideal B).primeCompl
      (Localization.AtPrime (⊥ : Ideal B)) L).commutes x
  let I := (Finset (⊥ : Ideal B).primeCompl)ᵒᵖ
  let D₀ : I ⥤ Scheme.{u} := (CommRingCat.awayProdDiagram (⊥ : Ideal B)).op ⋙ Scheme.Spec
  let c₀ : Cone D₀ := Scheme.Spec.mapCone cR.op
  have hc₀ : IsLimit c₀ := isLimitOfPreserves Scheme.Spec hR.op
  let q (s : I) : D₀.obj s ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap B (CommRingCat.AwayProd ⊥ s.unop))) ≫ σ
  have hq {s s' : I} (u : s ⟶ s') : D₀.map u ≫ q s' = q s := by
    change Spec.map _ ≫ Spec.map _ ≫ σ = _
    rw [← Spec.map_comp_assoc]
    exact congrArg (Spec.map · ≫ σ)
      (CommRingCat.ofHom_algebraMap_comp_awayProdDiagram_map _ u.unop)
  let q₀ : Spec (.of L) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap B L)) ≫ σ
  have hq₀ (s : I) : c₀.π.app s ≫ q s = q₀ := by
    change Spec.map _ ≫ Spec.map _ ≫ σ = _
    rw [← Spec.map_comp_assoc]
    exact congrArg (Spec.map · ≫ σ) (hRA s.unop)
  have : IsConnected I := IsCofiltered.isConnected I
  let D := baseChangeOverFamilyDiagram D₀ q hq f
  let c := baseChangeOverFamilyCone D₀ c₀ q hq q₀ hq₀ f
  have hc : IsLimit c := isLimitBaseChangeOverFamilyCone D₀ c₀ q hq q₀ hq₀ f hc₀
  have : ∀ {s s' : I} (u : s ⟶ s'), IsAffineHom (D₀.map u) := fun u ↦
    isAffineHom_of_isAffine (X := Spec _) (Y := Spec _) _
  have (s : I) : IsAffine (D₀.obj s) := inferInstanceAs (IsAffine (Spec _))
  have (s : I) : IsNoetherian (D₀.obj s) :=
    inferInstanceAs (IsNoetherian (Spec (.of (CommRingCat.AwayProd ⊥ s.unop))))
  have (s : I) : IsNoetherian (D.obj s) := by
    have : IsLocallyNoetherian (D.obj s) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (q s))
    have : CompactSpace (D.obj s) :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (q s))
    exact {}
  have : IsNoetherian c.pt := by
    have : IsLocallyNoetherian c.pt := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f q₀)
    have : CompactSpace c.pt := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f q₀)
    exact {}
  -- transport the data on the generic fibre to the limit
  let e₀ : YL ≅ c.pt := H.isoPullback
  let W' : c.pt.Opens := e₀.hom ''ᵁ W
  let z' : Z ⟶ W'.toScheme := z ≫ (e₀.hom.isoImage W).hom
  have hz'ι : z' ≫ W'.ι ≫ pullback.snd f q₀ = z ≫ W.ι ≫ b := by
    simp only [z', W', Category.assoc, Scheme.Hom.isoImage_hom_ι_assoc]
    rw [IsPullback.isoPullback_hom_snd]
  have hW'c : IsCompact (SetLike.coe W') := TopologicalSpace.NoetherianSpace.isCompact _
  obtain ⟨j, Wj, Zj, zj, s, hzj₁, hzj₂, hpre, hs⟩ :=
    exists_open_isClosedImmersion_of_isLimit_pt hc W' hW'c z'
  set p' : Zj ⟶ D₀.obj j := zj ≫ Wj.ι ≫ pullback.snd f (q j)
  have h2 (k : I) : IsPullback (c.π.app k) (pullback.snd f q₀) (pullback.snd f (q k))
      (c₀.π.app k) :=
    isPullback_pullback_map f q₀ (q k) (c₀.π.app k) (hq₀ k)
  have hs' : IsPullback s (z' ≫ W'.ι ≫ pullback.snd f q₀) p' (c₀.π.app j) := by
    have := hs.paste_vert (h2 j)
    simp only [Category.assoc] at this
    exact this
  have : IsLocallyNoetherian Zj := LocallyOfFiniteType.isLocallyNoetherian p'
  have : CompactSpace Zj := QuasiCompact.compactSpace_of_compactSpace zj
  have : IsNoetherian Zj := {}
  have : QuasiSeparated p' :=
    (HasAffineProperty.iff_of_isAffine (P := @QuasiSeparated)).mpr inferInstance
  have hA : Smooth (z' ≫ W'.ι ≫ pullback.snd f q₀) := by
    rw [hz'ι]
    exact hz
  have : Smooth (pullback.snd p' (c₀.π.app j)) := by
    rw [← hs'.isoPullback_inv_snd]
    infer_instance
  obtain ⟨t, g, hsmt⟩ := Scheme.exists_smooth_pullback_snd_of_isLimit hc₀ p'
  set v := pullback.snd (zj ≫ Wj.ι) (D.map g)
  set sndt := pullback.snd f (q t)
  have hrange : Set.range v = D.map g ⁻¹' (Wj : Set (D.obj j)) := by
    rw [Scheme.Pullback.range_snd]
    congr 1
    ext y
    refine ⟨fun ⟨w, hw⟩ ↦ hw ▸ (zj w).2, fun hy ↦ ?_⟩
    obtain ⟨w, hw⟩ := zj.surjective ⟨y, hy⟩
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hw]; rfl⟩
  have hcπ : c.π.app t ⁻¹' Set.range v = (W' : Set c.pt) := by
    rw [hrange, ← Set.preimage_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, c.w g]
    exact congrArg SetLike.coe hpre
  have hW'd : Dense (W' : Set c.pt) :=
    e₀.hom.surjective.denseRange.dense_image e₀.hom.continuous hW
  have hfinc : (irreducibleComponents c.pt).Finite :=
    TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  -- generic points of `X_t` over the generic point of the base lie in the image of `v`
  have hgood (y : D.obj t) (hy : closure {y} ∈ irreducibleComponents (D.obj t))
      (hy' : sndt y ∈ Set.range (c₀.π.app t)) : y ∈ Set.range v := by
    obtain ⟨w, hw⟩ := hy'
    obtain ⟨x', hx'₁, hx'₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := sndt)
      (g := c₀.π.app t) y w hw.symm
    set x := (h2 t).isoPullback.inv x'
    have hx : c.π.app t x = y := by
      rw [← hx'₁, ← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
      rfl
    obtain ⟨y', hy'c, hy'x⟩ := exists_mem_irreducibleComponents_specializes x
    have hy'W : y' ∈ (W' : Set c.pt) :=
      mem_of_dense_of_closure_mem_irreducibleComponents hfinc hW'd W'.isOpen hy'c
    have hsp : c.π.app t y' ⤳ y := hx ▸ hy'x.map (c.π.app t).continuous
    have heq : c.π.app t y' = y := by
      have hsub : closure {y} ⊆ closure {c.π.app t y'} := by
        rw [← specializes_iff_closure_subset]
        exact hsp
      have := hy.2 (isIrreducible_singleton.closure) hsub
      exact (inseparable_iff_closure_eq.mpr (hsub.antisymm this).symm).eq
    rw [← heq, ← Set.mem_preimage, hcπ]
    exact hy'W
  -- the image of `Spec L` is the generic point of the stage
  have hξ (pt : Spec (.of L)) (w : D₀.obj t) : c₀.π.app t pt ⤳ w := by
    have hinj := injective_awayProd_fractionRing (L := L) t.unop (cR.ι.app t.unop).hom
      (congrArg CommRingCat.Hom.hom (hRA t.unop))
    have hpt : PrimeSpectrum.asIdeal (R := L) pt = ⊥ :=
      @Ideal.eq_bot_of_prime L _ _ (PrimeSpectrum.isPrime pt)
    rw [← PrimeSpectrum.le_iff_specializes]
    intro x hx
    have hx' : (cR.ι.app t.unop).hom x ∈ PrimeSpectrum.asIdeal (R := L) pt := hx
    rw [hpt, Ideal.mem_bot] at hx'
    rw [hinj (hx'.trans (map_zero _).symm)]
    exact zero_mem _
  -- the bad generic points
  let G : Set (D.obj t) := {y | closure {y} ∈ irreducibleComponents (D.obj t) ∧
    y ∉ Set.range v}
  have hG : G.Finite := by
    refine Set.Finite.of_finite_image (f := fun y ↦ closure {y})
      ((TopologicalSpace.NoetherianSpace.finite_irreducibleComponents).subset ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
    · intro y _ y' _ h
      exact (inseparable_iff_closure_eq.mpr h).eq
  let O : (D₀.obj t).Opens := ⟨(⋃ y ∈ G, closure {sndt y})ᶜ,
    (hG.isClosed_biUnion fun _ _ ↦ isClosed_closure).isOpen_compl⟩
  have hsm : Smooth (v ≫ sndt) := by
    have H' : IsPullback (pullback.fst (zj ≫ Wj.ι) (D.map g)) (v ≫ sndt) p' (D₀.map g) := by
      have := (IsPullback.of_hasPullback (zj ≫ Wj.ι) (D.map g)).paste_vert
        (isPullback_baseChangeOverFamilyDiagram_map D₀ q hq f g)
      simp only [Category.assoc] at this
      exact this
    rw [← H'.isoPullback_hom_snd]
    infer_instance
  refine ⟨∏ x ∈ t.unop, (x : B), Finset.prod_ne_zero_iff.mpr fun x _ hx ↦ x.2 (by simp [hx]),
    pullback (zj ≫ Wj.ι) (D.map g), v, O, inferInstance, ?_, hsm, ?_, ?_⟩
  · have := Wj.isOpen.preimage (D.map g).continuous
    rw [← hrange] at this
    exact this
  · obtain ⟨pt⟩ : Nonempty (Spec (.of L)) := inferInstance
    refine ⟨c₀.π.app t pt, ?_⟩
    simp only [O, TopologicalSpace.Opens.coe_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro y hy hcl
    exact hy.2 (hgood y hy.1 ⟨pt, ((hξ pt _).antisymm (specializes_iff_mem_closure.mpr hcl)).eq⟩)
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := exists_mem_irreducibleComponents_specializes x
    by_cases hyv : y ∈ Set.range v
    · exact ⟨y, hyv, hyx⟩
    · exfalso
      refine hx ?_
      simp only [Set.mem_iUnion]
      exact ⟨y, ⟨hy, hyv⟩, specializes_iff_mem_closure.mp (hyx.map sndt.continuous)⟩

end AlgebraicGeometry
