import Langlands.Geometry.Building.CrossTorusFunctions

/-! # Valuations under actual cross-torus isomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k]
  {S S' : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {i : S.toGrp ⟶ G} {j : S'.toGrp ⟶ H}

private abbrev pointTransportEquiv (f : G ≅ H) : rationalPoints G ≃* rationalPoints H where
  toFun := rationalPoints.map f.hom
  invFun := rationalPoints.map f.inv
  left_inv g := by
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  right_inv g := by
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  map_mul' := (rationalPoints.map f.hom).map_mul

private theorem pointMap_surjective (f : G ≅ H) :
    Function.Surjective (rationalPoints.map f.hom) :=
  (pointTransportEquiv f).surjective

private abbrev underlyingGroupIso (e : S ≅ S') : S.toGrp ≅ S'.toGrp where
  hom := CommGroupScheme.groupHom e.hom
  inv := CommGroupScheme.groupHom e.inv
  hom_inv_id := congrArg Additive.toMul e.hom_inv_id
  inv_hom_id := congrArg Additive.toMul e.inv_hom_id

variable (e : S ≅ S') (f : G ≅ H)
  (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)

include h

/-- The actual ambient map carries the entire rational root group onto the target one. -/
theorem image_rootGroupPoints_transport (a : characterLattice S) :
    rationalPoints.map f.hom '' (rootGroupPoints i a : Set (rationalPoints G)) =
      (rootGroupPoints j (characterLattice.congr e a) : Set (rationalPoints H)) := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (rootGroupPoints_transport_iff e f h a g).mpr hg
  · intro hg
    obtain ⟨g, rfl⟩ := pointMap_surjective f g
    exact ⟨g, (rootGroupPoints_transport_iff e f h a g).mp hg, rfl⟩

/-- The actual ambient map carries every filtration set onto its target at the same level. -/
theorem image_rootFiltration_transport (φ : RootFunctionFamily S G)
    (a : characterLattice S) (r : ℝ) :
    rationalPoints.map f.hom '' rootFiltration i φ a r =
      rootFiltration j (RootFunctionFamily.transportEquiv e f φ)
        (characterLattice.congr e a) r := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (rootFiltration_transport_iff e f h φ a r g).mpr hg
  · intro hg
    obtain ⟨g, rfl⟩ := pointMap_surjective f g
    exact ⟨g, (rootFiltration_transport_iff e f h φ a r g).mp hg, rfl⟩

variable [Mono i.hom.hom.left] [Mono j.hom.hom.left]

/-- Reflection realization uses the original actual character and cocharacter actions. -/
theorem realizesReflection_transport_iff (a : characterLattice S) (n : normalizerPoints i) :
    RealizesReflection j (characterLattice.congr e a)
        (normalizerPointsTransportEquiv e f h n) ↔ RealizesReflection i a n := by
  constructor
  · rintro ⟨ha, hv⟩
    refine ⟨(characterLattice.congr e).injective ?_, fun v hv0 => ?_⟩
    · simpa only [weylAction_transport, map_neg] using ha
    · apply (cocharacterRealCongr e).injective
      change cocharacterRealCongr e (normalizerAction i n v) = _
      rw [cocharacterRealCongr_normalizerAction e f h]
      exact hv _ ((eval_cocharacterRealCongr e a v).trans hv0)
  · rintro ⟨ha, hv⟩
    refine ⟨?_, fun v hv0 => ?_⟩
    · rw [weylAction_transport, ha, map_neg]
    · obtain ⟨v, rfl⟩ := (cocharacterRealCongr e).surjective v
      rw [eval_cocharacterRealCongr] at hv0
      change normalizerAction j (normalizerPointsTransportEquiv e f h n)
        (cocharacterRealCongr e v) = _
      rw [← cocharacterRealCongr_normalizerAction e f h]
      exact congrArg (cocharacterRealCongr e) (hv v hv0)

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

open RootFunctionFamily

/-- Every normalization condition and every axiom V0--V5 is preserved. -/
theorem IsRootDatumValuation.transport {φ : RootFunctionFamily S G}
    (hφ : IsRootDatumValuation i φ) :
    IsRootDatumValuation j (transportEquiv e f φ) where
  eq_top_of_not_mem_roots a ha g := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨g, rfl⟩ := pointMap_surjective f g
    rw [transportEquiv_apply_map]
    exact hφ.eq_top_of_not_mem_roots a
      (fun ha' => ha ((roots_mem_of_transport_iff e f h a).mpr ha')) g
  eq_top_of_not_mem a ha g hg := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨g, rfl⟩ := pointMap_surjective f g
    rw [transportEquiv_apply_map]
    exact hφ.eq_top_of_not_mem a ((roots_mem_of_transport_iff e f h a).mp ha) g
      (fun hg' => hg ((rootGroupPoints_transport_iff e f h a g).mpr hg'))
  three_le_encard a ha := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    have himage : transportEquiv e f φ (characterLattice.congr e a) ''
        (rootGroupPoints j (characterLattice.congr e a) : Set (rationalPoints H)) =
        φ a '' (rootGroupPoints i a : Set (rationalPoints G)) := by
      rw [← image_rootGroupPoints_transport e f h a, Set.image_image]
      simp only [transportEquiv_apply_map]
    rw [himage]
    exact hφ.three_le_encard a ((roots_mem_of_transport_iff e f h a).mp ha)
  one_mem a ha r := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    have hm := (rootFiltration_transport_iff e f h φ a r 1).mpr
      (hφ.one_mem a ((roots_mem_of_transport_iff e f h a).mp ha) r)
    simpa only [map_one] using hm
  mul_mem a ha r g g' hg hg' := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨g, rfl⟩ := pointMap_surjective f g
    obtain ⟨g', rfl⟩ := pointMap_surjective f g'
    rw [← map_mul]
    exact (rootFiltration_transport_iff e f h φ a r (g * g')).mpr
      (hφ.mul_mem a ((roots_mem_of_transport_iff e f h a).mp ha) r g g'
        ((rootFiltration_transport_iff e f h φ a r g).mp hg)
        ((rootFiltration_transport_iff e f h φ a r g').mp hg'))
  inv_mem a ha r g hg := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨g, rfl⟩ := pointMap_surjective f g
    rw [← map_inv]
    exact (rootFiltration_transport_iff e f h φ a r g⁻¹).mpr
      (hφ.inv_mem a ((roots_mem_of_transport_iff e f h a).mp ha) r g
        ((rootFiltration_transport_iff e f h φ a r g).mp hg))
  eq_top_iff a ha g hg := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨g, rfl⟩ := pointMap_surjective f g
    rw [transportEquiv_apply_map,
      hφ.eq_top_iff a ((roots_mem_of_transport_iff e f h a).mp ha) g
        ((rootGroupPoints_transport_iff e f h a g).mp hg)]
    exact (map_eq_one_iff (pointTransportEquiv f) (pointTransportEquiv f).injective).symm
  reflection a ha n hn := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨n, rfl⟩ := (normalizerPointsTransportEquiv e f h).surjective n
    obtain ⟨c, hc⟩ := hφ.reflection a ((roots_mem_of_transport_iff e f h a).mp ha) n
      ((realizesReflection_transport_iff e f h a n).mp hn)
    refine ⟨c, fun u hu hu1 => ?_⟩
    obtain ⟨u, rfl⟩ := pointMap_surjective f u
    have hu0 := (rootGroupPoints_transport_iff e f h a u).mp hu
    have hu01 : u ≠ 1 := by
      intro hu'
      apply hu1
      simp only [hu', map_one]
    change transportEquiv e f φ (characterLattice.congr e a)
        (rationalPoints.map f.hom u) =
      transportEquiv e f φ (-(characterLattice.congr e a))
        ((rationalPoints.map f.hom (n : rationalPoints G)) *
          rationalPoints.map f.hom u * (rationalPoints.map f.hom (n : rationalPoints G))⁻¹) +
        (c : WithTop ℝ)
    rw [← map_neg, ← map_inv, ← map_mul, ← map_mul, transportEquiv_apply_map,
      transportEquiv_apply_map]
    exact hc u hu0 hu01
  commutator a ha b hb hab r s := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨b, rfl⟩ := (characterLattice.congr e).surjective b
    have hab0 : ∀ t : ℝ, 0 < t →
        ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] a) := by
      intro t ht heq
      apply hab t ht
      simpa only [map_neg, map_smul, characterRealCongr_tmul,
        characterLattice.congr_apply] using congrArg (characterRealCongr e) heq
    have hc := Subgroup.map_mono (f := rationalPoints.map f.hom)
      (hφ.commutator a ((roots_mem_of_transport_iff e f h a).mp ha)
        b ((roots_mem_of_transport_iff e f h b).mp hb) hab0 r s)
    rw [Subgroup.map_commutator, MonoidHom.map_closure, MonoidHom.map_closure,
      image_rootFiltration_transport e f h, image_rootFiltration_transport e f h] at hc
    refine hc.trans ?_
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨g, hg, rfl⟩
    simp only [Set.mem_iUnion] at hg ⊢
    obtain ⟨p, q, hp, hq, hroot, hg⟩ := hg
    refine ⟨p, q, hp, hq, ?_, ?_⟩
    · change _ ∈ roots j
      simpa only [map_add, map_nsmul] using
        (roots_mem_of_transport_iff e f h (p • a + q • b)).mpr hroot
    · simpa only [map_add, map_nsmul] using
        (rootFiltration_transport_iff e f h φ (p • a + q • b)
          (p * r + q * s) g).mpr hg
  double a ha h2a u hu := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨u, rfl⟩ := pointMap_surjective f u
    rw [← map_nsmul] at h2a hu ⊢
    rw [transportEquiv_apply_map, transportEquiv_apply_map]
    exact hφ.double a ((roots_mem_of_transport_iff e f h a).mp ha)
      ((roots_mem_of_transport_iff e f h (2 • a)).mp h2a) u
      ((rootGroupPoints_transport_iff e f h (2 • a) u).mp hu)
  opposite a ha u hu hu1 u' hu' u'' hu'' hn := by
    obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
    obtain ⟨u, rfl⟩ := pointMap_surjective f u
    obtain ⟨u', rfl⟩ := pointMap_surjective f u'
    obtain ⟨u'', rfl⟩ := pointMap_surjective f u''
    have hu01 : u ≠ 1 := by
      intro hu0
      apply hu1
      simp only [hu0, map_one]
    rw [← map_neg] at hu' hu'' ⊢
    rw [← map_mul, ← map_mul] at hn
    rw [transportEquiv_apply_map, transportEquiv_apply_map]
    exact hφ.opposite a ((roots_mem_of_transport_iff e f h a).mp ha) u
      ((rootGroupPoints_transport_iff e f h a u).mp hu) hu01 u'
      ((rootGroupPoints_transport_iff e f h (-a) u').mp hu') u''
      ((rootGroupPoints_transport_iff e f h (-a) u'').mp hu'')
      ((mem_normalizerPoints_transport_iff e f h (u' * u * u'')).mp hn)

/-- The full valuation predicate is preserved and reflected by the family equivalence. -/
theorem isRootDatumValuation_transportEquiv_iff (φ : RootFunctionFamily S G) :
    IsRootDatumValuation j (transportEquiv e f φ) ↔ IsRootDatumValuation i φ := by
  constructor
  · intro hφ
    have hv := hφ.transport e.symm f.symm (torusTransport_inverse_square e f h)
    change IsRootDatumValuation i
      ((transportEquiv e f).symm (transportEquiv e f φ)) at hv
    simpa only [Equiv.symm_apply_apply] using hv
  · exact fun hφ => hφ.transport e f h

/-- Actual cross-torus isomorphisms identify the types of full root-datum valuations. -/
def rootDatumValuationTransportEquiv :
    {φ : RootFunctionFamily S G // IsRootDatumValuation i φ} ≃
      {ψ : RootFunctionFamily S' H // IsRootDatumValuation j ψ} :=
  (transportEquiv e f).subtypeEquiv
    (fun φ => (isRootDatumValuation_transportEquiv_iff e f h φ).symm)

/-- The valuation equivalence has exactly the original family transport underneath. -/
@[simp] theorem rootDatumValuationTransportEquiv_val
    (φ : {φ : RootFunctionFamily S G // IsRootDatumValuation i φ}) :
    (rootDatumValuationTransportEquiv e f h φ).val = transportEquiv e f φ.val := rfl

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
/-- Split-torus compatibility uses the same scalar valuation and actual torus-point map. -/
theorem IsSplitTorusCompatible.transport {ω : kˣ → ℝ} {φ : RootFunctionFamily S G}
    (hφ : IsSplitTorusCompatible i ω φ) :
    IsSplitTorusCompatible j ω (transportEquiv e f φ) := by
  intro a ha s u hu
  obtain ⟨a, rfl⟩ := (characterLattice.congr e).surjective a
  obtain ⟨s, rfl⟩ :=
    pointMap_surjective (underlyingGroupIso e) s
  obtain ⟨u, rfl⟩ := pointMap_surjective f u
  have hs : rationalPoints.map f.hom (rationalPoints.map i s) =
      rationalPoints.map j (rationalPoints.map (CommGroupScheme.groupHom e.hom) s) := by
    simpa only [rationalPoints.map_apply, Category.assoc, Grp.comp_hom_hom] using
      congrArg (fun m : S.toGrp ⟶ H => s ≫ m.hom.hom) h
  have hχ : characterRestrict (CommGroupScheme.groupHom e.hom)
      ((rationalCharacters.equivCharacterLattice S').symm (characterLattice.congr e a)) =
      (rationalCharacters.equivCharacterLattice S).symm a := by
    apply (rationalCharacters.equivCharacterLattice S).injective
    change e.hom ≫ (e.inv ≫ a) = a
    simp
  have heval :
      rationalCharacterEval
          ((rationalCharacters.equivCharacterLattice S').symm (characterLattice.congr e a))
          (rationalPoints.map (CommGroupScheme.groupHom e.hom) s) =
        rationalCharacterEval ((rationalCharacters.equivCharacterLattice S).symm a) s := by
    rw [← rationalCharacterEval_characterRestrict, hχ]
  change transportEquiv e f φ (characterLattice.congr e a)
      ((rationalPoints.map j (rationalPoints.map (CommGroupScheme.groupHom e.hom) s))⁻¹ *
        rationalPoints.map f.hom u *
        rationalPoints.map j (rationalPoints.map (CommGroupScheme.groupHom e.hom) s)) = _
  rw [← hs, ← map_inv, ← map_mul, ← map_mul, transportEquiv_apply_map,
    transportEquiv_apply_map, heval]
  exact hφ a ((roots_mem_of_transport_iff e f h a).mp ha) s u
    ((rootGroupPoints_transport_iff e f h a u).mp hu)

omit [Mono i.hom.hom.left] [Mono j.hom.hom.left] in
/-- Compatibility with the unchanged scalar valuation is preserved and reflected. -/
theorem isSplitTorusCompatible_transportEquiv_iff (ω : kˣ → ℝ)
    (φ : RootFunctionFamily S G) :
    IsSplitTorusCompatible j ω (transportEquiv e f φ) ↔ IsSplitTorusCompatible i ω φ := by
  constructor
  · intro hφ
    have hv := hφ.transport e.symm f.symm (torusTransport_inverse_square e f h)
    change IsSplitTorusCompatible i ω
      ((transportEquiv e f).symm (transportEquiv e f φ)) at hv
    simpa only [Equiv.symm_apply_apply] using hv
  · exact fun hφ => hφ.transport e f h

end Langlands.Geometry.Building
