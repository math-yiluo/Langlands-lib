/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.Topology.Maps.Basic

/-!
# Open immersions respect open immersions on the right

The `MorphismProperty.RespectsRight` instance for open immersions of schemes.

We also record the structure of **lifts of an open immersion along a partial
isomorphism**: if `q ≫ π` is an open immersion `j` and `π` is an isomorphism over the
range of `j`, then `q` factors as an isomorphism onto the full inverse image of the
range of `j`; in particular `q` is an open immersion
(`AlgebraicGeometry.isOpenImmersion_of_comp_of_isIso_restrict`) with range the inverse
image of the range of `j`
(`AlgebraicGeometry.range_eq_preimage_of_comp_of_isIso_restrict`). These describe the
embedded copies of preserved opens in admissible blow-ups.

Finally we record the range of the base change of an open immersion
(`AlgebraicGeometry.range_snd_of_isPullback`) and the form of
`AlgebraicGeometry.isIso_morphismRestrict_of_range_eq` in which the modification layer
produces its data: a partial section `m` of `ψ` whose composite `m ≫ ψ` is an open
immersion and whose range is the full inverse image of the range of `m ≫ ψ` exhibits
`ψ` as an isomorphism over that range
(`AlgebraicGeometry.isIso_morphismRestrict_opensRange_of_range_eq`).
The `MorphismProperty.RespectsRight` instance for open immersions of schemes, and the
emptiness of a fibre product over disjoint opens
(`AlgebraicGeometry.isEmpty_pullback_of_disjoint_range`).
The lift of a morphism of `S`-schemes along an open immersion of `S`-schemes is a morphism of
`S`-schemes (`AlgebraicGeometry.IsOpenImmersion.isOver_lift`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

instance : MorphismProperty.RespectsRight @IsOpenImmersion @IsOpenImmersion :=
  ⟨fun i hi f hf ↦ by
    have : IsOpenImmersion i := hi
    have : IsOpenImmersion f := hf
    infer_instance⟩

section LiftAlongPartialIso

variable {T X' X : Scheme.{u}} (q : T ⟶ X') (π : X' ⟶ X) (j : T ⟶ X) [IsOpenImmersion j]

/-- A lift `q` of an open immersion `j` along a morphism `π` which is an isomorphism
over the range of `j` factors as an isomorphism followed by the inclusion of the
inverse image of the range of `j`. -/
theorem eq_isoOpensRange_inv_restrict_comp_ι_of_comp (hq : q ≫ π = j)
    (hiso : IsIso (π ∣_ j.opensRange)) :
    q = (j.isoOpensRange.hom ≫ inv (π ∣_ j.opensRange)) ≫ (π ⁻¹ᵁ j.opensRange).ι := by
  have hrange : Set.range q ⊆ ((π ⁻¹ᵁ j.opensRange : X'.Opens) : Set X') := by
    rintro - ⟨t, rfl⟩
    change π (q t) ∈ j.opensRange
    have : π (q t) = j t := by
      rw [← Scheme.Hom.comp_apply, hq]
    rw [this]
    exact ⟨t, rfl⟩
  let q' : T ⟶ (π ⁻¹ᵁ j.opensRange).toScheme :=
    IsOpenImmersion.lift (π ⁻¹ᵁ j.opensRange).ι q (by rwa [Scheme.Opens.range_ι])
  have hq' : q' ≫ (π ⁻¹ᵁ j.opensRange).ι = q := IsOpenImmersion.lift_fac _ _ _
  have hfac : q' ≫ (π ∣_ j.opensRange) = j.isoOpensRange.hom := by
    rw [← cancel_mono j.opensRange.ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hq', hq, Scheme.Hom.isoOpensRange_hom_ι]
  have hq'iso : q' = j.isoOpensRange.hom ≫ inv (π ∣_ j.opensRange) := by
    rw [← hfac, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← hq', hq'iso]

/-- **A lift of an open immersion along a partial isomorphism is an open immersion**:
if `q ≫ π = j` with `j` an open immersion and `π` an isomorphism over the range of
`j`, then `q` is an open immersion. -/
theorem isOpenImmersion_of_comp_of_isIso_restrict (hq : q ≫ π = j)
    (hiso : IsIso (π ∣_ j.opensRange)) : IsOpenImmersion q := by
  rw [eq_isoOpensRange_inv_restrict_comp_ι_of_comp q π j hq hiso]
  infer_instance

/-- **The range of a lift of an open immersion along a partial isomorphism** is the
full inverse image of the range of the open immersion. -/
theorem range_eq_preimage_of_comp_of_isIso_restrict (hq : q ≫ π = j)
    (hiso : IsIso (π ∣_ j.opensRange)) : Set.range q = π ⁻¹' (Set.range j) := by
  have hfac := eq_isoOpensRange_inv_restrict_comp_ι_of_comp q π j hq hiso
  apply subset_antisymm
  · rintro - ⟨t, rfl⟩
    refine Set.mem_preimage.mpr ⟨t, ?_⟩
    rw [← Scheme.Hom.comp_apply, hq]
  · intro x' hx'
    have hx'P : x' ∈ Set.range (π ⁻¹ᵁ j.opensRange).ι := by
      rw [Scheme.Opens.range_ι]
      exact Set.mem_preimage.mp hx'
    obtain ⟨p, rfl⟩ := hx'P
    obtain ⟨t, ht⟩ := (Scheme.homeoOfIso
      (asIso (j.isoOpensRange.hom ≫ inv (π ∣_ j.opensRange)))).surjective p
    refine ⟨t, ?_⟩
    rw [hfac, Scheme.Hom.comp_apply]
    exact congrArg (π ⁻¹ᵁ j.opensRange).ι (by simpa using ht)

end LiftAlongPartialIso

section RestrictOfSection

variable {T X : Scheme.{u}} (ψ : T ⟶ X) (V : X.Opens) (v : V.toScheme ⟶ T)

/-- **A morphism with an open section covering the inverse image is an isomorphism over
the open**: if `v` is an open immersion lifting the inclusion of `V` along `ψ` whose
range is the whole inverse image of `V`, then `ψ` restricts to an isomorphism over `V`.
This produces the isomorphism over `V` of the graph extension of a compactification
(Stacks Project Tag 0F3Z; revised blueprint
`lemma:nagata-scheme-image-partial-section`). -/
theorem isIso_morphismRestrict_of_range_eq [IsOpenImmersion v] (hv : v ≫ ψ = V.ι)
    (hrange : ((ψ ⁻¹ᵁ V : T.Opens) : Set T) = Set.range v) : IsIso (ψ ∣_ V) := by
  -- lift `v` to the inverse image of `V`
  have hsub : Set.range v ⊆ Set.range (ψ ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι]
    exact hrange.ge
  obtain ⟨v', hv'⟩ : ∃ v' : V.toScheme ⟶ (ψ ⁻¹ᵁ V).toScheme, v' ≫ (ψ ⁻¹ᵁ V).ι = v :=
    ⟨IsOpenImmersion.lift (ψ ⁻¹ᵁ V).ι v hsub, IsOpenImmersion.lift_fac _ _ _⟩
  have hOI : IsOpenImmersion (v' ≫ (ψ ⁻¹ᵁ V).ι) := by
    rw [hv']
    infer_instance
  have hOIv' : IsOpenImmersion v' := IsOpenImmersion.of_comp v' (ψ ⁻¹ᵁ V).ι
  -- the lift is surjective, since the range of `v` is the whole inverse image
  have hsurj : Function.Surjective v' := by
    intro w
    have hw : (ψ ⁻¹ᵁ V).ι w ∈ Set.range v := by
      rw [← hrange, ← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    obtain ⟨t, ht⟩ := hw
    refine ⟨t, (ψ ⁻¹ᵁ V).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hv', ht]
  -- a surjective open immersion is an isomorphism, and it inverts `ψ ∣_ V`
  have hepi : Epi v'.base := (TopCat.epi_iff_surjective _).mpr hsurj
  have hIsov' : IsIso v' := IsOpenImmersion.isIso v'
  have hcomp : v' ≫ (ψ ∣_ V) = 𝟙 V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hv', hv,
      Category.id_comp]
  have : IsIso (v' ≫ (ψ ∣_ V)) := by
    rw [hcomp]
    infer_instance
  exact IsIso.of_isIso_comp_left v' (ψ ∣_ V)

end RestrictOfSection

section PullbackRange

/-- **The range of the base change of an open immersion**: in a cartesian square whose
left vertical leg `f` is an open immersion, the parallel leg `snd` has range the inverse
image of the range of `f`. -/
theorem range_snd_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [IsOpenImmersion f] (h : IsPullback fst snd f g) :
    Set.range snd = g ⁻¹' Set.range f := by
  have hsurj : Function.Surjective ⇑h.isoPullback.hom := by
    have := (Scheme.homeoOfIso h.isoPullback).surjective
    rwa [Scheme.coe_homeoOfIso] at this
  have hcomp : snd = h.isoPullback.hom ≫ Limits.pullback.snd f g :=
    (h.isoPullback_hom_snd).symm
  rw [hcomp, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hsurj, Set.image_univ, IsOpenImmersion.range_pullbackSnd]
  rfl

end PullbackRange

section RestrictOfSectionRange

/-- **A partial section identifies an isomorphism locus**: if `m` is an open immersion
whose composite `j := m ≫ ψ` is again an open immersion and whose range is the full
inverse image of the range of `j`, then `ψ` restricts to an isomorphism over the range
of `j`. This is `AlgebraicGeometry.isIso_morphismRestrict_of_range_eq` in the form in
which the modification layer produces its data. -/
theorem isIso_morphismRestrict_opensRange_of_range_eq {W T X : Scheme.{u}} (ψ : T ⟶ X)
    (m : W ⟶ T) [IsOpenImmersion m] [IsOpenImmersion (m ≫ ψ)]
    (hrange : Set.range m = ψ ⁻¹' Set.range (m ≫ ψ)) :
    IsIso (ψ ∣_ (m ≫ ψ).opensRange) := by
  have hsurj : Function.Surjective ⇑(m ≫ ψ).isoOpensRange.inv := by
    have := (Scheme.homeoOfIso (m ≫ ψ).isoOpensRange.symm).surjective
    rwa [Scheme.coe_homeoOfIso] at this
  refine isIso_morphismRestrict_of_range_eq ψ (m ≫ ψ).opensRange
    ((m ≫ ψ).isoOpensRange.inv ≫ m) ?_ ?_
  · rw [Category.assoc]
    exact (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι (m ≫ ψ)).symm
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr hsurj, Set.image_univ, hrange]
    rfl

end RestrictOfSectionRange

/-- An open immersion whose range is an open `B` is an isomorphism onto `B`. -/
lemma exists_isIso_lift_of_mem_iff {Y Z : Scheme.{u}} (m : Z ⟶ Y)
    (hm : IsOpenImmersion m) {B : Y.Opens} (hB : ∀ y, (∃ z, m z = y) ↔ y ∈ B) :
    ∃ m' : Z ⟶ B.toScheme, IsIso m' ∧ m' ≫ B.ι = m := by
  have := hm
  have hsub : Set.range m.base ⊆ Set.range B.ι.base := by
    rintro - ⟨z, rfl⟩
    exact ⟨⟨m z, (hB _).mp ⟨z, rfl⟩⟩, rfl⟩
  refine ⟨IsOpenImmersion.lift B.ι m hsub, ?_, IsOpenImmersion.lift_fac _ _ _⟩
  have hfac : IsOpenImmersion.lift B.ι m hsub ≫ B.ι = m := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (IsOpenImmersion.lift B.ι m hsub) := by
    have h1 : IsOpenImmersion (IsOpenImmersion.lift B.ι m hsub ≫ B.ι) := by
      rw [hfac]; infer_instance
    exact IsOpenImmersion.of_comp _ B.ι
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun t ↦ ?_)
  obtain ⟨z, hz⟩ := (hB t.1).mpr t.2
  refine ⟨z, B.ι.isOpenEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, hfac]
  exact hz

/-- A set in a scheme is closed as soon as its preimage under each member of a jointly
surjective family of open immersions is closed. -/
lemma Scheme.isClosed_of_openCover {Q : Scheme.{u}} {κ : Type*} {Z : κ → Scheme.{u}}
    (q : ∀ k, Z k ⟶ Q) [∀ k, IsOpenImmersion (q k)] (hcov : ∀ x : Q, ∃ k y, q k y = x)
    {s : Set Q} (hs : ∀ k, IsClosed ((q k).base ⁻¹' s)) : IsClosed s :=
  isClosed_of_isOpenEmbedding_cover (fun k ↦ (q k).base)
    (fun k ↦ (q k).isOpenEmbedding) hcov hs
/-! ### Fibre products over disjoint opens -/

section DisjointRange


variable {U X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- If `j` is an open immersion whose range is disjoint from the range of `f`, the fibre
product `V ×_X U` is empty. -/
lemma isEmpty_pullback_of_disjoint_range {V : Scheme.{u}} (f : V ⟶ X) (j : U ⟶ X)
    [IsOpenImmersion j] (h : Set.range f.base ∩ Set.range j.base = ∅) :
    IsEmpty ↥(Limits.pullback f j) := by
  have hr : Set.range (Limits.pullback.fst f j).base = ∅ := by
    rw [IsOpenImmersion.range_pullbackFst]
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hmem : f.base x ∈ Set.range f.base ∩ Set.range j.base := ⟨⟨x, rfl⟩, hx⟩
    rw [h] at hmem
    exact hmem
  exact Set.range_eq_empty_iff.mp hr

end DisjointRange

section LiftOver

variable {S X Y Z : Scheme.{u}} [X.Over S] [Y.Over S] [Z.Over S] (f : X ⟶ Z) (g : Y ⟶ Z)
  [IsOpenImmersion f] [f.IsOver S] [g.IsOver S]

/-- The lift of a morphism of `S`-schemes along an open immersion of `S`-schemes is a morphism
of `S`-schemes. -/
instance IsOpenImmersion.isOver_lift (H : Set.range g ⊆ Set.range f) :
    (IsOpenImmersion.lift f g H).IsOver S :=
  ⟨by rw [← comp_over f S, IsOpenImmersion.lift_fac_assoc, comp_over]⟩

end LiftOver

/-- Let `s : Y ⟶ X` be a section of `p : X ⟶ Y` and let `U` be an open of `X` containing the
image of `s` such that `p ≫ s` restricts to the inclusion on `U`. Then `s` is an open immersion
with image `U`. -/
lemma isOpenImmersion_and_range_eq_of_section {X Y : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ p = 𝟙 Y) (U : X.Opens) (hU : s ⁻¹ᵁ U = ⊤) (hpU : U.ι ≫ p ≫ s = U.ι) :
    IsOpenImmersion s ∧ Set.range s = U := by
  have hrange : Set.range s ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [U.range_ι]
    have hy : y ∈ s ⁻¹ᵁ U := hU ▸ trivial
    exact hy
  have hs' : IsOpenImmersion.lift U.ι s hrange ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  have : IsIso (IsOpenImmersion.lift U.ι s hrange) := by
    refine ⟨U.ι ≫ p, ?_, ?_⟩
    · rw [reassoc_of% hs', hs]
    · rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hs', hpU, Category.id_comp]
  rw [← hs']
  refine ⟨inferInstance, ?_⟩
  rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_comp_of_isIso, U.opensRange_ι]

end AlgebraicGeometry
