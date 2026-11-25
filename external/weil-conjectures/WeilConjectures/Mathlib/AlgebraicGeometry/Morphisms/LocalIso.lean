/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Separated local isomorphisms onto an irreducible reduced scheme

Let `p : V ⟶ S` be a separated local isomorphism into an irreducible reduced scheme `S`. Then
`V` is the disjoint union of opens each of which maps isomorphically onto an open of `S`.

The pieces are indexed by the points of `V` over the generic point `η` of `S`: the piece of such
a point `v` consists of all specialisations of `v`. Every point `x` of `V` has a neighbourhood
mapping isomorphically onto an open of `S`; that open contains `η`, so the neighbourhood contains
exactly one point over `η`, which is the unique point of `V` over `η` specialising to `x`. This
shows the pieces are open and partition `V`. Each piece maps injectively to `S`: two local
sections of `p` through points of the same piece agree on a dense open, hence agree by
separatedness of `p` and reducedness of `S`
(`AlgebraicGeometry.ext_of_isDominant_of_isSeparated`).

## Main results

- `AlgebraicGeometry.IsLocalIso.exists_opens_isOpenImmersion`: the decomposition above, with
  nonempty pieces.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace IsLocalIso

/-- A local isomorphism is universally open. -/
instance (priority := 100) universallyOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocalIso f] :
    UniversallyOpen f :=
  have : MorphismProperty.ContainsIdentities @UniversallyOpen := ⟨fun _ ↦ inferInstance⟩
  le_of_isZariskiLocalAtSource @UniversallyOpen _ _ f ‹_›

set_option backward.isDefEq.respectTransparency false in
/-- The stalk maps of a local isomorphism are isomorphisms. -/
instance isIso_stalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocalIso f] (x : X) :
    IsIso (f.stalkMap x) := by
  obtain ⟨U, hxU, hU⟩ := exists_isOpenImmersion (f := f) x
  obtain ⟨y, rfl⟩ : x ∈ Set.range U.ι := by simpa using hxU
  have : IsIso (f.stalkMap (U.ι y) ≫ U.ι.stalkMap y) := by
    rw [← Scheme.Hom.stalkMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (U.ι.stalkMap y)

end IsLocalIso

/-- If `W` is an open of `V` on which `p : V ⟶ S` is an open immersion and `w ∈ W` lies over the
generic point of the irreducible scheme `S`, then `w` specialises to every point of `W`. -/
lemma specializes_of_isOpenImmersion_of_eq_genericPoint {V S : Scheme.{u}} [IrreducibleSpace S]
    (p : V ⟶ S) {W : V.Opens} [IsOpenImmersion (W.ι ≫ p)] {w z : V} (hw : w ∈ W) (hz : z ∈ W)
    (hpw : p w = genericPoint S) : w ⤳ z := by
  have := ((W.ι ≫ p).isOpenEmbedding.isInducing.specializes_iff (x := ⟨w, hw⟩)
    (y := ⟨z, hz⟩)).mp (hpw ▸ genericPoint_specializes (p z))
  simpa using this.map W.ι.continuous

/-- Let `p : V ⟶ S` be separated with `S` irreducible and reduced, and let `W₁, W₂` be opens of `V`
on which `p` is an open immersion. If `W₁` and `W₂` intersect, then `p` is injective on
`W₁ ∪ W₂`; more precisely points `x ∈ W₁` and `y ∈ W₂` with the same image coincide. -/
lemma eq_of_isOpenImmersion_of_inf_nonempty {V S : Scheme.{u}} [IrreducibleSpace S]
    [IsReduced S] (p : V ⟶ S) [IsSeparated p] {W₁ W₂ : V.Opens}
    [IsOpenImmersion (W₁.ι ≫ p)] [IsOpenImmersion (W₂.ι ≫ p)]
    (h : ((W₁ ⊓ W₂ : V.Opens) : Set V).Nonempty) {x y : V} (hx : x ∈ W₁) (hy : y ∈ W₂)
    (hxy : p x = p y) : x = y := by
  have : IsOpenImmersion ((W₁ ⊓ W₂).ι ≫ p) := by
    rw [← Scheme.homOfLE_ι V inf_le_left, Category.assoc]
    infer_instance
  let O : S.Opens := (W₁.ι ≫ p).opensRange ⊓ (W₂.ι ≫ p).opensRange
  let O' : S.Opens := ((W₁ ⊓ W₂).ι ≫ p).opensRange
  have hO' : O' ≤ O := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨⟨a.1, a.2.1⟩, rfl⟩, ⟨a.1, a.2.2⟩, rfl⟩
  let σ₁ := IsOpenImmersion.lift (W₁.ι ≫ p) O.ι
    ((Scheme.Opens.range_ι O).trans_subset fun _ h ↦ h.1)
  let σ₂ := IsOpenImmersion.lift (W₂.ι ≫ p) O.ι
    ((Scheme.Opens.range_ι O).trans_subset fun _ h ↦ h.2)
  let τ := IsOpenImmersion.lift ((W₁ ⊓ W₂).ι ≫ p) O'.ι (by
    rw [Scheme.Opens.range_ι]
    rfl)
  have h₁ : S.homOfLE hO' ≫ σ₁ = τ ≫ V.homOfLE inf_le_left := by
    rw [← cancel_mono (W₁.ι ≫ p)]
    simp only [σ₁, τ, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, Scheme.homOfLE_ι]
  have h₂ : S.homOfLE hO' ≫ σ₂ = τ ≫ V.homOfLE inf_le_right := by
    rw [← cancel_mono (W₂.ι ≫ p)]
    simp only [σ₂, τ, Category.assoc, Scheme.homOfLE_ι_assoc]
    rw [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac, Scheme.homOfLE_ι]
  have : IsDominant (S.homOfLE hO') := by
    have : PreirreducibleSpace O := O.ι.isOpenEmbedding.preirreducibleSpace
    obtain ⟨v, hv⟩ := h
    have : Nonempty O' := ⟨⟨p v, ⟨v, hv⟩, rfl⟩⟩
    exact ⟨(S.homOfLE hO').isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩
  have hσ : σ₁ ≫ W₁.ι = σ₂ ≫ W₂.ι := by
    refine ext_of_isDominant_of_isSeparated p (by simp [σ₁, σ₂]) (S.homOfLE hO') ?_
    rw [reassoc_of% h₁, reassoc_of% h₂, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  have hpx : p x ∈ O := ⟨⟨⟨x, hx⟩, rfl⟩, ⟨y, hy⟩, hxy.symm⟩
  have e₁ : σ₁ ⟨p x, hpx⟩ = ⟨x, hx⟩ :=
    (W₁.ι ≫ p).isOpenEmbedding.injective
      congr($(IsOpenImmersion.lift_fac (W₁.ι ≫ p) O.ι _) ⟨p x, hpx⟩)
  have e₂ : σ₂ ⟨p x, hpx⟩ = ⟨y, hy⟩ :=
    (W₂.ι ≫ p).isOpenEmbedding.injective
      (congr($(IsOpenImmersion.lift_fac (W₂.ι ≫ p) O.ι _) ⟨p x, hpx⟩).trans hxy)
  calc x = W₁.ι (σ₁ ⟨p x, hpx⟩) := by rw [e₁, Scheme.Opens.ι_apply]
    _ = W₂.ι (σ₂ ⟨p x, hpx⟩) := congr($hσ ⟨p x, hpx⟩)
    _ = y := by rw [e₂, Scheme.Opens.ι_apply]

/-- A separated local isomorphism `p : V ⟶ S` into an irreducible reduced scheme `S` is a
disjoint union of open immersions: there is a family of nonempty, pairwise disjoint opens
`U i` of `V` covering `V` such that each `(U i).ι ≫ p` is an open immersion. -/
theorem IsLocalIso.exists_opens_isOpenImmersion {V S : Scheme.{u}} [IrreducibleSpace S]
    [IsReduced S] (p : V ⟶ S) [IsLocalIso p] [IsSeparated p] :
    ∃ (ι : Type u) (U : ι → V.Opens), (∀ i, (U i : Set V).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧ (⨆ i, U i) = ⊤ ∧
      ∀ i, IsOpenImmersion ((U i).ι ≫ p) := by
  choose W hxW hW using IsLocalIso.exists_isOpenImmersion (f := p)
  -- every chart contains a point over the generic point
  have hη (x : V) : ∃ w ∈ W x, p w = genericPoint S := by
    obtain ⟨⟨w, hw⟩, hw'⟩ : genericPoint S ∈ ((W x).ι ≫ p).opensRange :=
      ((genericPoint_spec S).mem_open_set_iff ((W x).ι ≫ p).opensRange.isOpen).mpr
        ⟨p x, trivial, ⟨x, hxW x⟩, rfl⟩
    exact ⟨w, hw, hw'⟩
  have key {v x z : V} (hv : p v = genericPoint S) (hvx : v ⤳ x) (hz : z ∈ W x) : v ⤳ z :=
    specializes_of_isOpenImmersion_of_eq_genericPoint p (hvx.mem_open (W x).isOpen (hxW x)) hz hv
  have uniq {v v' x : V} (hv : p v = genericPoint S) (hv' : p v' = genericPoint S) (h : v ⤳ x)
      (h' : v' ⤳ x) : v = v' :=
    eq_of_isOpenImmersion_of_inf_nonempty p (W₁ := W x) (W₂ := W x) ⟨x, hxW x, hxW x⟩
      (h.mem_open (W x).isOpen (hxW x)) (h'.mem_open (W x).isOpen (hxW x)) (hv.trans hv'.symm)
  -- the piece of a point `v` over the generic point consists of its specialisations
  let U (v : {v : V // p v = genericPoint S}) : V.Opens := ⟨{x | v.1 ⤳ x}, by
    rw [isOpen_iff_forall_mem_open]
    exact fun x hx ↦ ⟨W x, fun z hz ↦ key v.2 hx hz, (W x).isOpen, hxW x⟩⟩
  refine ⟨{v : V // p v = genericPoint S}, U, fun v ↦ ⟨v, specializes_rfl⟩, ?_, ?_, ?_⟩
  · intro i j hij
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hi, hj⟩
    exact (hij (Subtype.ext (uniq i.2 j.2 hi hj))).elim
  · refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨w, hw, hpw⟩ := hη x
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨⟨w, hpw⟩, specializes_of_isOpenImmersion_of_eq_genericPoint p hw (hxW x) hpw⟩
  · intro v
    have hinj : Function.Injective ((U v).ι ≫ p) := by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      exact Subtype.ext (eq_of_isOpenImmersion_of_inf_nonempty p
        ⟨v, ha.mem_open (W a).isOpen (hxW a), hb.mem_open (W b).isOpen (hxW b)⟩
        (hxW a) (hxW b) hab)
    have (x : (U v).toScheme) : IsIso (((U v).ι ≫ p).stalkMap x) := by
      rw [Scheme.Hom.stalkMap_comp]
      set_option backward.isDefEq.respectTransparency false in infer_instance
    exact IsOpenImmersion.of_isIso_stalkMap _ (.of_continuous_injective_isOpenMap
      (Scheme.Hom.continuous _) hinj (Scheme.Hom.isOpenMap _))

end AlgebraicGeometry
