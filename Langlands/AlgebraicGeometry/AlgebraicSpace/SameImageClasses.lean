import Langlands.AlgebraicGeometry.AlgebraicSpace.SameImageSpecialization
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-! # Classes of points with the same image under a finite map -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

section Topology

variable {α : Type*} [TopologicalSpace α]

/-- In a Noetherian quasi-sober space, a point in the closure of a locally closed set `H ∩ O`
is a specialization of a point of that set. -/
theorem exists_mem_specializes_of_mem_closure [NoetherianSpace α] [QuasiSober α] {H O : Set α}
    (hH : IsClosed H) (hO : IsOpen O) {x : α} (hx : x ∈ closure (H ∩ O)) :
    ∃ a ∈ H ∩ O, a ⤳ x := by
  classical
  set K := closure (H ∩ O)
  have hex : ∃ n, ∃ S : Finset (Set α), S.card = n ∧ (∀ t ∈ S, IsClosed t ∧ IsIrreducible t) ∧
      K = ⋃₀ (S : Set (Set α)) := by
    obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
      NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_closure (s := H ∩ O))
    refine ⟨hSf.toFinset.card, hSf.toFinset, rfl, fun t ht => ?_, by simpa using hSU⟩
    rw [Set.Finite.mem_toFinset] at ht
    exact ⟨hSc t ht, hSi t ht⟩
  let n := Nat.find hex
  obtain ⟨S, hSn, hS, hSK⟩ := Nat.find_spec hex
  have hxS : x ∈ ⋃₀ (S : Set (Set α)) := hSK ▸ hx
  obtain ⟨Z, hZS, hxZ⟩ := hxS
  obtain ⟨hZc, hZi⟩ := hS Z hZS
  have hgen := hZi.isGenericPoint_genericPoint hZc
  have hζZ : hZi.genericPoint ∈ Z := hgen.mem
  have hKH : K ⊆ H := closure_minimal Set.inter_subset_left hH
  have hZK : Z ⊆ K := by rw [hSK]; exact Set.subset_sUnion_of_mem hZS
  refine ⟨hZi.genericPoint, ⟨hKH (hZK hζZ), ?_⟩, hgen.specializes hxZ⟩
  by_contra hζO
  have hZO : ¬ (Z ∩ O).Nonempty := fun h => hζO ((hgen.mem_open_set_iff hO).mpr h)
  have hsub : H ∩ O ⊆ ⋃₀ ((S.erase Z : Finset (Set α)) : Set (Set α)) := by
    intro a ha
    have haK : a ∈ ⋃₀ (S : Set (Set α)) := hSK ▸ subset_closure ha
    obtain ⟨Z', hZ'S, haZ'⟩ := haK
    refine ⟨Z', ?_, haZ'⟩
    rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff]
    refine ⟨hZ'S, fun hZ' => hZO ⟨a, hZ' ▸ haZ', ha.2⟩⟩
  have hclosed : IsClosed (⋃₀ ((S.erase Z : Finset (Set α)) : Set (Set α))) :=
    (S.erase Z).finite_toSet.isClosed_sUnion fun t ht =>
      (hS t (Finset.mem_of_mem_erase (Finset.mem_coe.mp ht))).1
  have hK' : K = ⋃₀ ((S.erase Z : Finset (Set α)) : Set (Set α)) := by
    apply le_antisymm (closure_minimal hsub hclosed)
    exact (Set.sUnion_mono (Finset.coe_subset.mpr (Finset.erase_subset Z S))).trans
      hSK.symm.subset
  have hlt : (S.erase Z).card < n := by
    show (S.erase Z).card < Nat.find hex
    rw [Finset.card_erase_of_mem hZS, ← hSn]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨Z, hZS⟩) Nat.one_pos
  exact Nat.find_min hex hlt ⟨S.erase Z, rfl, fun t ht => hS t (Finset.mem_of_mem_erase ht), hK'⟩

/-- Existence of a generic class: given an equivalence relation without specializations
inside classes, along which specializations transport, and a finite set `G` of points of
which every point is a specialization, some point of `G` has a class closed under
generization. -/
theorem exists_generic_class [T0Space α] (r : α → α → Prop) (hr : Equivalence r)
    (hdisc : ∀ a b, r a b → a ⤳ b → a = b)
    (htr : ∀ x x' y, r x x' → x ⤳ y → ∃ y', r y y' ∧ x' ⤳ y') {G : Set α}
    (hG : G.Finite) (hGne : G.Nonempty) (hcov : ∀ x, ∃ g ∈ G, g ⤳ x) :
    ∃ γ ∈ G, ∀ a b, a ⤳ b → r b γ → r a γ := by
  let le : α → α → Prop := fun a b => ∃ c, r c b ∧ a ⤳ c
  have le_trans : ∀ a b d, le a b → le b d → le a d := by
    rintro a b d ⟨c, hcb, hac⟩ ⟨e, hed, hbe⟩
    obtain ⟨e', hee', hce'⟩ := htr b c e (hr.symm hcb) hbe
    exact ⟨e', hr.trans (hr.symm hee') hed, hac.trans hce'⟩
  let lt : α → α → Prop := fun a b => le a b ∧ ¬ le b a
  have : IsStrictOrder α lt :=
    { irrefl := fun a h => h.2 h.1
      trans := fun a b c hab hbc =>
        ⟨le_trans a b c hab.1 hbc.1, fun hca => hbc.2 (le_trans c a b hca hab.1)⟩ }
  have hwf : WellFounded (fun a b : G => lt a b) := hG.wellFoundedOn (r := lt)
  obtain ⟨g₀, hg₀⟩ := hGne
  obtain ⟨⟨γ, hγG⟩, -, hγmin'⟩ := hwf.has_min Set.univ ⟨⟨g₀, hg₀⟩, trivial⟩
  have hγmin : ∀ g ∈ G, ¬ lt g γ := fun g hg => hγmin' ⟨g, hg⟩ trivial
  refine ⟨γ, hγG, fun a b hab hbγ => ?_⟩
  obtain ⟨g, hgG, hga⟩ := hcov a
  have hgγ : le g γ := ⟨b, hbγ, hga.trans hab⟩
  have hγg : le γ g := by
    by_contra h
    exact hγmin g hgG ⟨hgγ, h⟩
  obtain ⟨c, hcg, hγc⟩ := hγg
  obtain ⟨a', haa', hca'⟩ := htr g c a (hr.symm hcg) hga
  obtain ⟨b', hbb', ha'b'⟩ := htr a a' b haa' hab
  have hγb' : r γ b' := hr.trans (hr.symm hbγ) hbb'
  have h1 : γ = b' := hdisc γ b' hγb' ((hγc.trans hca').trans ha'b')
  have h2 : a' = γ := ((h1 ▸ ha'b' : a' ⤳ γ).antisymm (hγc.trans hca')).eq
  exact h2 ▸ haa'

end Topology

variable {S : Scheme.{u}} {Y : Presheaf S}

set_option backward.isDefEq.respectTransparency.types false in
/-- Specializations transport along points with the same image under a finite map. -/
theorem SameImage.exists_specializes {U : Over S} {f : (schemeYoneda S).obj U ⟶ Y}
    (hf : IsFinite f) {x x' y : U.left} (h : SameImage f x x') (hxy : x ⤳ y) :
    ∃ y', SameImage f y y' ∧ x' ⤳ y' := by
  have hr : (schemeYoneda S).relativelyRepresentable f := hf.representable
  obtain ⟨r, hrt, hrs⟩ := SameImage₂.exists_pullback hr h
  have ht : _root_.AlgebraicGeometry.IsFinite (hr.snd f).left :=
    hf.projection f (hr.fst f) (hr.snd f) (hr.isPullback f)
  have hcl : IsClosedMap (hr.snd f).left := (hr.snd f).left.isClosedMap
  obtain ⟨r', hrr', hr't⟩ := hcl.specializingMap (hrt ▸ hxy)
  refine ⟨(hr.fst' f).left r', ?_, ?_⟩
  · have := SameImage₂.of_pullback hr r'
    rwa [hr't] at this
  · rw [← hrs]
    exact hrr'.map (hr.fst' f).left.continuous

set_option backward.isDefEq.respectTransparency.types false in
/-- Classes of points with the same image under a finite map are finite. -/
theorem SameImage.finite_class {U : Over S} {f : (schemeYoneda S).obj U ⟶ Y}
    (hf : IsFinite f) (x : U.left) : {x' | SameImage f x x'}.Finite := by
  have hr : (schemeYoneda S).relativelyRepresentable f := hf.representable
  have ht : _root_.AlgebraicGeometry.IsFinite (hr.snd f).left :=
    hf.projection f (hr.fst f) (hr.snd f) (hr.isPullback f)
  refine (((hr.snd f).left.finite_preimage_singleton x).image (hr.fst' f).left).subset ?_
  intro x' hx'
  obtain ⟨r, hrt, hrs⟩ := SameImage₂.exists_pullback hr hx'
  exact ⟨r, hrt, hrs⟩

/-- The saturation of a set of points for a finite map. -/
def saturation {U : Over S} (f : (schemeYoneda S).obj U ⟶ Y) (T : Set U.left) : Set U.left :=
  {x' | ∃ x ∈ T, SameImage f x x'}

theorem subset_saturation {U : Over S} (f : (schemeYoneda S).obj U ⟶ Y) (T : Set U.left) :
    T ⊆ saturation f T :=
  fun x hx => ⟨x, hx, SameImage.refl f x⟩

theorem saturation_saturated {U : Over S} (f : (schemeYoneda S).obj U ⟶ Y) (T : Set U.left)
    {x x' : U.left} (hx : x ∈ saturation f T) (h : SameImage f x x') : x' ∈ saturation f T := by
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨y, hy, hyx.trans h⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The saturation of a closed set for a finite map is closed. -/
theorem isClosed_saturation {U : Over S} {f : (schemeYoneda S).obj U ⟶ Y} (hf : IsFinite f)
    {T : Set U.left} (hT : IsClosed T) : IsClosed (saturation f T) := by
  have hr : (schemeYoneda S).relativelyRepresentable f := hf.representable
  have ht : _root_.AlgebraicGeometry.IsFinite (hr.snd f).left :=
    hf.projection f (hr.fst f) (hr.snd f) (hr.isPullback f)
  have hs : _root_.AlgebraicGeometry.IsFinite (hr.fst' f).left :=
    hf.projection f ((schemeYoneda S).map (hr.snd f)) (hr.fst' f) (hr.isPullback' f).flip
  have heq : saturation f T = (hr.fst' f).left '' ((hr.snd f).left ⁻¹' T) := by
    ext x'
    constructor
    · rintro ⟨x, hx, hxx'⟩
      obtain ⟨r, hrt, hrs⟩ := SameImage₂.exists_pullback hr hxx'
      exact ⟨r, by rw [Set.mem_preimage, hrt]; exact hx, hrs⟩
    · rintro ⟨r, hr', rfl⟩
      exact ⟨_, hr', SameImage₂.of_pullback hr r⟩
  rw [heq]
  exact (hr.fst' f).left.isClosedMap _ (hT.preimage (hr.snd f).left.continuous)

end Langlands.AlgebraicGeometry.AlgebraicSpace
