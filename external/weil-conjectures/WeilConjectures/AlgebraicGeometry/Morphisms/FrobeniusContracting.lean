/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius

/-!
# The relative Frobenius contracts the local ring at a fixed rational point

Let `X₀` be a scheme over a finite field `k₀` with `q` elements, let `S = X₀ ×_{k₀} k` be a base
change to a field `k`, with projections `p: S ⟶ X₀` and `a: S ⟶ Spec k`, and let `h` be a
`k`-endomorphism of `S` lifting a `q ^ m`-power Frobenius `G` of `X₀` (`h ≫ p = p ≫ G`), with
`m ≥ 1`. If `x` is a `k`-rational point of `S` fixed by `h`, then the stalk map of `h` at `x`
sends the maximal ideal `𝔪` of `𝒪_{S,x}` into `𝔪 ^ 2`: in affine coordinates,
`h^♯ (t - t(x)) = (t - t(x)) ^ (q ^ m)`.

The proof is a computation with points: the two morphisms
`Spec (𝒪_{S,x} / 𝔪²) ⟶ S` given by `𝒪_{S,x} --h^♯--> 𝒪_{S,x} ⟶ 𝒪_{S,x} / 𝔪²` and by
`𝒪_{S,x} ⟶ k ⟶ 𝒪_{S,x} / 𝔪²` agree after composition with `p` (the `q ^ m`-power map kills
`𝔪 / 𝔪²`, and `x` is fixed) and with `a` (both are `k`-morphisms), hence agree.

## Main statements

- `AlgebraicGeometry.map_maximalIdeal_stalkMap_le_sq_of_isFrobenius`: the stalk map of `h` at a
  fixed rational point sends `𝔪` into `𝔪 ^ 2`.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀]

/-- On a ring over a finite field `k₀`, the `#k₀ ^ m`-power map is a ring endomorphism. -/
lemma exists_ringHom_pow_card_pow {R : CommRingCat.{u}} (g : Spec R ⟶ Spec (.of k₀)) (m : ℕ) :
    ∃ χ : R ⟶ R, ∀ r, χ.hom r = r ^ Nat.card k₀ ^ m := by
  obtain ⟨ψ, hψ, -⟩ := exists_specMap_pow_comp g
  refine ⟨CommRingCat.ofHom (ψ.hom ^ m), fun r ↦ ?_⟩
  change (ψ.hom ^ m) r = _
  rw [RingHom.coe_pow]
  induction m with
  | zero => simp
  | succ n ihn => rw [Function.iterate_succ_apply', ihn, hψ, ← pow_mul, ← pow_succ]

/-- A ring homomorphism out of a field into a nontrivial ring is local. -/
lemma isLocalHom_of_field {K R : Type*} [Field K] [CommRing R] [Nontrivial R] (f : K →+* R) :
    IsLocalHom f := by
  refine ⟨fun a ha ↦ ?_⟩
  by_cases h : a = 0
  · rw [h, map_zero] at ha
    exact absurd ha not_isUnit_zero
  · exact isUnit_iff_ne_zero.mpr h

variable {k : Type u} [Field k] {S X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
  {a : S ⟶ Spec (.of k)} {p : S ⟶ X₀} {σ : Spec (.of k) ⟶ Spec (.of k₀)}

/-- **A lift of a Frobenius contracts the local ring at a fixed rational point**: let `S = X₀ ×_{k₀}
k` with projections
`p`, `a`, let `h` be a `k`-endomorphism of `S` with `h ≫ p = p ≫ G` for a `#k₀ ^ m`-power Frobenius
`G` of `X₀`, `m ≥ 1`, and let `x` be a `k`-rational point of `S` fixed by `h`. Then the stalk map
of `h` at `x` sends the maximal ideal of `𝒪_{S,x}` into its square. -/
theorem map_maximalIdeal_stalkMap_le_sq_of_isFrobenius (hp : IsPullback p a f₀ σ)
    {G : X₀ ⟶ X₀} {m : ℕ} (hm : 1 ≤ m) (hG : G.IsFrobenius (Nat.card k₀ ^ m)) {h : S ⟶ S}
    (ha : h ≫ a = a) (hh : h ≫ p = p ≫ G) (x : Spec (.of k) ⟶ S) (hxa : x ≫ a = 𝟙 _)
    (hx : x ≫ h = x) (z : Spec (.of k)) :
    (maximalIdeal (S.presheaf.stalk (h.base (x.base z)))).map (h.stalkMap (x.base z)).hom ≤
      maximalIdeal (S.presheaf.stalk (x.base z)) ^ 2 := by
  obtain rfl : z = closedPoint k := Subsingleton.elim _ _
  -- notation
  let y := x.base (closedPoint k)
  let R := S.presheaf.stalk y
  let t := S.fromSpecStalk y
  let g := h.stalkMap y
  let I : Ideal R := maximalIdeal R ^ 2
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
    (Ideal.pow_le_self two_ne_zero)
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  let T : CommRingCat.{u} := .of (R ⧸ I)
  have : IsLocalRing T :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let π : R ⟶ T := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have : IsLocalHom π.hom := isLocalHom_of_le_jacobson_bot I (by
    rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact Ideal.pow_le_self two_ne_zero)
  -- the structure map `α: k ⟶ R` and the evaluation `ev: R ⟶ k` at `x`
  let α : CommRingCat.of k ⟶ R := Spec.preimage (t ≫ a)
  have hα : Spec.map α = t ≫ a := Spec.map_preimage _
  let ev : R ⟶ CommRingCat.of k := Scheme.stalkClosedPointTo x
  have hev : Spec.map ev ≫ t = x := Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have hαev : α ≫ ev = 𝟙 _ := Spec.map_injective (by
    rw [Spec.map_comp, hα, reassoc_of% hev, hxa, Spec.map_id])
  have hαev' (c : k) : ev.hom (α.hom c) = c := by
    rw [← CommRingCat.comp_apply, hαev, CommRingCat.id_apply]
  let ι : CommRingCat.of k ⟶ T := α ≫ π
  have : IsLocalHom ι.hom := isLocalHom_of_field _
  have : IsLocalHom ev.hom := Scheme.isLocalHom_stalkClosedPointTo x
  have : IsLocalHom (ev ≫ ι).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  have : IsLocalHom (g ≫ π).hom := by
    rw [CommRingCat.hom_comp]; infer_instance
  -- the `q ^ m`-power maps
  obtain ⟨χR, hχR⟩ := exists_ringHom_pow_card_pow (t ≫ p ≫ f₀) m
  obtain ⟨χT, hχT⟩ := exists_ringHom_pow_card_pow (Spec.map π ≫ t ≫ p ≫ f₀) m
  obtain ⟨χk, hχk⟩ := exists_ringHom_pow_card_pow (x ≫ p ≫ f₀) m
  have hQ : 2 ≤ Nat.card k₀ ^ m :=
    (Nat.le_self_pow (by omega) _).trans' (Finite.one_lt_card (α := k₀))
  have hadd (u v : T) :
      (u + v) ^ Nat.card k₀ ^ m = u ^ Nat.card k₀ ^ m + v ^ Nat.card k₀ ^ m := by
    rw [← hχT, ← hχT, ← hχT, map_add]
  -- the ring identity `π ∘ χ_R = ι ∘ χ_k ∘ ev`
  have hring : χR ≫ π = ev ≫ χk ≫ ι := by
    ext r
    change π.hom (χR.hom r) = π.hom (α.hom (χk.hom (ev.hom r)))
    have he : r - α.hom (ev.hom r) ∈ maximalIdeal R := by
      by_contra hne
      have hu : IsUnit (ev.hom (r - α.hom (ev.hom r))) :=
        IsUnit.map ev.hom (not_not.mp ((mem_maximalIdeal _).not.mp hne))
      rw [map_sub, hαev', sub_self] at hu
      exact not_isUnit_zero hu
    have hzero : π.hom ((r - α.hom (ev.hom r)) ^ Nat.card k₀ ^ m) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.pow_le_pow_right hQ (Ideal.pow_mem_pow he _))
    calc π.hom (χR.hom r)
        = (π.hom (α.hom (ev.hom r)) + π.hom (r - α.hom (ev.hom r))) ^ Nat.card k₀ ^ m := by
          rw [hχR, map_pow, ← map_add, add_sub_cancel]
      _ = π.hom (α.hom (ev.hom r)) ^ Nat.card k₀ ^ m +
            π.hom ((r - α.hom (ev.hom r)) ^ Nat.card k₀ ^ m) := by
          rw [hadd, map_pow π.hom (r - _)]
      _ = π.hom (α.hom (χk.hom (ev.hom r))) := by
          rw [hzero, add_zero, hχk, map_pow, map_pow]
  -- the two morphisms `Spec T ⟶ S` agree
  have h₁ : Spec.map (g ≫ π) ≫ S.fromSpecStalk (h.base y) = Spec.map π ≫ t ≫ h := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h₂ : Spec.map (ev ≫ ι) ≫ t = Spec.map ι ≫ x := by
    rw [Spec.map_comp, Category.assoc, hev]
  have hmaps : Spec.map (g ≫ π) ≫ S.fromSpecStalk (h.base y) =
      Spec.map (ev ≫ ι) ≫ S.fromSpecStalk y := by
    refine hp.hom_ext ?_ ?_
    · change (Spec.map (g ≫ π) ≫ S.fromSpecStalk (h.base y)) ≫ p =
        (Spec.map (ev ≫ ι) ≫ t) ≫ p
      rw [h₁, h₂]
      calc (Spec.map π ≫ t ≫ h) ≫ p = Spec.map π ≫ (t ≫ p) ≫ G := by
            simp only [Category.assoc, hh]
        _ = Spec.map (χR ≫ π) ≫ t ≫ p := by
            rw [hG (t ≫ p) χR hχR, Spec.map_comp]; simp only [Category.assoc]
        _ = Spec.map ι ≫ Spec.map χk ≫ (Spec.map ev ≫ t) ≫ p := by
            rw [hring]; simp only [Spec.map_comp, Category.assoc]
        _ = Spec.map ι ≫ (x ≫ p) ≫ G := by
            rw [hev, hG (x ≫ p) χk hχk]
        _ = (Spec.map ι ≫ x) ≫ p := by
            rw [Category.assoc x, ← hh, ← Category.assoc x, hx, Category.assoc]
    · change (Spec.map (g ≫ π) ≫ S.fromSpecStalk (h.base y)) ≫ a =
        (Spec.map (ev ≫ ι) ≫ t) ≫ a
      rw [h₁, h₂]
      simp only [Category.assoc, ha, hxa, Category.comp_id]
      rw [← hα, ← Spec.map_comp]
  -- conclusion
  have heq := (SpecToEquivOfLocalRing S T).symm.injective
    (a₁ := ⟨h.base y, g ≫ π, inferInstance⟩) (a₂ := ⟨y, ev ≫ ι, inferInstance⟩) hmaps
  obtain ⟨h₁, hfg⟩ := SpecToEquivOfLocalRing_eq_iff.mp heq
  replace hfg : g ≫ π = (S.presheaf.stalkCongr (.of_eq h₁)).hom ≫ ev ≫ ι := hfg
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change (g ≫ π).hom r = 0
  rw [hfg, CommRingCat.comp_apply, CommRingCat.comp_apply]
  have hr' : (S.presheaf.stalkCongr (.of_eq h₁)).hom.hom r ∈ maximalIdeal R :=
    map_nonunit _ r hr
  have hev0 : ev.hom ((S.presheaf.stalkCongr (.of_eq h₁)).hom.hom r) = 0 := by
    have := map_nonunit ev.hom _ hr'
    rwa [maximalIdeal_eq_bot, Ideal.mem_bot] at this
  rw [hev0, map_zero]

end AlgebraicGeometry
