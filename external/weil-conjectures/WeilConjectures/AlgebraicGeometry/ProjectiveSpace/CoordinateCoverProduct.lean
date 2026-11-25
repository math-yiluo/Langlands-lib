/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateCover
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Products of coordinate covers

A coordinate cover of a scheme `X` (`AlgebraicGeometry.Scheme.CoordinateCover`) is an invertible
module `L` with trivialising sections `Tᵢ` written in terms of their ratios `Tⱼ / Tᵢ`. The tensor
product of finitely many such modules `L_a` with the products `⊗ₐ T_{a, J a}` of the trivialising
sections is again a coordinate cover, indexed by the families `J`; its charts are the
intersections `⋂ₐ U_{a, J a}`.

This is the construction behind Stacks, Tag 09NC: if every point of a quasi-compact scheme lies
in an affine chart of one of finitely many coordinate covers, the tensor product of these covers,
restricted to the charts meeting an affine chart, is a coordinate cover by affine charts, i.e. an
ample invertible module.

## Main definitions

- `AlgebraicGeometry.Scheme.CoordinateCover.pi`: the product of finitely many coordinate covers.
- `AlgebraicGeometry.Scheme.CoordinateCover.restrict`: the coordinate cover formed by a family of
  charts that still covers `X`.
- `AlgebraicGeometry.Scheme.CoordinateCover.ofPair`: the coordinate cover with two charts.

## Main statements

- `AlgebraicGeometry.Scheme.CoordinateCover.isAffineOpen_inf`: an affine open meets a chart in an
  affine open.
- `AlgebraicGeometry.Scheme.CoordinateCover.exists_isAffineOpen_of_iSup_eq_top`: finitely many
  coordinate covers with distinguished affine charts covering `X` give a coordinate cover by
  affine charts (Stacks, Tag 09NC).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- Membership in a finite infimum of opens. -/
lemma Scheme.mem_iInf_opens_of_finite {X : Scheme.{u}} {α : Type*} [Finite α] (U : α → X.Opens)
    (x : X) : x ∈ ⨅ a, U a ↔ ∀ a, x ∈ U a := by
  rw [← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter]
  rfl

namespace Scheme.CoordinateCover

variable {X : Scheme.{u}}

section Pi

variable {α : Type u} [Fintype α] {ι : α → Type u} (𝒟 : ∀ a, X.CoordinateCover (ι a))

/-- The product of finitely many coordinate covers `𝒟 a`, the tensor product of the underlying
invertible modules with the products of the trivialising sections: its charts are the
intersections `⋂ₐ U_{a, J a}` and its ratios the products of the ratios. -/
def pi : X.CoordinateCover (∀ a, ι a) where
  U J := ⨅ a, (𝒟 a).U (J a)
  ratio J J' := ∏ a, X.presheaf.map (homOfLE (iInf_le (fun a ↦ (𝒟 a).U (J a)) a)).op
    ((𝒟 a).ratio (J a) (J' a))
  ratio_self J := by simp [CoordinateCover.ratio_self]
  basicOpen_ratio J J' := by
    rw [Scheme.basicOpen_prod]
    apply SetLike.coe_injective
    simp only [Finset.mem_univ, iInf_true, Scheme.basicOpen_res, (𝒟 _).basicOpen_ratio,
      Opens.coe_inf, Opens.coe_iInf]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, SetLike.mem_coe]
    exact ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun a ↦ (h₂ a).2.2⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, fun a ↦ ⟨h₁, h₁ a, h₂ a⟩⟩⟩
  ratio_mul J J' J'' := by
    simp only [map_prod, Scheme.presheaf_map_map, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ ↦ ?_
    have hJ : (⨅ b, (𝒟 b).U (J b)) ⊓ ⨅ b, (𝒟 b).U (J' b) ≤ (𝒟 a).U (J a) ⊓ (𝒟 a).U (J' a) :=
      inf_le_inf (iInf_le _ a) (iInf_le _ a)
    have := congrArg (X.presheaf.map (homOfLE hJ).op) ((𝒟 a).ratio_mul (J a) (J' a) (J'' a))
    simp only [map_mul, Scheme.presheaf_map_map] at this
    exact this
  iSup_U := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    have h (a : α) : ∃ i, x ∈ (𝒟 a).U i :=
      Opens.mem_iSup.mp ((𝒟 a).iSup_U.ge (Set.mem_univ x))
    choose J hJ using h
    exact Opens.mem_iSup.mpr ⟨J, (Scheme.mem_iInf_opens_of_finite _ x).mpr hJ⟩

lemma pi_U (J : ∀ a, ι a) : (pi 𝒟).U J = ⨅ a, (𝒟 a).U (J a) := rfl

end Pi

section Restrict

variable {ι : Type u} (𝒟 : X.CoordinateCover ι)

/-- The coordinate cover formed by the charts `U_i`, `i ∈ s`, of a coordinate cover, provided
that they still cover `X`. -/
def restrict (s : Set ι) (hs : ⨆ i : s, 𝒟.U i = ⊤) : X.CoordinateCover s where
  U i := 𝒟.U i
  ratio i j := 𝒟.ratio i j
  ratio_self i := 𝒟.ratio_self i
  basicOpen_ratio i j := 𝒟.basicOpen_ratio i j
  ratio_mul i j l := 𝒟.ratio_mul i j l
  iSup_U := hs

lemma restrict_U (s : Set ι) (hs : ⨆ i : s, 𝒟.U i = ⊤) (i : s) :
    (𝒟.restrict s hs).U i = 𝒟.U i := rfl

/-- An affine open meets a chart of a coordinate cover in an affine open: on an affine scheme
the non-vanishing locus of a section of an invertible module is affine. -/
lemma isAffineOpen_inf {Y : X.Opens} (hY : IsAffineOpen Y) (l : ι) :
    IsAffineOpen (Y ⊓ 𝒟.U l) := by
  let S : Set Γ(X, Y) := {r | ∃ i, X.basicOpen r ≤ 𝒟.U i}
  have hS : Ideal.span S = ⊤ := by
    rw [← hY.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (𝒟.iSup_U.ge (Set.mem_univ x))
    obtain ⟨r, hr, hrx⟩ := hY.exists_basicOpen_le ⟨x, hi⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨r, i, hr⟩, hrx⟩
  refine isAffineOpen_of_isAffineOpen_basicOpen (Y ⊓ 𝒟.U l)
    (X.presheaf.map (homOfLE inf_le_left).op '' S) ?_ ?_
  · rw [← Ideal.map_span, hS, Ideal.map_top]
  · rintro _ ⟨r, ⟨i, hi⟩, rfl⟩
    have hle : X.basicOpen r ≤ 𝒟.U i := hi
    have e : X.basicOpen (X.presheaf.map (homOfLE (inf_le_left : Y ⊓ 𝒟.U l ≤ Y)).op r) =
        X.basicOpen (X.presheaf.map (homOfLE hle).op (𝒟.ratio i l)) := by
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res, 𝒟.basicOpen_ratio]
      exact le_antisymm
        (le_inf inf_le_right (le_inf (inf_le_right.trans hle) (inf_le_left.trans inf_le_right)))
        (le_inf (le_inf (inf_le_left.trans (X.basicOpen_le r)) (inf_le_right.trans inf_le_right))
          inf_le_left)
    rw [e]
    exact (hY.basicOpen r).basicOpen _

end Restrict

section OfPair

variable {U₀ U₁ : X.Opens} (a : Γ(X, U₀)) (b : Γ(X, U₁))

/-- The charts of a coordinate cover with two charts. -/
def pairU (U₀ U₁ : X.Opens) : ULift.{u} Bool → X.Opens
  | ⟨false⟩ => U₀
  | ⟨true⟩ => U₁

/-- The ratios of a coordinate cover with two charts. -/
def pairRatio : (i j : ULift.{u} Bool) → Γ(X, pairU U₀ U₁ i)
  | ⟨false⟩, ⟨false⟩ => (1 : Γ(X, pairU U₀ U₁ ⟨false⟩))
  | ⟨false⟩, ⟨true⟩ => a
  | ⟨true⟩, ⟨false⟩ => b
  | ⟨true⟩, ⟨true⟩ => (1 : Γ(X, pairU U₀ U₁ ⟨true⟩))

/-- The coordinate cover with two charts `U₀, U₁` and ratios `a ∈ Γ(U₀)`, `b ∈ Γ(U₁)` which are
inverse to each other on `U₀ ∩ U₁` and whose basic opens are `U₀ ∩ U₁`. -/
def ofPair (ha : X.basicOpen a = U₀ ⊓ U₁) (hb : X.basicOpen b = U₀ ⊓ U₁)
    (hab : X.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op a *
      X.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op b = 1)
    (hcov : U₀ ⊔ U₁ = ⊤) : X.CoordinateCover (ULift.{u} Bool) where
  U := pairU U₀ U₁
  ratio := pairRatio a b
  ratio_self i := by rcases i with ⟨_ | _⟩ <;> rfl
  basicOpen_ratio i j := by
    rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
    · simp [pairRatio, pairU]
    · exact ha
    · rw [inf_comm]
      exact hb
    · simp [pairRatio, pairU]
  ratio_mul i j l := by
    have hab' := congrArg (X.presheaf.map (homOfLE (le_of_eq (inf_comm U₁ U₀))).op) hab
    simp only [map_mul, map_one, Scheme.presheaf_map_map] at hab'
    rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩ <;> rcases l with ⟨_ | _⟩ <;>
      simp only [pairRatio, map_one, one_mul, mul_one]
    · exact hab.symm
    · rw [mul_comm]
      exact hab'.symm
  iSup_U := by
    rw [← hcov]
    refine le_antisymm (iSup_le fun i ↦ ?_) (sup_le (le_iSup (pairU U₀ U₁) ⟨false⟩)
      (le_iSup (pairU U₀ U₁) ⟨true⟩))
    rcases i with ⟨_ | _⟩
    · exact le_sup_left
    · exact le_sup_right

lemma ofPair_U_false (ha hb hab hcov) : (ofPair a b ha hb hab hcov).U ⟨false⟩ = U₀ := rfl

lemma ofPair_U_true (ha hb hab hcov) : (ofPair a b ha hb hab hcov).U ⟨true⟩ = U₁ := rfl

end OfPair

/-- **Coordinate covers by affine charts from distinguished affine charts** (Stacks, Tag 09NC).
Let `𝒟 a`, `a ∈ α` finite, be coordinate covers of `X` with distinguished charts `U_{a, o a}`
which are affine and cover `X`. Then `X` has a coordinate cover by finitely many affine charts,
namely the charts `⋂_b U_{b, J b}` of the product cover with `J a = o a` for some `a`. -/
theorem exists_isAffineOpen_of_iSup_eq_top {α : Type u} [Finite α] {ι : α → Type u}
    [∀ a, Finite (ι a)] (𝒟 : ∀ a, X.CoordinateCover (ι a)) (o : ∀ a, ι a)
    (ho : ∀ a, IsAffineOpen ((𝒟 a).U (o a))) (hcov : ⨆ a, (𝒟 a).U (o a) = ⊤) :
    ∃ (β : Type u) (_ : Finite β) (𝒟' : X.CoordinateCover β), ∀ i, IsAffineOpen (𝒟'.U i) := by
  classical
  have := Fintype.ofFinite α
  let s : Set (∀ a, ι a) := {J | ∃ a, J a = o a}
  have hs : ⨆ J : s, (pi 𝒟).U J = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ x))
    have h (b : α) : ∃ i, x ∈ (𝒟 b).U i :=
      Opens.mem_iSup.mp ((𝒟 b).iSup_U.ge (Set.mem_univ x))
    choose J hJ using h
    let J' : ∀ b, ι b := Function.update J a (o a)
    have hJ' (b : α) : x ∈ (𝒟 b).U (J' b) := by
      by_cases hb : b = a
      · subst hb
        simpa [J'] using ha
      · simpa [J', Function.update_of_ne hb] using hJ b
    exact Opens.mem_iSup.mpr ⟨⟨J', a, by simp [J']⟩,
      (Scheme.mem_iInf_opens_of_finite _ x).mpr hJ'⟩
  refine ⟨s, inferInstance, (pi 𝒟).restrict s hs, fun J ↦ ?_⟩
  obtain ⟨J, a, hJa⟩ := J
  rw [restrict_U, pi_U]
  -- `⋂_b U_{b, J b} = U_{a, o a} ∩ ⋂_b U_{b, J b}` is affine by induction on the factors
  have key (t : Finset α) : IsAffineOpen ((𝒟 a).U (o a) ⊓ t.inf fun b ↦ (𝒟 b).U (J b)) := by
    induction t using Finset.induction_on with
    | empty => simpa using ho a
    | insert b t hb ih =>
      rw [Finset.inf_insert, inf_left_comm, inf_comm]
      exact (𝒟 b).isAffineOpen_inf ih (J b)
  have e : (⨅ b, (𝒟 b).U (J b)) = (𝒟 a).U (o a) ⊓ Finset.univ.inf fun b ↦ (𝒟 b).U (J b) := by
    rw [Finset.inf_univ_eq_iInf, inf_eq_right.mpr (hJa ▸ iInf_le _ a)]
  rw [e]
  exact key _

end Scheme.CoordinateCover

end AlgebraicGeometry
