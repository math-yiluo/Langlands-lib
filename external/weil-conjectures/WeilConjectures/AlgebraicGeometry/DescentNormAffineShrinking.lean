/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.DescentNormLocusAffine
import WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated
import WeilConjectures.AlgebraicGeometry.TransportLeftNaturality

/-!
# Norm shrinking around finite saturated sets

Source: Stacks Project, Tag 03JE.
(blueprint: lem-pd-descent-norm-affine-shrinking).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

private theorem descent_inversion
    {X Y R : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    (D : Over.DescentDatum p V) (s : R ⟶ V.left) (q : R ⟶ X) (t : R ⟶ V.left)
    (hsq : IsPullback s q (V.hom ≫ p) p)
    (ht : (D.transport (s ≫ V.hom) q
      (by simpa only [Category.assoc] using hsq.w) (Over.homMk s)).left = t)
    : ∃ i : R ⟶ R, IsIso i ∧ i ≫ s = t ∧ i ≫ t = s := by
  have htq : t ≫ V.hom = q := by
    rw [← ht]
    exact Over.w _
  have hp : (s ≫ V.hom) ≫ p = q ≫ p := by
    simpa only [Category.assoc] using hsq.w
  let a₀ : Over.mk (s ≫ V.hom) ⟶ V := Over.homMk s
  let i := hsq.lift t (s ≫ V.hom) (by
    rw [← Category.assoc, htq]
    exact hp.symm)
  have his : i ≫ s = t := hsq.lift_fst _ _ _
  have hiq : i ≫ q = s ≫ V.hom := hsq.lift_snd _ _ _
  have hit : i ≫ t = s := by
    let b : Over.mk q ⟶ V := Over.homMk t htq
    have hb : D.transport (s ≫ V.hom) q hp a₀ = b := by
      ext
      exact ht
    have hn : (D.transport q (s ≫ V.hom) hp.symm b).left = i ≫ t := by
      rw [← ht]
      apply transport_left_naturality D i (s ≫ V.hom) q hp a₀
      · rw [← Category.assoc, his, htq]
      · exact hiq.symm
      · exact his.symm
    rw [← hn, ← hb, D.transport_transport, D.transport_self]
    rfl
  have hii : i ≫ i = 𝟙 R := by
    apply hsq.hom_ext
    · simp only [Category.assoc, his, hit, Category.id_comp]
    · rw [Category.assoc, hiq, ← Category.assoc, his, htq, Category.id_comp]
  have : IsIso i := ⟨⟨i, hii, hii⟩⟩
  exact ⟨i, inferInstance, his, hit⟩

/-- A finite saturated set contained in an affine open admits an invariant affine shrinking.
Source: Stacks Project, Tag 03JE, proof after the choice of the affine open W.
(blueprint: lem-pd-descent-norm-affine-shrinking).

Proof: The transport datum makes (R,s,t) a cartesian groupoid. The source s is the
base change of p. Inversion exchanges s and t, so both are finite locally free.
Let Z = t(s⁻¹(V \ A)). This is closed, and its complement W is invariant, is
contained in A, and contains S: saturation prevents an arrow from S to outside A.
Prime avoidance (00DS) gives f on A with S ⊆ D(f) ⊆ W. On s⁻¹(W), t factors through
A. Form g = Norm_s(t* f) on W. The norm criterion says g is nonzero at w exactly
when f is nonzero at every target of an arrow starting at w. This includes every
point of S, by saturation. It is an invariant condition by inverse and composition,
and the identity arrow gives D(g) ⊆ D(f). The restriction of g to the affine D(f)
has the same nonvanishing locus, so D(g) is affine. Take U = D(g); then U ⊆ A and
s⁻¹(U) = t⁻¹(U). For S empty one can take the empty affine open, including when R
and V are empty. No global degree bound is used: the norm is defined for a finite
locally free morphism of locally varying rank. -/
theorem exists_descent_norm_affine_shrinking
    {X Y R : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    (D : Over.DescentDatum p V) (s : R ⟶ V.left) (q : R ⟶ X) (t : R ⟶ V.left)
    (hsq : IsPullback s q (V.hom ≫ p) p)
    (ht : (D.transport (s ≫ V.hom) q
      (by simpa only [Category.assoc] using hsq.w) (Over.homMk s)).left = t)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p]
    (S : Set V.left) (hS : S.Finite) (hstable : s ⁻¹' S = t ⁻¹' S)
    (A : V.left.Opens) (hA : IsAffineOpen A) (hSA : S ⊆ A) :
    ∃ U : V.left.Opens, S ⊆ U ∧ IsAffineOpen U ∧ U ≤ A ∧ s ⁻¹' (U : Set V.left) =
      t ⁻¹' (U : Set V.left) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hSne
  · exact ⟨⊥, by simp, isAffineOpen_bot _, bot_le, by simp⟩
  obtain ⟨i, hi, his, hit⟩ := descent_inversion D s q t hsq ht
  have : IsFinite s := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip
    inferInstance
  have : Flat s := MorphismProperty.of_isPullback (P := @Flat) hsq.flip inferInstance
  have : LocallyOfFinitePresentation s := MorphismProperty.of_isPullback
    (P := @LocallyOfFinitePresentation) hsq.flip inferInstance
  have : IsFinite t := by rw [← his]; infer_instance
  have : Flat t := by rw [← his]; infer_instance
  have : LocallyOfFinitePresentation t := by rw [← his]; infer_instance
  let e := hsq.lift (𝟙 V.left) V.hom (by simp)
  have hes : e ≫ s = 𝟙 V.left := hsq.lift_fst _ _ _
  have heq : e ≫ q = V.hom := hsq.lift_snd _ _ _
  have het : e ≫ t = 𝟙 V.left := by
    have h₀ : (s ≫ V.hom) ≫ p = q ≫ p := by
      simpa only [Category.assoc] using hsq.w
    have he₁ : V.hom = e ≫ (s ≫ V.hom) := by
      rw [← Category.assoc, hes, Category.id_comp]
    have hn := transport_left_naturality D e (s ≫ V.hom) q h₀ (Over.homMk s)
      V.hom V.hom rfl (Over.homMk (𝟙 V.left)) he₁ heq.symm hes.symm
    rw [ht] at hn
    simpa only [D.transport_self, Over.homMk_left] using hn.symm
  have hes_apply (x : V.left) : s (e x) = x := by
    simpa using congrArg (fun f : V.left ⟶ V.left ↦ f x) hes
  have het_apply (x : V.left) : t (e x) = x := by
    simpa using congrArg (fun f : V.left ⟶ V.left ↦ f x) het
  have his_apply (r : R) : s (i r) = t r := by
    simpa using congrArg (fun f : R ⟶ V.left ↦ f r) his
  have hit_apply (r : R) : t (i r) = s r := by
    simpa using congrArg (fun f : R ⟶ V.left ↦ f r) hit
  let orbit (x : V.left) : Set V.left := t '' (s ⁻¹' {x})
  have hrefl (x : V.left) : x ∈ orbit x := ⟨e x, hes_apply x, het_apply x⟩
  have horbit (r : R) : orbit (s r) = orbit (t r) := by
    have h₁ := descent_orbit_saturated D s q t hsq ht (s r)
    have h₂ := descent_orbit_saturated D s q t hsq ht (t r)
    have hts : t r ∈ orbit (s r) := ⟨r, rfl, rfl⟩
    have hst : s r ∈ orbit (t r) := by
      have he := Set.ext_iff.mp h₂ r
      exact he.mpr (hrefl (t r))
    apply Set.Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      have he := Set.ext_iff.mp h₂ z
      apply he.mp
      change s z ∈ orbit (t r)
      exact hz ▸ hst
    · rintro x ⟨z, hz, rfl⟩
      have he := Set.ext_iff.mp h₁ z
      apply he.mp
      change s z ∈ orbit (s r)
      exact hz ▸ hts
  have interior (B : V.left.Opens) :
      ∃ W : V.left.Opens,
        (W : Set V.left) = (t '' (s ⁻¹' (B : Set V.left)ᶜ))ᶜ ∧
        W ≤ B ∧ s ⁻¹' (W : Set V.left) = t ⁻¹' (W : Set V.left) := by
    let W : V.left.Opens := ⟨(t '' (s ⁻¹' (B : Set V.left)ᶜ))ᶜ,
      (t.isClosedMap _ (B.isOpen.isClosed_compl.preimage s.continuous)).isOpen_compl⟩
    have hmem (x : V.left) : x ∈ W ↔ orbit x ⊆ B := by
      constructor
      · intro hx y hy
        obtain ⟨r, hr, rfl⟩ := hy
        by_contra hn
        apply hx
        exact ⟨i r, by simpa only [Set.mem_preimage, his_apply, Set.mem_compl_iff] using hn,
          (hit_apply r).trans hr⟩
      · intro hx ⟨r, hr, htr⟩
        apply hr
        apply hx
        exact ⟨i r, (his_apply r).trans htr, hit_apply r⟩
    refine ⟨W, rfl, fun x hx ↦ (hmem x).mp hx (hrefl x), ?_⟩
    ext r
    change s r ∈ W ↔ t r ∈ W
    rw [hmem, hmem, horbit r]
  obtain ⟨W, hWset, hWA, hWstable⟩ := interior A
  have hSW : S ⊆ W := by
    intro x hx
    rw [hWset]
    rintro ⟨r, hr, htr⟩
    have htrS : t r ∈ S := htr.symm ▸ hx
    have hsrS : s r ∈ S := (Set.ext_iff.mp hstable r).mpr htrS
    exact hr (hSA hsrS)
  obtain ⟨f, hSf, hfW⟩ := hA.exists_basicOpen_le_of_finite hWA hS hSW
  obtain ⟨U, hUset, hUf, hUstable⟩ := interior (V.left.basicOpen f)
  have hSU : S ⊆ U := by
    intro x hx
    rw [hUset]
    rintro ⟨r, hr, htr⟩
    have htrS : t r ∈ S := htr.symm ▸ hx
    have hsrS : s r ∈ S := (Set.ext_iff.mp hstable r).mpr htrS
    exact hr (hSf hsrS)
  refine ⟨U, hSU, ?_, hUf.trans (V.left.basicOpen_le f), hUstable⟩
  have hex : t '' (s ⁻¹' (V.left.basicOpen f : Set V.left)ᶜ) =
      s '' (t ⁻¹' (V.left.basicOpen f : Set V.left)ᶜ) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨i r, by simpa only [Set.mem_preimage, hit_apply] using hr, his_apply r⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨i r, by simpa only [Set.mem_preimage, his_apply] using hr, hit_apply r⟩
  refine isAffineOpen_descent_norm_locus s t A hA W ?_ f hfW U hUf ?_
  · intro r hr
    exact hWA ((Set.ext_iff.mp hWstable r).mp hr)
  · rw [← hex, ← hUset]
    exact (Set.inter_eq_right.mpr (hUf.trans hfW)).symm


end CategoryTheory.Over.DescentDatum
