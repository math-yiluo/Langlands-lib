/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.TransportLeftNaturality

/-!
# Saturation of descent orbits

Source: Stacks Project, Tags 03JE and 0H8K.
(blueprint: lem-pd-descent-orbit-saturated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- The orbit of a point in the cartesian groupoid associated to a descent datum is saturated.
Source: Stacks Project, Tag 03JE, orbit used in the first two paragraphs of the proof;
Tag 0H8K, identification of the cartesian groupoid of a descent datum.
(blueprint: lem-pd-descent-orbit-saturated).

Proof: The universal transport gives the target t on R = V ×_Y X. Naturality and the
identity and cocycle laws give the identity, inverse and composition of this groupoid.
For a point r of R, if s(r) is in the orbit of v, choose an arrow from v to s(r).
The residue fields of that arrow and r have a common field extension over the residue
field of s(r): their tensor product is nonzero, and a prime quotient embeds in its
fraction field. Thus they lift to composable geometric arrows. Composition gives an
arrow from v to t(r), proving t(r) is in the orbit. Applying the inverse gives the
converse. The argument works for nonclosed points and inseparable extensions, since
it uses field tensor products rather than rational points. -/
theorem descent_orbit_saturated
    {X Y R : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    (D : Over.DescentDatum p V) (s : R ⟶ V.left) (q : R ⟶ X) (t : R ⟶ V.left)
    (hsq : IsPullback s q (V.hom ≫ p) p)
    (ht : (D.transport (s ≫ V.hom) q
      (by simpa only [Category.assoc] using hsq.w) (Over.homMk s)).left = t)
    (v : V.left) :
    s ⁻¹' (t '' (s ⁻¹' {v})) = t ⁻¹' (t '' (s ⁻¹' {v})) := by
  classical
  have htq : t ≫ V.hom = q := by
    rw [← ht]
    exact Over.w _
  have hp : (s ≫ V.hom) ≫ p = q ≫ p := by
    simpa only [Category.assoc] using hsq.w
  let a₀ : Over.mk (s ≫ V.hom) ⟶ V := Over.homMk s
  have composition {W : Scheme.{u}} (g₁ g₂ : W ⟶ R) (he : g₁ ≫ t = g₂ ≫ s) :
      ∃ c : W ⟶ R, c ≫ s = g₁ ≫ s ∧ c ≫ t = g₂ ≫ t := by
    have hm : g₁ ≫ q = g₂ ≫ (s ≫ V.hom) := by
      rw [← htq, ← Category.assoc, he, Category.assoc]
    have h₁ : (g₁ ≫ (s ≫ V.hom)) ≫ p = (g₁ ≫ q) ≫ p := by
      simp only [Category.assoc, hp]
    have h₂ : (g₁ ≫ q) ≫ p = (g₂ ≫ q) ≫ p := by
      rw [hm]
      simp only [Category.assoc, hp]
    let b₁ : Over.mk (g₁ ≫ (s ≫ V.hom)) ⟶ V :=
      Over.homMk (g₁ ≫ s) (by simp only [Category.assoc]; rfl)
    let b₂ : Over.mk (g₁ ≫ q) ⟶ V := Over.homMk (g₂ ≫ s) (by
      rw [Category.assoc, ← hm]; rfl)
    have hn₁ : D.transport _ _ h₁ b₁ = b₂ := by
      ext
      have hn := transport_left_naturality D g₁ (s ≫ V.hom) q hp a₀
        _ _ h₁ b₁ rfl rfl rfl
      rw [ht] at hn
      exact hn.trans he
    have hn₂ : (D.transport _ _ h₂ b₂).left = g₂ ≫ t := by
      rw [← ht]
      exact transport_left_naturality D g₂ (s ≫ V.hom) q hp a₀
        _ _ h₂ b₂ hm rfl rfl
    let c := hsq.lift (g₁ ≫ s) (g₂ ≫ q) (by
      simpa only [Category.assoc] using h₁.trans h₂)
    have hcs : c ≫ s = g₁ ≫ s := hsq.lift_fst _ _ _
    have hcq : c ≫ q = g₂ ≫ q := hsq.lift_snd _ _ _
    refine ⟨c, hcs, ?_⟩
    have hcn : (D.transport _ _ (h₁.trans h₂) b₁).left = c ≫ t := by
      rw [← ht]
      apply transport_left_naturality D c (s ≫ V.hom) q hp a₀
      · rw [← Category.assoc, ← Category.assoc, hcs]
      · exact hcq.symm
      · exact hcs.symm
    rw [← hcn, ← D.transport_transport _ _ _ h₁ h₂, hn₁]
    exact hn₂
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
  have forward : ∀ r : R, s r ∈ t '' (s ⁻¹' {v}) → t r ∈ t '' (s ⁻¹' {v}) := by
    intro r hr
    obtain ⟨r₀, hr₀, he⟩ := hr
    obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := t) (g := s)
      r₀ r he
    obtain ⟨c, hcs, hct⟩ := composition (pullback.fst t s) (pullback.snd t s)
      (pullback.condition (f := t) (g := s))
    refine ⟨c z, ?_, ?_⟩
    · change s (c z) = v
      have hc := congrArg (fun f ↦ f z) hcs
      simp only [Scheme.Hom.comp_apply, hz₁] at hc
      exact hc.trans hr₀
    · have hc := congrArg (fun f ↦ f z) hct
      simpa only [Scheme.Hom.comp_apply, hz₂] using hc
  ext r
  constructor
  · exact forward r
  · intro hr
    have hr' : s (i r) ∈ t '' (s ⁻¹' {v}) := by
      have hi := congrArg (fun f ↦ f r) his
      simpa only [Scheme.Hom.comp_apply] using hi.symm ▸ hr
    have hr'' := forward (i r) hr'
    have hi := congrArg (fun f ↦ f r) hit
    simp only [Scheme.Hom.comp_apply] at hi
    change s r ∈ t '' (s ⁻¹' {v})
    rw [← hi]
    exact hr''

end CategoryTheory.Over.DescentDatum
