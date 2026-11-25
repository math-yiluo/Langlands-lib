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
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.DescentOrbitSaturated
import WeilConjectures.AlgebraicGeometry.TransportLeftNaturality
import WeilConjectures.AlgebraicGeometry.DescentNormAffineShrinking

/-!
# Invariant affine neighbourhoods for finite locally free descent

Source: Stacks Project, Groupoid Schemes, Tags 0H8K and 03JE; Algebra, Tag 00DS.
(blueprint: lem-pd-invariant-affine-neighbourhoods).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Every point has an affine neighbourhood invariant under transport, lying over an affine
open of the base. Source: Stacks Project, Tags 0H8K, 03JE and 00DS.
(blueprint: lem-pd-invariant-affine-neighbourhoods).

Proof: Choose an affine neighbourhood B of the image of v in Y and restrict X and V
above B. The transport defines a groupoid on V; both projections are finite locally
free because they are base changes of p. The orbit of v is therefore finite. By hV it
lies in an affine open A. Intersect with the inverse image of B and use finite prime
avoidance (00DS) to choose a principal affine neighbourhood of the orbit within A.
Apply the invariant-neighbourhood construction of 03JE to the restricted groupoid:
remove the closed saturation of the complement of A, choose a function nonzero on
the finite orbit, and take the nonvanishing locus of its norm along the finite locally
free projection. This is an invariant affine neighbourhood U of v inside A, hence
inside the inverse image of B. Invariance for the universal groupoid arrows implies
invariance for every transported T-point by naturality. The empty V case is vacuous;
no global bound on the degree of p is needed since the construction is local on B. -/
theorem exists_invariant_affine_neighbourhood
    {X Y : Scheme.{u}} {p : X ⟶ Y} [IsFinite p] [Flat p]
    [LocallyOfFinitePresentation p] [Surjective p] {V : Over X}
    (hV : ∀ s : Set V.left, s.Finite → ∃ U : V.left.Opens, IsAffineOpen U ∧ s ⊆ U)
    (D : Over.DescentDatum p V) (v : V.left) :
    ∃ U : V.left.Opens, v ∈ U ∧ IsAffineOpen U ∧
      (∃ B : Y.Opens, IsAffineOpen B ∧ U ≤ (V.hom ≫ p) ⁻¹ᵁ B) ∧
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
        (a : Over.mk f₁ ⟶ V), Set.range a.left ⊆ U →
          Set.range (D.transport f₁ f₂ h a).left ⊆ U := by
  let s := Limits.pullback.fst (V.hom ≫ p) p
  let q := Limits.pullback.snd (V.hom ≫ p) p
  have hsq : IsPullback s q (V.hom ≫ p) p := IsPullback.of_hasPullback _ _
  let a₀ : Over.mk (s ≫ V.hom) ⟶ V := Over.homMk s
  have h₀ : (s ≫ V.hom) ≫ p = q ≫ p := by
    simpa only [Category.assoc] using hsq.w
  let t : Limits.pullback (V.hom ≫ p) p ⟶ V.left := (D.transport (s ≫ V.hom) q h₀ a₀).left
  let S : Set V.left := t '' (s ⁻¹' {v})
  have hS : S.Finite := (s.finite_preimage_singleton v).image t
  have hstable : s ⁻¹' S = t ⁻¹' S := descent_orbit_saturated D s q t hsq rfl v
  let e : V.left ⟶ Limits.pullback (V.hom ≫ p) p :=
    Limits.pullback.lift (𝟙 V.left) V.hom (by simp)
  have hes : e ≫ s = 𝟙 V.left := by simp [e, s]
  have heq : e ≫ q = V.hom := by simp [e, q]
  have het : e ≫ t = 𝟙 V.left := by
    have he₁ : V.hom = e ≫ (s ≫ V.hom) := by
      rw [← Category.assoc, hes, Category.id_comp]
    have hn := transport_left_naturality D e (s ≫ V.hom) q h₀ a₀
      V.hom V.hom rfl (Over.homMk (𝟙 V.left)) he₁ heq.symm hes.symm
    simpa only [D.transport_self, Over.homMk_left] using hn.symm
  have hvS : v ∈ S := by
    refine ⟨e v, ?_, ?_⟩
    · change s (e v) = v
      simpa only [Scheme.Hom.comp_apply, Scheme.Hom.id_base, TopCat.id_app] using
        congrArg (fun f : V.left ⟶ V.left ↦ f v) hes
    · simpa only [Scheme.Hom.comp_apply, Scheme.Hom.id_base, TopCat.id_app] using
        congrArg (fun f : V.left ⟶ V.left ↦ f v) het
  have htbase : t ≫ V.hom ≫ p = s ≫ V.hom ≫ p := by
    rw [← Category.assoc,
      show t ≫ V.hom = q from Over.w (D.transport (s ≫ V.hom) q h₀ a₀)]
    simpa only [Category.assoc] using h₀.symm
  obtain ⟨B, hB, hvB, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y) (U := ⊤) (x := (V.hom ≫ p) v) (by trivial)
  obtain ⟨A, hA, hSA⟩ := hV S hS
  have hSB : S ⊆ (V.hom ≫ p) ⁻¹ᵁ B := by
    rintro w ⟨r, hr, rfl⟩
    change p (V.hom (t r)) ∈ B
    have heval := congrArg (fun f ↦ f r) htbase
    simp only [Scheme.Hom.comp_apply] at heval
    rw [heval]
    have hr' : s r = v := hr
    rw [hr']
    exact hvB
  obtain ⟨f, hSf, hf⟩ := hA.exists_basicOpen_le_of_finite
    (O := A ⊓ (V.hom ≫ p) ⁻¹ᵁ B) inf_le_left hS (fun w hw ↦ ⟨hSA hw, hSB hw⟩)
  obtain ⟨U, hSU, hU, hUf, hInv⟩ := exists_descent_norm_affine_shrinking
    D s q t hsq rfl S hS hstable (V.left.basicOpen f) (hA.basicOpen f) hSf
  refine ⟨U, hSU hvS, hU, ⟨B, hB, hUf.trans (hf.trans inf_le_right)⟩, ?_⟩
  intro T f₁ f₂ h a ha
  let g : T ⟶ Limits.pullback (V.hom ≫ p) p := Limits.pullback.lift a.left f₂ (by
    rw [← Category.assoc, Over.w a]; exact h)
  have hgs : g ≫ s = a.left := by simp [g, s]
  have hgq : g ≫ q = f₂ := by simp [g, q]
  have hgt : g ≫ t = (D.transport f₁ f₂ h a).left := by
    have hg₁ : f₁ = g ≫ (s ≫ V.hom) := by
      rw [← Category.assoc, hgs, Over.w a]
      rfl
    exact (transport_left_naturality D g (s ≫ V.hom) q h₀ a₀
      f₁ f₂ h a hg₁ hgq.symm hgs.symm).symm
  rintro w ⟨z, rfl⟩
  have hz : s (g z) ∈ U := by
    rw [← Scheme.Hom.comp_apply, hgs]
    exact ha ⟨z, rfl⟩
  have hz' : t (g z) ∈ U := by
    change g z ∈ t ⁻¹' (U : Set V.left)
    exact (Set.ext_iff.mp hInv (g z)).mp hz
  have heval := congrArg (fun f ↦ f z) hgt
  rw [Scheme.Hom.comp_apply] at heval
  exact heval ▸ hz'

end CategoryTheory.Over.DescentDatum
