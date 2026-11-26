import Langlands.HarmonicAnalysis.Distribution.TopologicalSupport
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Conjugation-invariant distributions on an algebra with support near a compact set

Let `A` be a topological ring, for instance a finite-dimensional associative algebra over a
nonarchimedean local field with its module topology, regarded as the Lie algebra of its unit
group `Aˣ`. The unit group acts on `A` by conjugation `X ↦ u X u⁻¹`, the adjoint action
(`conjugationHomeomorph`, equal to Mathlib's action `ConjAct.toConjAct u • X`).

For a subset `ω` of `A` this module defines

* the saturation `ω^G = ⋃_u u ω u⁻¹` (`conjugationSaturation`);
* the conjugation-invariant distributions (`IsConjugationInvariant`, `conjugationInvariant`):
  `D (f ∘ Ad u) = D f` for every unit `u` and every Schwartz–Bruhat function `f`;
* the space `J(ω)` of conjugation-invariant distributions supported in the closure of `ω^G`
  (`invariantSupportedIn`), the support condition being the Library's annihilator condition
  `Distribution.supportedOn`; on a locally profinite `A` it is equivalent to the inclusion of
  the topological support `Distribution.support` (`mem_invariantSupportedIn_iff_support`).

Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups* (notes by
DeBacker and Sally, 1999), Introduction, printed pp. 1–2: `ᵡT(f) = T(fˣ)` with
`fˣ(X) = f(x.X)`, invariance `ˣT = T`, `ω^G = ⋃_x Ad(x)ω` and
`J(ω) = {T ∈ J : Supp(T) ⊆ cl(ω^G)}`.
-/

noncomputable section

open Topology

namespace Langlands.HarmonicAnalysis.UnitConjugation

universe v

variable {A : Type v} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

/-! ### The conjugation action -/

/-- Conjugation `X ↦ u X u⁻¹` by a unit `u` of `A`, as a homeomorphism of `A`: the adjoint
action of `Aˣ` on its Lie algebra `A`. -/
def conjugationHomeomorph (u : Aˣ) : A ≃ₜ A where
  toFun X := (u : A) * X * ((u⁻¹ : Aˣ) : A)
  invFun X := ((u⁻¹ : Aˣ) : A) * X * (u : A)
  left_inv X := by
    simp only [mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one]
  right_inv X := by
    simp only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]
  continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const

@[simp]
theorem conjugationHomeomorph_apply (u : Aˣ) (X : A) :
    conjugationHomeomorph u X = (u : A) * X * ((u⁻¹ : Aˣ) : A) := rfl

@[simp]
theorem conjugationHomeomorph_symm_apply (u : Aˣ) (X : A) :
    (conjugationHomeomorph u).symm X = ((u⁻¹ : Aˣ) : A) * X * (u : A) := rfl

/-- The homeomorphism is Mathlib's conjugation action of the units of `A` on `A`. -/
theorem conjugationHomeomorph_eq_smul (u : Aˣ) (X : A) :
    conjugationHomeomorph u X = ConjAct.toConjAct u • X := by
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  rfl

theorem conjugationHomeomorph_one (X : A) : conjugationHomeomorph (1 : Aˣ) X = X := by
  simp

theorem conjugationHomeomorph_mul (u w : Aˣ) (X : A) :
    conjugationHomeomorph (u * w) X = conjugationHomeomorph u (conjugationHomeomorph w X) := by
  simp only [conjugationHomeomorph_apply, Units.val_mul, mul_inv_rev, mul_assoc]

theorem conjugationHomeomorph_symm (u : Aˣ) (X : A) :
    (conjugationHomeomorph u).symm X = conjugationHomeomorph u⁻¹ X := by
  simp

/-! ### Saturation -/

/-- The saturation `ω^G = ⋃_{u ∈ Aˣ} u ω u⁻¹` of a subset of `A` under conjugation. -/
def conjugationSaturation (ω : Set A) : Set A :=
  ⋃ u : Aˣ, conjugationHomeomorph u '' ω

theorem mem_conjugationSaturation_iff {ω : Set A} {Y : A} :
    Y ∈ conjugationSaturation ω ↔ ∃ u : Aˣ, ∃ X ∈ ω, (u : A) * X * ((u⁻¹ : Aˣ) : A) = Y := by
  simp [conjugationSaturation]

theorem subset_conjugationSaturation (ω : Set A) : ω ⊆ conjugationSaturation ω := fun X hX =>
  mem_conjugationSaturation_iff.2 ⟨1, X, hX, by simp⟩

theorem conjugationHomeomorph_mem_conjugationSaturation {ω : Set A} (u : Aˣ) {X : A}
    (hX : X ∈ ω) : conjugationHomeomorph u X ∈ conjugationSaturation ω :=
  mem_conjugationSaturation_iff.2 ⟨u, X, hX, rfl⟩

theorem conjugationSaturation_mono {ω ω' : Set A} (h : ω ⊆ ω') :
    conjugationSaturation ω ⊆ conjugationSaturation ω' :=
  Set.iUnion_mono fun _ => Set.image_mono h

/-! ### Invariant distributions -/

/-- A distribution on `A` is invariant under conjugation by `Aˣ`: its pushforward along every
conjugation is itself, that is `D (f ∘ Ad u) = D f` for every unit `u` and test function `f`
(`isConjugationInvariant_iff`). -/
def IsConjugationInvariant (D : Distribution A) : Prop :=
  ∀ u : Aˣ, Distribution.pushforward (conjugationHomeomorph u) D = D

theorem isConjugationInvariant_iff (D : Distribution A) :
    IsConjugationInvariant D ↔
      ∀ (u : Aˣ) (f : SchwartzBruhat A),
        D (Hecke.TestFunction.pullback (conjugationHomeomorph u) f) = D f := by
  constructor
  · intro h u f
    exact congrArg (fun E : Distribution A => E f) (h u)
  · intro h u
    ext f
    exact h u f

/-- The conjugation-invariant distributions on `A`, as a complex subspace of all
distributions (Harish-Chandra's `J`). -/
def conjugationInvariant : Submodule ℂ (Distribution A) where
  carrier := {D | IsConjugationInvariant D}
  zero_mem' u := map_zero _
  add_mem' {D E} hD hE u := by
    change Distribution.pushforward (conjugationHomeomorph u) (D + E) = D + E
    rw [map_add, hD u, hE u]
  smul_mem' c D hD u := by
    change Distribution.pushforward (conjugationHomeomorph u) (c • D) = c • D
    rw [map_smul, hD u]

@[simp]
theorem mem_conjugationInvariant_iff (D : Distribution A) :
    D ∈ conjugationInvariant ↔ IsConjugationInvariant D := Iff.rfl

/-- Harish-Chandra's space `J(ω)`: the conjugation-invariant distributions on `A` supported in
the closure of the saturation `ω^G`. Support is the Library's annihilator condition: `D f = 0`
for every test function `f` vanishing on `cl(ω^G)`. -/
def invariantSupportedIn (ω : Set A) : Submodule ℂ (Distribution A) :=
  conjugationInvariant ⊓ Distribution.supportedOn (closure (conjugationSaturation ω))

theorem mem_invariantSupportedIn_iff (ω : Set A) (D : Distribution A) :
    D ∈ invariantSupportedIn ω ↔
      IsConjugationInvariant D ∧
        ∀ f : SchwartzBruhat A, (∀ Y ∈ closure (conjugationSaturation ω), f Y = 0) →
          D f = 0 :=
  Iff.rfl

theorem invariantSupportedIn_mono {ω ω' : Set A} (h : ω ⊆ ω') :
    invariantSupportedIn ω ≤ invariantSupportedIn ω' :=
  inf_le_inf_left _ (Distribution.supportedOn_mono
    (closure_mono (conjugationSaturation_mono h)))

/-- On a locally profinite `A` the support condition of `J(ω)` is Harish-Chandra's: the
topological support `Distribution.support D` lies in the closure of `ω^G`. -/
theorem mem_invariantSupportedIn_iff_support [T2Space A] [LocallyCompactSpace A]
    [TotallyDisconnectedSpace A] (ω : Set A) (D : Distribution A) :
    D ∈ invariantSupportedIn ω ↔
      IsConjugationInvariant D ∧
        Distribution.support D ⊆ closure (conjugationSaturation ω) := by
  rw [Distribution.support_subset_iff_mem_supportedOn isClosed_closure]
  exact Iff.rfl

end Langlands.HarmonicAnalysis.UnitConjugation
