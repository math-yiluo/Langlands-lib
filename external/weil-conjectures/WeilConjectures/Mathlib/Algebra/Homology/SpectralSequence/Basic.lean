/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Convergence of a first quadrant cohomological spectral sequence

Mathlib knows about spectral sequences (`CategoryTheory.SpectralSequence`) but has no notion of
convergence or of an abutment. This file adds the little that the Grothendieck and
Čech-to-derived spectral sequences need.

For a first quadrant cohomological spectral sequence `E` starting at the `E₂`-page (that is, a
term of `CategoryTheory.E₂CohomologicalSpectralSequenceNat C`) both differentials into and out of
the spot `(p, q)` vanish as soon as `r > max p (q + 1)`, so the objects `(E.page r).X (p, q)`
become constant. `SpectralSequence.pageInfinity` picks out this stable value at the explicit
page `p + q + 2`; no degeneration hypothesis is needed.

`SpectralSequence.Abutment E H` then bundles the data that the image filtration of a first
quadrant double complex produces: a decreasing filtration
`H n = F⁰ ⊇ F¹ ⊇ ⋯ ⊇ Fⁿ ⊇ Fⁿ⁺¹ = 0` of the `n`-th graded piece of the abutment by subobjects,
together with isomorphisms `Fᵖ / Fᵖ⁺¹ ≅ E∞^{p, q}` for `p + q = n`. Since the filtration and
the isomorphisms are genuine data, this is a structure; the `Prop`-valued statement used in the
theorems that consume it is `SpectralSequence.AbutsTo E H`, its `Nonempty`.

## Main definitions

- `CategoryTheory.SpectralSequence.pageInfinity`: the `E∞`-term of a first quadrant
  cohomological spectral sequence, as the stable value of the pages.
- `CategoryTheory.SpectralSequence.Abutment`: a filtration of a graded object exhibiting it as
  the abutment of a first quadrant cohomological spectral sequence.
- `CategoryTheory.SpectralSequence.AbutsTo`: the associated `Prop`.
- `CategoryTheory.SpectralSequence.Abutment.ofIso`: transport of an abutment along isomorphisms
  of graded objects.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The `E∞`-term of a first quadrant cohomological spectral sequence at the spot `(p, q)`.

In the first quadrant both differentials into and out of `(p, q)` vanish on the `r`-th page as
soon as `r > max p (q + 1)`, so the objects `(E.page r).X (p, q)` are canonically isomorphic for
all large `r`; we read off this stable value on the page `p + q + 2`. -/
noncomputable def SpectralSequence.pageInfinity (E : E₂CohomologicalSpectralSequenceNat C)
    (pq : ℕ × ℕ) : C :=
  (E.page (pq.1 + pq.2 + 2 : ℕ)).X pq

/-- The data exhibiting the `ℕ`-graded object `H` of `C` as the abutment of the first quadrant
cohomological spectral sequence `E`: a decreasing filtration of each `H n` by subobjects, which
is exhaustive (`F⁰ = ⊤`) and separated in the strong first quadrant sense (`Fⁿ⁺¹ = ⊥`), whose
successive quotients are the `E∞`-terms of total degree `n`. This is the filtration that the
image filtration on the total complex of a first quadrant double complex produces.

(blueprint: `det-def-groth-ss`) -/
structure SpectralSequence.Abutment (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C) where
  /-- The `p`-th step of the decreasing filtration of `H n`. -/
  filtration (n p : ℕ) : Subobject (H n)
  /-- The filtration is decreasing. -/
  filtration_succ_le (n p : ℕ) : filtration n (p + 1) ≤ filtration n p
  /-- The filtration is exhaustive. -/
  filtration_zero (n : ℕ) : filtration n 0 = ⊤
  /-- The filtration is separated: in the first quadrant it stops in degree `n`. -/
  filtration_succ_self (n : ℕ) : filtration n (n + 1) = ⊥
  /-- The successive quotients of the filtration are the `E∞`-terms. -/
  nonempty_gradedIso (n p q : ℕ) (hpq : p + q = n) :
    Nonempty (cokernel (Subobject.ofLE _ _ (filtration_succ_le n p)) ≅ E.pageInfinity (p, q))

/-- A first quadrant cohomological spectral sequence `E` *abuts to* the `ℕ`-graded object `H`
if there exists a `SpectralSequence.Abutment E H`, that is, a finite decreasing filtration of
each `H n` whose successive quotients are the `E∞`-terms `E∞^{p, q}` with `p + q = n`. -/
def SpectralSequence.AbutsTo (E : E₂CohomologicalSpectralSequenceNat C) (H : ℕ → C) : Prop :=
  Nonempty (E.Abutment H)

namespace SpectralSequence

variable {E : E₂CohomologicalSpectralSequenceNat C} {H H' : ℕ → C}

/-- Transport of an abutment along isomorphisms `H n ≅ H' n`: the filtration of `H' n` is the
image of the filtration of `H n`. -/
noncomputable def Abutment.ofIso (A : E.Abutment H) (e : ∀ n, H n ≅ H' n) : E.Abutment H' where
  filtration n p := Subobject.mk ((A.filtration n p).arrow ≫ (e n).hom)
  filtration_succ_le n p :=
    Subobject.mk_le_mk_of_comm (Subobject.ofLE _ _ (A.filtration_succ_le n p)) (by simp)
  filtration_zero n := by
    rw [A.filtration_zero]
    exact Subobject.mk_eq_top_of_isIso _
  filtration_succ_self n := by
    rw [A.filtration_succ_self, Subobject.mk_eq_bot_iff_zero, Subobject.bot_arrow, zero_comp]
  nonempty_gradedIso n p q hpq := by
    obtain ⟨i⟩ := A.nonempty_gradedIso n p q hpq
    refine ⟨cokernel.mapIso _ _ (Subobject.underlyingIso _) (Subobject.underlyingIso _) ?_ ≪≫ i⟩
    simp [← cancel_mono ((A.filtration n p).arrow ≫ (e n).hom)]

/-- Abutting to a graded object is invariant under isomorphisms of graded objects. -/
lemma AbutsTo.of_iso (h : E.AbutsTo H) (e : ∀ n, H n ≅ H' n) : E.AbutsTo H' :=
  ⟨h.some.ofIso e⟩

/-- Convergence of a spectral sequence is invariant under (unspecified) isomorphisms of the
abutment. -/
lemma AbutsTo.of_nonempty_iso (h : E.AbutsTo H) (e : ∀ n, Nonempty (H n ≅ H' n)) :
    E.AbutsTo H' :=
  h.of_iso fun n ↦ (e n).some

end SpectralSequence

section PageInduction

variable {κ : Type*} {c : ℤ → ComplexShape κ} {r₀ : ℤ}

/-- **Page induction.** A morphism of spectral sequences which is an isomorphism on the first
page `r₀` is an isomorphism on every page: the `(r + 1)`-th page is the homology of the `r`-th
one, compatibly with the morphism.

(blueprint: `lem-sp-page-induction`) -/
theorem SpectralSequence.Hom.isIso_hom {E E' : SpectralSequence C c r₀} (φ : E ⟶ E')
    (h : IsIso (φ.hom r₀)) (r : ℤ) (hr : r₀ ≤ r) : IsIso (φ.hom r) := by
  induction r, hr using Int.leInduction with
  | base => exact h
  | succ r hr ih =>
    have : ∀ pq, IsIso ((φ.hom (r + 1)).f pq) := fun pq ↦ by
      have e := φ.comm r (r + 1) pq
      have : IsIso (HomologicalComplex.homologyMap (φ.hom r) pq) :=
        (inferInstance : IsIso ((HomologicalComplex.homologyFunctor C _ pq).map (φ.hom r)))
      rw [← Iso.inv_comp_eq] at e
      rw [← e]
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _

/-- **Page induction for `E∞`.** A morphism of first quadrant spectral sequences which is an
isomorphism on the `E₂`-page is an isomorphism on the `E∞`-terms.

(blueprint: `lem-sp-page-induction`) -/
theorem SpectralSequence.Hom.isIso_pageInfinity {E E' : E₂CohomologicalSpectralSequenceNat C}
    (φ : E ⟶ E') (h : IsIso (φ.hom 2)) (pq : ℕ × ℕ) :
    IsIso ((φ.hom (pq.1 + pq.2 + 2 : ℕ) (by lia)).f pq) := by
  have := φ.isIso_hom h (pq.1 + pq.2 + 2 : ℕ) (by lia)
  infer_instance


end PageInduction

end CategoryTheory
