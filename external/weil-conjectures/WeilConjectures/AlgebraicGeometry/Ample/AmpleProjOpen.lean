/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.AmpleFiniteAffineCover
import WeilConjectures.AlgebraicGeometry.Ample.AmpleProjLocalChart

/-!
# An ample invertible module gives an open immersion into Proj

Source: Stacks Project, Properties, Proposition 01Q3, implication (1) => (2),
and Lemma 01Q1 (blueprint: lem-sc-ample-proj-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A scheme with an ample invertible module is an open subscheme of the Proj of a
nonnegatively graded commutative ring.
Source: Stacks Project, Properties, Proposition 01Q3, implication (1) => (2),
and Lemma 01Q1 (blueprint: lem-sc-ample-proj-open).

Proof: form the section ring `S = ⨁ n ≥ 0, Γ(X, L^{⊗ n})`. By
`lem-sc-ample-finite-affine-cover`, finitely many positive-degree homogeneous sections
have affine nonvanishing loci covering `X`. The cover hypothesis of
`lem-sc-ample-proj-local-chart` supplies the canonical morphism `f : X ⟶ Proj(S)`.
For each chosen section `s`, that node identifies the inverse image of `D₊(s)` with
`X_s` and the map `X_s ⟶ D₊(s)` with an isomorphism. The image is consequently the
union of these standard open charts. These local isomorphisms agree on overlaps,
as restrictions of the single morphism `f`; they glue to an isomorphism from `X`
to that open subscheme. Hence `f` is an open immersion. -/
theorem exists_isOpenImmersion_proj_of_isAmple (X : Scheme.{u}) (L : X.Modules)
    [L.IsInvertible] (hL : Scheme.Modules.IsAmple X L) :
    ∃ (S : Type u) (_ : CommRing S) (𝒮 : ℕ → AddSubgroup S) (_ : GradedRing 𝒮)
      (f : X ⟶ Proj 𝒮), IsOpenImmersion f := by
  classical
  open Scheme.Modules in
  obtain ⟨m, n, s, U, hn, hU, hnonvanishing, hcover⟩ :=
    Scheme.Modules.IsAmple.exists_finite_affine_cover X L hL
  let t (i : Fin m) : Scheme.Modules.sectionRingGrade L (n i) :=
    ⟨DirectSum.of (Scheme.Modules.SectionRingComponent L) (n i) (s i), ⟨s i, rfl⟩⟩
  have ht (i : Fin m) : (t i).val (n i) = s i := DirectSum.of_eq_same _ _
  have hUeq (i : Fin m) : (U i : Set X) =
      Scheme.Modules.nonvanishingLocus (L.tensorPow (n i)) ((t i).val (n i)) := by
    rw [ht]
    exact Set.ext (hnonvanishing i)
  obtain ⟨f, hf⟩ := Scheme.Modules.exists_sectionRing_proj_affine_charts X L (by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact ⟨n i, t i, hn i, hUeq i ▸ hi⟩)
  refine ⟨Scheme.Modules.InvertibleSectionRing L, inferInstance,
    Scheme.Modules.sectionRingGrade L, inferInstance, f, ?_⟩
  let V (i : Fin m) := Proj.basicOpen (Scheme.Modules.sectionRingGrade L) (t i).val
  have hV (i : Fin m) : IsIso (f ∣_ V i) :=
    (hf (n i) (hn i) (t i)).2.2 hL (U i) (hUeq i) (hU i)
  apply IsZariskiLocalAtTarget.of_range_subset_iSup V
  · rintro y ⟨x, rfl⟩
    obtain ⟨i, hi⟩ := hcover x
    have hxi : x ∈ f ⁻¹ᵁ V i := by
      change x ∈ (f ⁻¹ᵁ V i : Set X)
      rw [(hf (n i) (hn i) (t i)).1]
      exact hUeq i ▸ hi
    exact (le_iSup V i) hxi
  · intro i
    let := hV i
    infer_instance

end AlgebraicGeometry
