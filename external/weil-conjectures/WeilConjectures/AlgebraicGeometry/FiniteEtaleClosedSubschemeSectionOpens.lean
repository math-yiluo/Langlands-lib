/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

import WeilConjectures.AlgebraicGeometry.AffineEtaleClosedImmersionLift
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
/-- Source: Stacks Project, Étale Cohomology, Lemma 59.80.6 (Tag 09ZA),
first paragraph of the proof (blueprint: lem-weil-pbc-gabber-finite-etale-section-opens).

Proof: Write `X = Spec R`. A closed subscheme of an affine scheme is affine, so
`Z = Spec (R/I)`, and write `V = Spec B` as an étale algebra over `R/I`.
By Stacks Tag 04D1 (the étale algebra lifting theorem), lift `B` to an étale
`R`-algebra `C`, with `C ⊗[R] (R/I) ≃ B`. Thus `U = Spec C` is affine étale
and separated over `X`, and `U ×[X] Z ≃ V` over `Z`.
Apply Stacks Tag 09Z9 to `U → X`: its source has a covering by pairwise disjoint
nonempty opens, each mapping to `X` by an open immersion. Since `U` is affine
it is quasi-compact, so finitely many of these opens cover. Disjointness and
nonemptiness ensure that these are all the opens of the decomposition. The
complement of each is the union of the others, so each is closed as well.
Pull the finite family back along `U ×[X] Z → U` and transport it along the
isomorphism with `V`. Inverse images preserve closedness, disjointness, and
the covering property. Each restriction to `Z` is the base change of an open
immersion to `X`, hence an open immersion. Empty inverse images are allowed;
if `V` is empty the empty family also satisfies the conclusion. -/
theorem Etale.exists_finite_clopen_opens_of_closedImmersion
    {X Z V : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
    (p : V ⟶ Z) [Etale p] [IsAffine V] :
    ∃ (n : ℕ) (W : Fin n → V.Opens),
      (∀ j, IsClosed (W j : Set V)) ∧
      (∀ j k, j ≠ k → Disjoint (W j) (W k)) ∧
      (⨆ j, W j) = ⊤ ∧ ∀ j, IsOpenImmersion ((W j).ι ≫ p) := by
  classical
  obtain ⟨U, hU, q, hq, a, ha⟩ := Etale.exists_affine_lift_of_closedImmersion i p
  let : IsAffine U := hU
  let : Etale q := hq
  obtain ⟨ι, hfin, O, hdisj, hcov, hopen⟩ :=
    Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField
      (fun x ↦ (hX x).2) q
  let : Finite ι := hfin
  let : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hclosed (j : ι) : IsClosed (O j : Set U) := by
    have heq : (O j : Set U)ᶜ = ⋃ k : {k : ι // k ≠ j}, (O k.1 : Set U) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion]
      constructor
      · intro hx
        have hx' : x ∈ (⨆ k, O k) := by rw [hcov]; trivial
        obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'
        exact ⟨⟨k, fun h ↦ hx (h ▸ hk)⟩, hk⟩
      · rintro ⟨k, hk⟩ hj
        exact (Set.disjoint_left.mp (show Disjoint (O k.1 : Set U) (O j : Set U) from
          TopologicalSpace.Opens.coe_disjoint.mpr (hdisj k.1 j k.2))) hk hj
    rw [← isOpen_compl_iff, heq]
    exact isOpen_iUnion fun k ↦ (O k.1).isOpen
  refine ⟨Fintype.card ι, fun j ↦ a ⁻¹ᵁ O (e j), ?_, ?_, ?_, ?_⟩
  · intro j
    exact (hclosed (e j)).preimage a.continuous
  · intro j k hjk
    rw [disjoint_iff]
    change a ⁻¹ᵁ (O (e j) ⊓ O (e k)) = ⊥
    rw [(hdisj (e j) (e k) (fun h ↦ hjk (e.injective h))).eq_bot]
    rfl
  · rw [← a.preimage_iSup, e.iSup_comp, hcov, a.preimage_top]
  · intro j
    have H := (isPullback_morphismRestrict a (O (e j))).paste_vert ha
    let : IsOpenImmersion ((O (e j)).ι ≫ q) := hopen (e j)
    exact MorphismProperty.of_isPullback H inferInstance
end AlgebraicGeometry
