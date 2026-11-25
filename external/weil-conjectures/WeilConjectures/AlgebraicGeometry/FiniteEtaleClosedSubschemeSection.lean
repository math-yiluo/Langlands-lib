/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.FiniteClopenOpenCoverSection
import WeilConjectures.AlgebraicGeometry.FiniteEtaleClosedSubschemeSectionOpens

/-!
# Étale covers of closed subschemes of an affine normal scheme

Source: Stacks Project, Étale Cohomology, Lemma 59.80.6 (Tag 09ZA)
(blueprint: lem-weil-pbc-gabber-finite-etale-section).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Source: Stacks Project, Étale Cohomology, Lemma 59.80.6 (Tag 09ZA)
(blueprint: lem-weil-pbc-gabber-finite-etale-section).

An affine étale scheme over a closed subscheme of an affine integral normal scheme with
separably closed function field is a finite disjoint union of opens of the closed subscheme.
If the étale morphism is also finite and surjective, it admits a section.

Proof:
1. Write `X = Spec R`. The closed immersion makes `Z = Spec (R/I)`, and the affine scheme
   `V` corresponds to an étale `R/I`-algebra. Use
   [lem-weil-pbc-closed-immersion-affine-cover-criterion],
   [lem-weil-pbc-morphism-into-affine-scheme], and
   [lem-weil-pbc-etale-ring-map-iff-etale-affine].
2. Lift that algebra to an étale `R`-algebra by
[proposition-extension-zero-restriction-closed-subscheme] (Stacks 04D1).
   Its spectrum `U` satisfies `U ×_X Z ≅ V` over `Z`, by
   [lem-weil-pbc-fibre-product-affine-spectra] and
   [lem-weil-pbc-tensor-quotient-base-change].
3. The affine morphism `U → X` is separated by
   [lem-weil-pbc-morphism-affine-schemes-affine] and
   [lem-weil-pbc-affine-morphism-permanence]. Apply
   [proposition-base-change-larger-algebraically-closed] (09Z9) to obtain disjoint nonempty opens of
   `U`, each mapping to `X` by an open immersion. Quasi-compactness
   [lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact] makes their number finite; each is
   closed because its complement is the union of the others.
4. Pull these opens back to `U ×_X Z` and transport them to `V`. They remain disjoint,
   clopen, and covering. Each restriction to `Z` is an open immersion by
   [lem-weil-pbc-open-fibre-product] and [lem-weil-pbc-open-immersion-base-change].
5. If `p` is finite and surjective, apply [theorem-gabber-affine-proper-base-change].
   Its proof forms the clopen strata in `Z` determined by membership in the finitely
   many images of these opens. Each stratum lies in one image; use the inverse of that
   open immersion there and glue the resulting sections across the disjoint strata.
-/
theorem Etale.exists_finite_clopen_opens_and_section_of_closedImmersion
    {X Z V : Scheme.{u}} [IsAffine X] [IsIntegral X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    [IsSepClosed X.functionField] (i : Z ⟶ X) [IsClosedImmersion i]
    (p : V ⟶ Z) [Etale p] [IsAffine V] :
    (∃ (n : ℕ) (W : Fin n → V.Opens),
      (∀ j, IsClosed (W j : Set V)) ∧
      (∀ j k, j ≠ k → Disjoint (W j) (W k)) ∧
      (⨆ j, W j) = ⊤ ∧
      ∀ j, IsOpenImmersion ((W j).ι ≫ p)) ∧
    (Surjective p → IsFinite p → ∃ s : Z ⟶ V, s ≫ p = 𝟙 Z) := by
  obtain ⟨n, W, hclosed, hdisj, hcov, hopen⟩ :=
    Etale.exists_finite_clopen_opens_of_closedImmersion hX i p
  refine ⟨⟨n, W, hclosed, hdisj, hcov, hopen⟩, ?_⟩
  intro hs hf
  let : Surjective p := hs
  let : IsFinite p := hf
  let (j : Fin n) : IsOpenImmersion ((W j).ι ≫ p) := hopen j
  obtain ⟨hcop⟩ := nonempty_isColimit_cofanMk_of (fun j ↦ (W j).ι)
    (by simpa using hcov) (by intro j k hjk; simpa using hdisj j k hjk)
  apply exists_section_of_finite_clopen_open_cover Z V p (fun j ↦ (W j).toScheme)
    (fun j ↦ (W j).ι) _ hcop (fun j ↦ (W j).ι ≫ p) (fun _ ↦ rfl)
  intro j
  refine ⟨inferInstance, IsClosedImmersion.of_isPreimmersion _ ?_⟩
  simpa using hclosed j

end AlgebraicGeometry
