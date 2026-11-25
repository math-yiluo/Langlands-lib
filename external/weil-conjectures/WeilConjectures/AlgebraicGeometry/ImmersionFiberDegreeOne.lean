/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.FiberDegreeBound

/-!
# Fibres of an immersion have degree at most one

Source: Stacks Project, Morphisms, Lemma Tag 03J9
(blueprint: lem-weil-pbc-immersion-fibre-degree-one).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- An immersion has finite fibres of degree at most one. Outside its image the fibre is
empty; on its image the canonical projection to the spectrum of the residue field is an
isomorphism. In particular its fibres are universally bounded.

Source: Stacks Project, Morphisms, Lemma Tag 03J9
(blueprint: lem-weil-pbc-immersion-fibre-degree-one).

Proof, following the five steps of the node:
1. Base change the immersion to `Spec κ(x)`. The fibre projection is an immersion by
   `lem-weil-pbc-immersion-base-change-lft`, hence factors into a closed and an open immersion
   (`def-weil-closed-immersion`, `def-weil-open-immersion`, `def-pc-scheme-fibre`,
   `def-pc-fibre-product`).
2. The spectrum of a field has one point, so the open part has empty source or is an
   isomorphism (`def-weil-affine-spectrum`, `def-weil-open-immersion`).
3. In the latter case the closed part is the spectrum of a quotient of the residue field.
   Its ideal is zero or the whole field, giving an isomorphism or the empty scheme
   (`def-weil-closed-immersion`, `def-weil-affine-spectrum`).
4. The fibre homeomorphism onto the inverse image of `x` identifies the empty case with
   `x` outside the image (`def-pc-scheme-fibre`). Thus on the image the projection is an iso.
5. The empty scheme is affine with zero global sections; the other case has the residue
   field as its algebra of global sections. Both projections are finite, and their degrees
   are respectively zero and one (`pqf-def-affine-morphism`,
   `def-weil-finite-integral-morphism`, `def-weil-affine-spectrum`). The bound one witnesses
   universal boundedness (`def-weil-pbc-fibre-degree-bound`). -/
theorem immersion_fiber_degree_one {Z X : Scheme.{u}} (j : Z ⟶ X) [IsImmersion j] :
    BoundsFiberDegrees j 1 ∧
      (∀ x : X, (x ∉ Set.range j → IsEmpty (j.fiber x)) ∧
        (x ∈ Set.range j → IsIso (j.fiberToSpecResidueField x))) ∧
      HasUniversallyBoundedFibers j := by
  classical
  have hclosed (x : X) : IsClosedImmersion (j.fiberToSpecResidueField x) :=
    .of_isPreimmersion (CategoryTheory.Limits.pullback.snd _ _) (isClosed_discrete _)
  have hcases (x : X) :
      (x ∉ Set.range j → IsEmpty (j.fiber x)) ∧
      (x ∈ Set.range j → IsIso (j.fiberToSpecResidueField x)) := by
    constructor
    · intro hx
      exact ⟨fun z ↦ hx ⟨(j.fiberHomeo x z).1, (j.fiberHomeo x z).2⟩⟩
    · rintro ⟨z, hz⟩
      let w : j.fiber x := (j.fiberHomeo x).symm ⟨z, hz⟩
      have :=  hclosed x
      have : Surjective (j.fiberToSpecResidueField x) :=
        ⟨fun y ↦ ⟨w, Subsingleton.elim _ _⟩⟩
      exact isIso_of_isClosedImmersion_of_surjective _
  have hbound : BoundsFiberDegrees j 1 := by
    intro x
    have :=  hclosed x
    refine ⟨inferInstance, ?_⟩
    by_cases hx : x ∈ Set.range j
    · have :=  (hcases x).2 hx
      have h := finrankΓ_eq_of_iso (j.fiberToSpecResidueField x) (𝟙 _)
        (asIso (j.fiberToSpecResidueField x)) (Iso.refl _) (by simp)
      rw [h]
      exact (finrankΓ_id (k := X.residueField x)).le
    · have :=  (hcases x).1 hx
      have h : (j.fiberToSpecResidueField x).finrankΓ = 0 :=
        Module.finrank_zero_of_subsingleton
      simp [h]
  exact ⟨hbound, hcases, 1, hbound⟩

end AlgebraicGeometry.Scheme.Hom
