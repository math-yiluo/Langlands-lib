/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Finite homogeneous coordinates

Source: Stacks Project, Tags 01N0 (Lemma 27.11.3) and 01ND (Section 27.13).
(blueprint: lem-weil-pbc-projective-space-finite-coordinates).
-/

@[expose] public section

universe u

open CategoryTheory Limits MvPolynomial

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A projective space with finitely many homogeneous coordinates embeds as a linear
closed subscheme of a projective space with coordinates `ULift (Fin (n + 1))`.
Source: Stacks Project, Tags 01N0 (surjective graded maps induce closed immersions)
and 01ND (projective space is the base change of the integral polynomial-ring Proj).
Enumerate `Option N`, send its extra variable to zero and its other variables to the
corresponding variables of `N`. Renaming back along `i ↦ e (some i)` is a right inverse,
and preserves every homogeneous degree, so the irrelevant ideal of the target is
contained in the image of the source irrelevant ideal. This gives a surjective graded map;
its Proj map is a closed immersion. Base change the integral map to `S`.
(blueprint: lem-weil-pbc-projective-space-finite-coordinates). -/
theorem ProjectiveSpace.exists_isClosedImmersion_finite_coordinates (N : Type u) [Finite N]
    (S : Scheme.{u}) :
    ∃ (n : ℕ) (k : ℙ(N; S) ⟶ ℙ(ULift.{u} (Fin (n + 1)); S)),
      IsClosedImmersion k ∧ k ≫ ℙ(ULift.{u} (Fin (n + 1)); S) ↘ S = ℙ(N; S) ↘ S := by
  classical
  let : Fintype N := Fintype.ofFinite N
  let M := ULift.{u} (Fin (Fintype.card N + 1))
  let e : Option N ≃ M := (Fintype.equivFin (Option N)).trans
    ((finCongr (Fintype.card_option)).trans Equiv.ulift.symm)
  let v : M → MvPolynomial N (ULift.{u} ℤ) := fun t ↦
    match e.symm t with
    | none => 0
    | some i => X i
  have hv (t : M) : (v t).IsHomogeneous 1 := by
    dsimp [v]
    cases e.symm t
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_X _ _
  let φ : homogeneousSubmodule M (ULift.{u} ℤ) →+*ᵍ
      homogeneousSubmodule N (ULift.{u} ℤ) :=
    { toRingHom := eval₂Hom C v
      map_mem := fun {d} {p} hp ↦ by
        change (eval₂ C v p).IsHomogeneous d
        simpa using hp.eval₂ C v (fun r ↦ isHomogeneous_C _ r) hv }
  have hφ (p : MvPolynomial N (ULift.{u} ℤ)) :
      φ (rename (fun i ↦ e (some i)) p) = p := by
    change eval₂Hom C v (rename _ p) = p
    rw [eval₂Hom_rename]
    have hve : v ∘ (fun i ↦ e (some i)) = X := by
      funext i
      simp [v]
    rw [hve]
    simp
  have hsurj : Function.Surjective φ := fun p ↦ ⟨_, hφ p⟩
  have hirr : HomogeneousIdeal.irrelevant (homogeneousSubmodule N (ULift.{u} ℤ)) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule M (ULift.{u} ℤ))).map φ := by
    rw [HomogeneousIdeal.irrelevant_le]
    intro d hd p hp
    have hp' := hp.rename_isHomogeneous (f := fun i ↦ e (some i))
    have hm := HomogeneousIdeal.mem_irrelevant_of_mem
      (homogeneousSubmodule M (ULift.{u} ℤ)) hd hp'
    have hx := Ideal.mem_map_of_mem φ hm
    change p ∈ Ideal.map φ
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule M (ULift.{u} ℤ))).toIdeal
    simpa only [hφ] using hx
  let q := Proj.map φ hirr
  have hq : IsClosedImmersion q := Proj.isClosedImmersion_map φ hirr hsurj
  let k : ℙ(N; S) ⟶ ℙ(M; S) := pullback.map _ _ _ _ (𝟙 S) q (𝟙 _)
    (by simp) (terminal.hom_ext _ _)
  have hk : IsClosedImmersion k := by
    apply MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstance : IsClosedImmersion (𝟙 S)) hq (by simp) (terminal.hom_ext _ _)
  refine ⟨Fintype.card N, k, hk, ?_⟩
  change k ≫ pullback.fst _ _ = pullback.fst _ _
  simp [k]

end AlgebraicGeometry
