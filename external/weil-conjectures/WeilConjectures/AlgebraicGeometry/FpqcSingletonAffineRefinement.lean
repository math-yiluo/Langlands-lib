/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Affine refinement of a singleton fpqc covering

Source: Stacks Project, Topologies, Definition 022B and Lemma 022E, with the finite
coproduct construction (blueprint: lem-galois-fpqc-singleton-affine-refinement).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- If a singleton fpqc covering has affine base, finitely many affine opens of its source
give an affine coproduct whose induced map is flat, surjective, and an fpqc covering.

Source: Stacks Project, Topologies, Definition 022B and Lemma 022E
(blueprint: lem-galois-fpqc-singleton-affine-refinement).

Apply the finite affine-open image condition of the fpqc covering to the whole affine base;
the source map is flat. Form the finite coproduct of the chosen opens and use its universal
property to obtain the map to the original source. A finite coproduct of affine schemes is
affine. The induced map is surjective since the images of the opens cover the base, and it
is flat because the coprojections and the open inclusions identify the local rings with
those of the original flat map. Finally, for every affine open of the base, its inverse
image under the resulting flat surjection is affine and witnesses the singleton fpqc
condition. The empty family is allowed when the base is empty. -/
theorem exists_fpqc_singleton_affine_refinement {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (hf : Presieve.singleton f ∈ fpqcPrecoverage S) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ j, IsAffineOpen (U j)) ∧
      (let X' := ∐ (fun j : Fin n ↦ (U j).toScheme);
       ∃ (h : X' ⟶ X) (g : X' ⟶ S),
        (∀ j, Sigma.ι (fun k ↦ (U k).toScheme) j ≫ h = (U j).ι) ∧
        g = h ≫ f ∧ IsAffine X' ∧ Flat g ∧ Surjective g ∧
          Presieve.singleton g ∈ fpqcPrecoverage S) := by
  classical
  have hqc : Presieve.singleton f ∈ qcPrecoverage S := hf.1
  have : Flat f := (singleton_mem_precoverage_iff (@Flat) f).mp hf.2 |>.2
  have : QuasiCompactCover (PreZeroHypercover.singleton.{0} f) := by
    apply presieve₀_mem_qcPrecoverage_iff.mp
    simpa using hqc
  obtain ⟨n, a, U, hU, hcover⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact
      (PreZeroHypercover.singleton.{0} f) (U := ⊤) isCompact_univ
  change ∃ (n : ℕ) (U : Fin n → X.Opens), _
  change Fin n → X.Opens at U
  change ∀ j, IsAffineOpen (U j) at hU
  change (⋃ j, f '' (U j : Set X)) = Set.univ at hcover
  have (j : Fin n) : IsAffine (U j).toScheme := hU j
  let h : (∐ fun j : Fin n ↦ (U j).toScheme) ⟶ X := Sigma.desc fun j ↦ (U j).ι
  let g : (∐ fun j : Fin n ↦ (U j).toScheme) ⟶ S :=
    Sigma.desc fun j ↦ (U j).ι ≫ f
  have hg : g = h ≫ f := by
    apply Sigma.hom_ext
    intro j
    simp [g, h]
  have : Flat g := by dsimp [g]; infer_instance
  have : Surjective g := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    convert hcover using 1
    congr 1
    funext j
    ext s
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  exact ⟨n, U, hU, h, g, (fun j ↦ by simp [h]), hg,
    inferInstance, inferInstance, inferInstance, g.singleton_mem_fpqcPrecoverage⟩

end AlgebraicGeometry.Scheme
