/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import Mathlib.AlgebraicGeometry.LimitsOver
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Finite affine subcovers with a prescribed covering-sieve condition. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- An etale cover of a compact object admits finitely many affine pieces satisfying
any covering-sieve condition on its source. Source: Stacks, Hypercoverings, 01GJ
and 094K; finite affine refinement of an etale covering.

Proof: Realize R by an etale covering family of E. Compose its members with e;
these maps are etale, open, and jointly surjective onto M. Their affine opens
still have open images covering M. Quasi-compactness selects finitely many.
Their disjoint union N has the asserted finite affine cofan, and its map to E
belongs to R on each constituent because R is closed under precomposition.
Each affine piece is qcqs; its etale structure map to X has all the stated
finiteness properties. No compactness of E is required.
(auxiliary; not a blueprint node) -/
theorem exists_finite_etale_sieve_cover
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (M E : X.Etale) [CompactSpace M.left] (e : E ⟶ M) (he : Surjective e.left)
    (R : Sieve E) (hR : R ∈ X.smallEtaleTopology E) :
    ∃ (N : X.Etale) (ν : N ⟶ E) (k : ℕ) (W : Fin k → X.Etale)
      (ι : ∀ i, W i ⟶ N),
      Surjective (ν ≫ e).left ∧ Nonempty (IsColimit (Cofan.mk N ι)) ∧
        (∀ i, CompactSpace (W i).left ∧ QuasiSeparatedSpace (W i).left ∧
          LocallyOfFinitePresentation (W i).hom ∧ QuasiCompact (W i).hom ∧
            QuasiSeparated (W i).hom) ∧ ∀ i, R (ι i ≫ ν) := by
  classical
  obtain ⟨C, hCX, hC, hle⟩ := (Scheme.mem_smallGrothendieckTopology E R).mp hR
  let := hCX
  let (i : C.I₀) : Etale (C.X i ↘ X) := hC i
  let := he
  let D : Scheme.Cover (Scheme.precoverage @Etale) M.left :=
    Scheme.Cover.mkOfCovers C.I₀ C.X (fun i ↦ C.f i ≫ e.left) (by
      intro x
      obtain ⟨y, hy⟩ := he.surj x
      obtain ⟨i, z, hz⟩ := C.exists_eq y
      exact ⟨i, z, by change e.left (C.f i z) = x; rw [hz, hy]⟩)
  have : QuasiCompactCover D.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap (fun i ↦ (D.f i).isOpenMap)
  obtain ⟨k, a, V, hV, hcover⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact D.toPreZeroHypercover
      (show IsCompact (⊤ : M.left.Opens).carrier from isCompact_univ)
  let W (i : Fin k) : X.Etale := Scheme.Etale.mk ((hV i).fromSpec ≫ (C.X (a i) ↘ X))
  let τ (i : Fin k) : W i ⟶ E :=
    MorphismProperty.Over.homMk ((hV i).fromSpec ≫ C.f (a i)) (by
      change (hV i).fromSpec ≫ C.f (a i) ≫ (E.left ↘ X) =
        (hV i).fromSpec ≫ (C.X (a i) ↘ X)
      rw [(hCX.isOver_map (a i)).comp_over]) trivial
  have : HasCoproductsOfShape (Fin k) X.Etale := by dsimp [Scheme.Etale]; infer_instance
  let N := ∐ W
  let ν : N ⟶ E := Sigma.desc τ
  have hsurj : Surjective (ν ≫ e).left := by
    constructor
    intro x
    have hx : x ∈ ⋃ i, D.f (a i) '' (V i : Set (D.X (a i))) := by
      rw [hcover]
      trivial
    simp only [Set.mem_iUnion, Set.mem_image] at hx
    obtain ⟨i, y, hy, hxy⟩ := hx
    obtain ⟨z, hz⟩ : ∃ z, (hV i).fromSpec z = y := by
      change y ∈ Set.range (hV i).fromSpec
      rw [(hV i).range_fromSpec]
      exact hy
    refine ⟨(Sigma.ι W i).left z, ?_⟩
    have hw : (Sigma.ι W i).left ≫ (ν ≫ e).left = (τ i ≫ e).left :=
      congrArg (fun f ↦ f.left) (Sigma.ι_comp_desc_assoc τ i e)
    change ((Sigma.ι W i).left ≫ (ν ≫ e).left) z = x
    rw [hw]
    change e.left (C.f (a i) ((hV i).fromSpec z)) = x
    rw [hz]
    exact hxy
  refine ⟨N, ν, k, W, Sigma.ι W, hsurj, ⟨coproductIsCoproduct W⟩, ?_, ?_⟩
  · intro i
    have hc : CompactSpace (W i).left := by
      change CompactSpace (Spec Γ(C.X (a i), V i))
      infer_instance
    have hq : QuasiSeparatedSpace (W i).left := by
      change QuasiSeparatedSpace (Spec Γ(C.X (a i), V i))
      infer_instance
    exact ⟨hc, hq, inferInstance,
      @quasiCompact_of_compactSpace _ X _ hc inferInstance,
      @QuasiSeparated.of_quasiSeparatedSpace _ _ _ hq⟩
  · intro i
    rw [Sigma.ι_comp_desc]
    let f : (C.X (a i)).asOverProp X (hC (a i)) ⟶ E := (C.f (a i)).asOverProp X
    let t : W i ⟶ (C.X (a i)).asOverProp X (hC (a i)) :=
      MorphismProperty.Over.homMk (hV i).fromSpec rfl trivial
    have hf : R f := hle _ _ (Presieve.ofArrows.mk (a i))
    exact R.downward_closed hf t

end AlgebraicGeometry
