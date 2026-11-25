/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.GluingPresentation

/-!
# Existence of finite affine gluing presentations

Every quasi-compact quasi-separated scheme `S` admits a finite affine gluing presentation
(`AlgebraicGeometry.Scheme.nonempty_finiteAffineGluingPresentation`); we select one,
`AlgebraicGeometry.Scheme.finiteAffineGluingPresentation`. Conversely, a scheme with a finite
affine gluing presentation is quasi-compact and quasi-separated, and the open cover by the charts
of the presentation glues back to `S`
(`AlgebraicGeometry.Scheme.FiniteAffineGluingPresentation.isCompact_inf_and_isIso_fromGlued`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Every quasi-compact quasi-separated scheme admits a finite affine gluing presentation. -/
theorem nonempty_finiteAffineGluingPresentation (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] : Nonempty S.FiniteAffineGluingPresentation := by
  classical
  -- A finite affine open cover.
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun U : S.affineOpens ↦ ((U : S.Opens) : Set S)) (fun U ↦ (U : S.Opens).2)
    (fun x _ ↦ by
      obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
      exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
  let U : t → S.affineOpens := fun a ↦ a.1
  have hU : ⨆ a, (U a : S.Opens) = ⊤ := by
    refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩
  -- Finitely many simultaneous basic opens covering each overlap.
  let P : t → t → Type u := fun a b ↦
    {p : Γ(S, U a) × Γ(S, U b) // S.basicOpen p.1 = S.basicOpen p.2}
  have hcov : ∀ a b, ∃ s : Finset (P a b),
      ((U a : S.Opens) ⊓ U b : Set S) ⊆ ⋃ p ∈ s, (S.basicOpen p.1.1 : Set S) := by
    intro a b
    refine IsCompact.elim_finite_subcover ?_ _ (fun p ↦ (S.basicOpen p.1.1).2) fun x hx ↦ ?_
    · exact QuasiSeparatedSpace.inter_isCompact _ _ (U a).1.2 (U a).2.isCompact (U b).1.2
        (U b).2.isCompact
    · obtain ⟨f, g, hfg, hx⟩ := exists_basicOpen_le_affine_inter (U a).2 (U b).2 x hx
      exact Set.mem_iUnion.mpr ⟨⟨(f, g), hfg⟩, hx⟩
  choose s hs using hcov
  exact ⟨{
    ι := t
    U := U
    iSup_U := hU
    κ := fun a b ↦ s a b
    f := fun a b r ↦ r.1.1.1
    g := fun a b r ↦ r.1.1.2
    basicOpen_f := fun a b r ↦ r.1.2
    iSup_basicOpen_f := fun a b ↦ by
      refine le_antisymm (iSup_le fun r ↦ le_inf (S.basicOpen_le _) ?_) fun x hx ↦ ?_
      · rw [r.1.2]
        exact S.basicOpen_le _
      · obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp (hs a b hx)
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hxp⟩ }⟩

/-- The selected finite affine gluing presentation `G_S` of a quasi-compact quasi-separated scheme
`S`. -/
noncomputable def finiteAffineGluingPresentation (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] : S.FiniteAffineGluingPresentation :=
  Classical.choice S.nonempty_finiteAffineGluingPresentation

namespace FiniteAffineGluingPresentation

variable {S : Scheme.{u}} (G : S.FiniteAffineGluingPresentation)

/-- Gluing the charts of a finite affine gluing presentation along their overlaps recovers `S`.
-/
noncomputable def gluedIso : G.openCover.gluedCover.glued ≅ S :=
  asIso G.openCover.fromGlued

/-- For a finite affine gluing presentation, every overlap `Uₐ ⊓ U_b` is quasi-compact and is the
union of the finitely many basic opens `D(f a b r)`, there are finitely many charts and overlap
basic opens, and the canonical map from the scheme glued from the charts to `S` is an
isomorphism. -/
theorem isCompact_inf_and_isIso_fromGlued :
    (∀ a b, IsCompact (((G.U a : S.Opens) ⊓ G.U b : S.Opens) : Set S)) ∧
      (∀ a b, ⨆ r, S.basicOpen (G.f a b r) = (G.U a : S.Opens) ⊓ G.U b) ∧
      Finite G.ι ∧ (∀ a b, Finite (G.κ a b)) ∧ IsIso G.openCover.fromGlued :=
  ⟨G.isCompact_inf, G.iSup_basicOpen_f, inferInstance, fun _ _ ↦ inferInstance, inferInstance⟩

end FiniteAffineGluingPresentation

end AlgebraicGeometry.Scheme
