/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Sets.OpenCover

/-! # Cofinal finite affine open coverings of a qcqs scheme

Source: Stacks Project, Schemes, Tags 01IT and 01KO, and Algebra, Tag 00E8
(blueprint: lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/-- Every open covering of a quasi-compact quasi-separated scheme has a finite affine open
refinement with quasi-compact pairwise intersections. Thus these finite coverings are cofinal
under refinement, as required in Stacks, Modules, Tag 01BS (3), and Sheaves, Tag 009F (4).

Source: Stacks Project, Schemes, Tags 01IT and 01KO, and Algebra, Tag 00E8
(blueprint: lem-weil-pbc-qcqs-scheme-cofinal-finite-coverings).

Proof:
1. For each point `x` of `X`, choose a member `V a` of the given covering containing `x`.
   The affine basis theorem (Stacks 01IT, `Scheme.isBasis_affineOpens`) gives an affine open
   neighbourhood of `x` contained in `V a`. These neighbourhoods cover `X`. Quasi-compactness
   gives a finite subcover (`IsCompact.elim_finite_subcover`). Index it by a finite type `J` and
   retain the chosen indices in `A` to obtain the refinement map. This uses `def-pc-scheme`
   and `definition-ind-etale-pro-etale-weakly--3`.
2. Each selected affine open is quasi-compact (Stacks 00E8, `IsAffineOpen.isCompact`).
   Quasi-separatedness implies their pairwise intersections are quasi-compact
   (`pqf-lem-qs-intersection-qc`, or directly Stacks 01KO (1) implies (2)). Hence every
   covering is refined by a covering of the asserted class, which is precisely cofinality
   under refinement and the stated hypotheses of 01BS and 009F.
-/
theorem qcqs_scheme_cofinal_finite_affine_open_coverings
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {A : Type v} (V : A → X.Opens) (hV : TopologicalSpace.IsOpenCover V) :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens) (a : J → A),
      TopologicalSpace.IsOpenCover U ∧
      (∀ j, IsAffineOpen (U j)) ∧
      (∀ j, U j ≤ V (a j)) ∧
      (∀ j j', IsCompact ((U j : Set X) ∩ (U j' : Set X))) := by
  classical
  have htop : ⨆ a, V a = ⊤ := hV.iSup_eq_top
  choose a ha using fun x : X ↦ (TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ (⨆ a, V a) from htop.symm ▸ Set.mem_univ x))
  choose U hUaff hxU hUsub using fun x : X ↦
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (ha x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x hx
      rw [Set.mem_iUnion]
      exact ⟨x, hxU x⟩)
  let J := {x : X // x ∈ t}
  let U' : J → X.Opens := fun j ↦ U j.1
  let a' : J → A := fun j ↦ a j.1
  refine ⟨J, inferInstance, U', a', ?_, ?_, ?_, ?_⟩
  · apply TopologicalSpace.IsOpenCover.mk
    apply le_antisymm le_top
    intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxi
    exact ⟨⟨i, hi⟩, hxi⟩
  · intro j
    exact hUaff j.1
  · intro j
    exact hUsub j.1
  · intro j j'
    exact QuasiSeparatedSpace.inter_isCompact _ _ (U' j).isOpen (hUaff j).isCompact
      (U' j').isOpen (hUaff j').isCompact

end AlgebraicGeometry
