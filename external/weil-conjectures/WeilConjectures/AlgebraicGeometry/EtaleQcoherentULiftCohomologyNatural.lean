/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleQcoherentCohomologyULift
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNaturalSucc

/-! # Naturality of the finite-cover coefficient comparison

Source: Stacks Project, Tag 03P2, separated-case finite affine cover proof.
(blueprint: lem-sc-etale-qcoherent-ulift-cohomology-natural)
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The coefficient comparison can be chosen to commute with every endomorphism
of the associated abelian sheaf, without assuming that universe lift preserves
injective objects.
Source: Stacks Project, Tag 03P2, separated-case finite affine cover proof.
(blueprint: lem-sc-etale-qcoherent-ulift-cohomology-natural)

Proof: Fix a finite affine open cover of the quasi-compact separated scheme X.
Finite intersections are affine. Both the associated quasi-coherent sheaf and
its coefficient lift are acyclic there, by affine acyclicity in their respective
universes. The two Cech-to-derived edge maps are therefore isomorphisms, and are
natural in endomorphisms of the abelian sheaf. Each Cech degree uses a finite
product of section groups. Lowering the lifted components is additive and
commutes with restriction maps, hence with every alternating differential and
with every component of an endomorphism theta. It identifies kernels and images,
so induces an additive equivalence on homology commuting with theta. Compose
with the two edge isomorphisms. Compute the Ext groups by these derived sections
comparisons, reindexing their universes through homAddEquiv if necessary; the
reindexing commutes with postcomposition. In degree zero use evaluation at the
terminal object and AddEquiv.ulift, whose naturality is sectionwise. The empty
cover and the zero sheaf give zero complexes, so the same construction includes
empty X and F=0. The same fixed cover is used for all theta. -/
theorem exists_etaleTensorSectionsSheaf_cohomology_ulift_natural
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    let E := etaleTensorSectionsSheaf F
    let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
    ∃ e : Sheaf.H (L.obj E) q ≃+
        @Sheaf.H _ _ X.smallEtaleTopology E inferInstance (HasExt.standard _) q,
      ∀ (θ : E ⟶ E) (x : Sheaf.H (L.obj E) q),
        e (Sheaf.H.map (L.map θ) q x) =
          @Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology
            inferInstance (HasExt.standard _)
            _ _ θ q (e x) := by
  dsimp
  cases q with
  | zero =>
      let E := etaleTensorSectionsSheaf F
      let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
      let eL := Sheaf.H.equiv₀ (L.obj E) CategoryTheory.Limits.terminalIsTerminal
      let eS := @Sheaf.H.equiv₀.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology inferInstance
        (HasExt.standard _) E _ CategoryTheory.Limits.terminalIsTerminal
      refine ⟨eL.trans (AddEquiv.ulift.trans eS.symm), ?_⟩
      intro θ x
      change eS.symm (AddEquiv.ulift (eL (Sheaf.H.map (L.map θ) 0 x))) =
        @Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology
          inferInstance (HasExt.standard _) _ _ θ 0 (eS.symm (AddEquiv.ulift (eL x)))
      rw [@Sheaf.H.equiv₀_symm_naturality.{u + 1, u, u, u + 1} _ _
        X.smallEtaleTopology inferInstance (HasExt.standard _) _
        CategoryTheory.Limits.terminalIsTerminal E E θ]
      apply congrArg eS.symm
      change AddEquiv.ulift (Sheaf.H.equiv₀ (L.obj E)
        CategoryTheory.Limits.terminalIsTerminal (Sheaf.H.map (L.map θ) 0 x)) = _
      rw [← Sheaf.H.equiv₀_naturality]
      rfl
  | succ n =>
      exact exists_etaleTensorSectionsSheaf_cohomology_ulift_natural_succ X F n

end AlgebraicGeometry.Scheme.Modules
