/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.EtaleQcoherentULiftCohomologyNatural
import WeilConjectures.AlgebraicGeometry.EtaleZariskiQcohComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison

/-! # Natural comparison of lifted tensor-sheaf cohomology with ordinary H

Source: Stacks Project, Tags 03P2 and 03FD.
(blueprint: lem-sc-etale-qcoherent-source-comparison-natural)
-/

@[expose] public section

universe u
open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Compose the natural coefficient, etale/Zariski and module/abelian comparisons.
Source: Stacks Project, Tags 03P2 and 03FD.
(blueprint: lem-sc-etale-qcoherent-source-comparison-natural)

Proof: Choose the etale/Zariski comparison and its module-map family m.
For the fixed F and q, compose the coefficient-lift comparison, the inverse
etale/Zariski comparison, and the source ordinary-H comparison. The inverse
etale/Zariski square follows by applying its forward equivalence and cancelling.
Substitute the three naturality identities in this composite. The resulting
square is natural for every module endomorphism phi. The map m has the section
components stated in etale_zariski_qcoh_comparison. -/
theorem exists_etaleTensorSectionsSheaf_source_comparison_natural
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) :
    let E := etaleTensorSectionsSheaf F
    let L := sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}
    ∃ m : (F ⟶ F) → (E ⟶ E),
      (∀ (φ : F ⟶ F) (U : X.Etale),
        (m φ).hom.app (op U) = ((tensorPullback U.hom).map φ).app ⊤) ∧
      ∃ e : Sheaf.H (L.obj E) q ≃+ H F q,
        ∀ (φ : F ⟶ F) (x : Sheaf.H (L.obj E) q),
          e (Sheaf.H.map (L.map (m φ)) q x) = H.map φ q (e x) := by
  classical
  obtain ⟨l, hl⟩ := exists_etaleTensorSectionsSheaf_cohomology_ulift_natural X F q
  obtain ⟨m, hm, z, hz, _⟩ := etale_zariski_qcoh_comparison X
  obtain ⟨s, hs⟩ := exists_moduleCohomology_source_comparison X q
  let e : Sheaf.H
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (etaleTensorSectionsSheaf F)) q ≃+ H F q :=
    (l.trans (z F q).symm).trans (s F)
  refine ⟨m F F, hm F F, e, ?_⟩
  intro φ x
  have hZ (y) :
      (z F q).symm
        (@Sheaf.H.map.{u + 1, u, u, u + 1} _ _ X.smallEtaleTopology inferInstance
          (HasExt.standard _) _ _ (m F F φ) q y) =
      ((RingedSpace.moduleCohomology X.toRingedSpace q).map φ).hom ((z F q).symm y) := by
    apply (z F q).injective
    simpa only [AddEquiv.apply_symm_apply] using
      (hz F F φ q ((z F q).symm y)).symm
  change s F ((z F q).symm (l (Sheaf.H.map _ q x))) = _
  rw [hl, hZ, hs]
  rfl

end AlgebraicGeometry.Scheme.Modules
