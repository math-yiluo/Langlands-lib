/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectFiniteFreeResidueModel
import WeilConjectures.AlgebraicGeometry.Derived.DerivedResidueUnitBetti
import WeilConjectures.AlgebraicGeometry.AbelianVariety.ConnectiveRankOneModelStalk

/-! # A local degree-zero unit criterion for perfect complexes

## References

* Stacks Project, Tag 0E62, local argument, and Tag 0BCD
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A map from the structure sheaf in degree zero to a perfect complex is surjective
on degree-zero cohomology at a point if its derived residue map is invertible and the
negative cohomology of that derived fibre vanishes. -/
theorem surjective_stalk_homology_of_perfect_local_unit (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : Scheme.IsPerfect S K)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ K) (s : S)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj K)))
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a))) :
    Function.Surjective (Scheme.Modules.Hom.stalkLinearMap
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) s) := by
  have hbettiNegative : ∀ i : ℤ, i < 0 → Scheme.derivedFiberBetti S K i s = 0 := by
    intro i hi
    let F := SheafOfModules.evaluation
      (moduleRings (Spec (S.residueField s)).toRingedSpace) (Opposite.op ⊤)
    have hF : F.Additive :=
      inferInstanceAs ((SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (Opposite.op ⊤)).Additive)
    have hz : IsZero (F.obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
          ((derivedPullback (S.fromSpecResidueField s)).obj K))) := by
      rw [IsZero.iff_id_eq_zero, ← F.map_id, (hnegative i hi).eq_of_src (𝟙 _) 0]
      exact F.map_zero _ _
    have hs := ModuleCat.isZero_iff_subsingleton.mp hz
    let : Subsingleton (Scheme.derivedFiberCohomology S K i s) := hs
    exact Module.finrank_zero_of_subsingleton
  have hbettiZero := Scheme.derivedFiberBetti_zero_eq_one_of_unit_iso S K a s ha
  obtain ⟨_, _, U, hs, hU, P, hb, hrank, ⟨e⟩⟩ :=
    Scheme.exists_finiteFreeResidueModel S K hK s
  have hP : Scheme.IsStrictlyPerfect S U P := by
    refine ⟨hb, fun i ↦ ?_⟩
    obtain ⟨ei⟩ := hrank i
    exact ⟨Scheme.derivedFiberBetti S K i s, ei.hom, ei.inv, ei.hom_inv_id⟩
  have hPnegative : ∀ i : ℤ, i < 0 → IsZero (P.X i) := by
    intro i hi
    obtain ⟨ei⟩ := hrank i
    have hfree : IsZero (SheafOfModules.free
        (R := (moduleRings S.toRingedSpace).over U)
        (ULift.{u} (Fin (Scheme.derivedFiberBetti S K i s)))) := by
      rw [hbettiNegative i hi]
      rw [IsZero.iff_id_eq_zero]
      apply (SheafOfModules.freeHomEquiv _).injective
      ext j
      exact Fin.elim0 j.down
    exact hfree.of_iso ei
  have hPzero : Nonempty (P.X 0 ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over U) (ULift.{u} (Fin 1))) := by
    simpa only [hbettiZero] using hrank 0
  exact surjective_stalk_homology_of_connective_rank_one_model S K a s U hs hU P
    hP hPnegative hPzero e ha

end AlgebraicGeometry
