/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraPullbackData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjQuotientPullbackComparison
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjNormalizedDescent
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjFreeComparison
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackQuasiCoherent
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank

/-!
# A standard model of a projective-bundle fibre with its tautological line

## References

* Stacks Project, Constructions, Tags 01OA and 01OE
* EGA II, Remark 4.2.7, residue-field normalization
* EGA II, Remark 4.2.7, field normalization
* Stacks Project, Tag 01CR
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionId
  Scheme.GradedAlgebraData.relProj Scheme.GradedAlgebraData.relProjHom
  Scheme.GradedAlgebraData.PullbackData.relProjComparison

/-- A finite locally free module on a one-point scheme is globally free. -/
private theorem nonempty_iso_free_of_subsingleton (X : Scheme.{u}) [Nonempty X]
    [Subsingleton X] (M : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r] :
    Nonempty (M ≅ SheafOfModules.free (ULift.{u} (Fin r))) := by
  classical
  obtain ⟨I, U, hU, e⟩ := IsFiniteLocallyFreeOfRank.exists_restrict_iso_free M (r := r)
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ ⨆ i, U i by rw [hU]; trivial)
  have htop : U i = ⊤ := eq_top_iff.mpr fun y _ ↦ by
    rwa [Subsingleton.elim y x]
  have ei := e i
  rw [htop] at ei
  have : IsIso (⊤ : X.Opens).ι := inferInstanceAs (IsIso X.topIso.hom)
  exact ⟨isoFreeOfRestrictIso M _ ei.some⟩

/-- Transport a pullback comparison through the inverse scheme isomorphism. -/
private noncomputable def inverse_pullback_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (M : X.Modules) (N : Y.Modules) (t : (tensorPullback e.hom).obj N ≅ M) :
    (tensorPullback e.inv).obj M ≅ N :=
  (tensorPullback e.inv).mapIso t.symm ≪≫
    (tensorPullbackSectionComp e.inv e.hom).symm.app N ≪≫
    eqToIso (congrArg (fun f ↦ (tensorPullback f).obj N) e.inv_hom_id) ≪≫
    (tensorPullbackSectionId Y).app N

/-- A basis of E at s identifies the scheme-theoretic fibre with standard
projective space and the pulled-back normalized line with the standard degree-one
twist. There is no assertion about arbitrary invertible modules or other powers. -/
theorem exists_projective_bundle_fiber_twist_model (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (D : TautologicalQuotient E) (s : S) :
    ∃ e : ℙ(ULift.{u} (Fin r); Spec (.of (S.residueField s))) ≅
        (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiber s,
      Nonempty
        ((tensorPullback e.hom).obj
          ((tensorPullback
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s)).obj D.line) ≅
          ProjectiveSpace.twist (ULift.{u} (Fin r)) (Spec (.of (S.residueField s))) 1) := by
  classical
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, r = n + 1 := ⟨r - 1, by omega⟩
  let X := Spec (.of (S.residueField s))
  let g : X ⟶ S := S.fromSpecResidueField s
  let F := (tensorPullback g).obj E
  have : F.IsQuasicoherent := isQuasicoherent_tensorPullback g E
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((tensorOrdinaryPullbackIso g).app E).symm
  obtain ⟨a⟩ := nonempty_iso_free_of_subsingleton X F (n + 1)
  obtain ⟨D', _⟩ :=
    SymmetricProjTautologicalCharts.exists_normalized_quotient_with_affine_restriction X F
  obtain ⟨b, hb⟩ := SymmetricAlgebraSheaf.exists_normalized_pullbackData g E
  obtain ⟨w, _⟩ := SymmetricProjTautologicalCharts.quotient_comparison_of_normalized_pullbackData
    g E D D' b hb (congrArg (fun f ↦ (tensorPullback f).obj E) b.isPullback.w)
  obtain ⟨_, eStd, t, _⟩ :=
    SymmetricProjTautologicalCharts.free_compatibility_of_normalized_quotient X F D'
      n a.symm
  let q := b.relProjIsoPullback
  let e := eStd.symm ≪≫ q
  refine ⟨e, ⟨?_⟩⟩
  let f := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom.fiberι s
  have hcomp : q.hom ≫ f = b.relProjComparison := b.relProjIsoPullback_hom_fst
  exact (tensorPullbackSectionComp eStd.inv q.hom).app
      ((tensorPullback f).obj D.line) ≪≫
    (tensorPullback eStd.inv).mapIso
      ((tensorPullbackSectionComp q.hom f).symm.app D.line ≪≫
        eqToIso (congrArg (fun h ↦ (tensorPullback h).obj D.line) hcomp) ≪≫ w) ≪≫
    inverse_pullback_iso eStd D'.line _ t

end AlgebraicGeometry.ProjectiveBundlePicardClassification
