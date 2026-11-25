/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjGluedSections
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjNormalizedQuotientEpi
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality

/-! # Affine comparisons for normalized symmetric Proj twists

Source: Stacks Project, Constructions, Tags 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-normalized-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite HomogeneousLocalization
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- An affine restriction comparison together with compatibility with the chosen chart.
Source: Stacks, Tags 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-normalized-descent).

Proof: construct the comparison on the standard affine charts of relative Proj by
the homogeneous fraction map.  The map sends a degree-one frame to its restriction;
the affine tilde equivalence and the fraction formula show that it is independent of
the chosen chart and hence glues to the displayed isomorphism. -/
structure AffineComparison {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent]
    (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (U V : S.affineOpens) (h : U ≤ V) where
  comparison : (Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).obj
        (Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1) ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1
  chart_compatibility : (Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).map
        (D.chart V).hom ≫ comparison.hom =
      (Scheme.Modules.tensorPullbackSectionComp
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V)).inv.app D.line ≫
      (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj D.line)
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor_map_relProjι
          (homOfLE h)))).hom ≫ (D.chart U).hom

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.GradedAlgebraData.relProj
  Scheme.GradedAlgebraData.relProjι Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.tensorPullbackSection

private theorem comparison_iso {C : Type u} [Category C]
    {A B D F G : C} (e : A ≅ B) (r : A ≅ D) (s : D ≅ F) (t : F ≅ G) :
    ∃ c : B ≅ G, e.hom ≫ c.hom = r.hom ≫ s.hom ≫ t.hom := by
  refine ⟨e.symm ≪≫ r ≪≫ s ≪≫ t, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

private theorem affineComparison_of_quotient {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E)
    (U V : S.affineOpens) (h : U ≤ V) : Nonempty (AffineComparison E D U V h) := by
  obtain ⟨c, hc⟩ := comparison_iso
    ((Scheme.Modules.tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))).mapIso
        (D.chart V))
    (((Scheme.Modules.tensorPullbackSectionComp
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor.map (homOfLE h))
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι V)).app D.line).symm)
    (eqToIso (congrArg (fun f ↦ (Scheme.Modules.tensorPullback f).obj D.line)
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjFunctor_map_relProjι
        (homOfLE h)))) (D.chart U)
  exact ⟨⟨c, hc⟩⟩

private theorem symmetric_degree_one_cover {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent] (U : S.affineOpens) :
    ∀ x : Proj ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U),
      ∃ f ∈ (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U 1,
        x ∈ Proj.basicOpen ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) f := by
  classical
  let A := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading U
  let : GradedAlgebra A := (SymmetricAlgebraSheaf.gradedAlgebraData E).gradedAlgebra U
  intro x
  by_contra h
  have hp : ∀ f ∈ A 1, f ∈ x.asHomogeneousIdeal.toIdeal := by
    intro f hf
    by_contra hn
    exact h ⟨f, hf, hn⟩
  let q := Ideal.Quotient.mk x.asHomogeneousIdeal.toIdeal
  have heq : q = q.comp (GradedRing.projZeroRingHom A) := by
    apply RingHom.ext
    intro a
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
      change q (algebraMap _ _ r) = q (DirectSum.decompose A _ 0)
      have hr : algebraMap Γ(S, U.1)
          (SymmetricAlgebra Γ(S, U.1) (E.val.obj (op U.1))) r ∈ A 0 := by
        change _ ∈ (SymmetricAlgebra.ι Γ(S, U.1) _).range ^ 0
        simpa only [pow_zero] using (Submodule.algebraMap_mem r)
      exact (congrArg q (DirectSum.decompose_of_mem_same A hr)).symm
    | ι m =>
      have hm : SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1)) m ∈ A 1 := by
        change _ ∈ (SymmetricAlgebra.ι Γ(S, U.1) _).range ^ 1
        simpa only [pow_one] using LinearMap.mem_range_self _ m
      change q _ = q (DirectSum.decompose A _ 0)
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (hp _ hm)).trans
        ((congrArg q (DirectSum.decompose_of_mem_ne A hm
          (by decide : (1 : ℕ) ≠ 0))).trans (map_zero q)).symm
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | mul a b ha hb => simpa only [map_mul] using congrArg₂ (· * ·) ha hb
  apply x.not_irrelevant_le
  intro a ha
  change a ∈ x.asHomogeneousIdeal.toIdeal
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hzero : GradedRing.projZeroRingHom A a = 0 := ha
  change q a = 0
  exact (congrArg (fun t : SymmetricAlgebra Γ(S, U.1) (E.val.obj (op U.1)) →+*
    SymmetricAlgebra Γ(S, U.1) (E.val.obj (op U.1)) ⧸ x.asHomogeneousIdeal.toIdeal ↦
      t a) heq).trans ((congrArg q hzero).trans (map_zero q))

private theorem invertible_of_symmetric_twist_charts {S : Scheme.{u}} (E : S.Modules)
    [E.IsQuasicoherent]
    (L : (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj.Modules)
    (chart : ∀ U : S.affineOpens,
      (Scheme.Modules.tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj L ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1) :
    L.IsInvertible := by
  have hlocal (U : S.affineOpens) :
      ((Scheme.Modules.pullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj L).IsInvertible := by
    have := Proj.isInvertible_twist
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading U) 1
      (symmetric_degree_one_cover E U)
    exact Scheme.Modules.IsInvertible.of_iso ((chart U).symm ≪≫
      (Scheme.Modules.boundaryPullbackComparison
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).app L)
  have hfree := Scheme.Modules.isFiniteLocallyFreeOfRank_of_isOpenImmersion L (r := 1)
    (fun U : S.affineOpens ↦ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)
    (SymmetricAlgebraSheaf.gradedAlgebraData E).iSup_opensRange_relProjι (fun U ↦ by
      have := hlocal U
      exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
        ((Scheme.Modules.pullback
          ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj L)).mp
        (Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
          ((Scheme.Modules.pullback
            ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjι U)).obj L)))
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).mpr hfree
  exact Scheme.Modules.IsInvertible.of_sheafOfModules L

/-- The chart comparison exists on every inclusion of affine base opens.
Source: Stacks, Tags 01NR and 01OB.
(blueprint: lem-trf-symmetric-proj-normalized-descent).

Proof: glue the degree-one affine twists together with their normalized section
map, and take the adjoint quotient. Degree-one standard opens cover symmetric Proj:
a prime containing the generators contains the irrelevant ideal, by induction on
the symmetric algebra. Thus the affine twists, and hence the glued module, are
invertible. The normalized sections give epimorphy. For an affine inclusion, invert
the pulled-back chart over the larger open and compose with the pullback-composition
comparison and the chart over the smaller open. Compatibility is cancellation of
an isomorphism with its inverse. -/
theorem exists_affine_comparison_with_chart_compatibility
    (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent] :
    ∃ D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E,
      ∀ (U V : S.affineOpens) (h : U ≤ V),
        Nonempty (AffineComparison E D U V h) := by
  obtain ⟨L, chart, σ, hσ⟩ := exists_symmetric_twist_sections S E
  let q := ((Scheme.Modules.tensorPullbackSectionAdjunction
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom).homEquiv E L).symm σ
  let D : ProjectiveBundleQuotientGeometry.TautologicalQuotient E :=
    { line := L
      quotient := q
      invertible := invertible_of_symmetric_twist_charts E L chart
      surjective := epi_of_symmetric_twist_sections E L chart σ hσ
      chart := chart
      generator := by
        intro U m hm
        dsimp only [q]
        rw [Equiv.apply_symm_apply]
        exact hσ U m hm }
  exact ⟨D, fun U V h ↦ affineComparison_of_quotient E D U V h⟩

end AlgebraicGeometry.SymmetricProjTautologicalCharts
