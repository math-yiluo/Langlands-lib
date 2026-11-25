/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjTautologicalCharts
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.LineQuotientChartInversePullback
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleSeparated
import WeilConjectures.AlgebraicGeometry.Line.LineQuotientTrivializedCoefficients

/-!
# Projective bundles classify invertible quotients

## References

* Stacks Project, Constructions, Tags 01OA, 01OB, 01O4, 01O9, 01OD and 01OE
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProjectiveBundleQuotientGeometry

open Scheme.Modules

/-- Projective bundles of arbitrary quasi-coherent modules represent invertible
quotients, naturally under arbitrary scheme pullback, with the prescribed twists,
open-base identifications, separated projection and free-module polynomial models. -/
theorem projective_bundle_quotient_geometry (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] :
    ∃ D : TautologicalQuotient E,
      IsSeparated (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L),
        L.IsInvertible → Epi q →
        ∃! a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj,
          Classifies D h L q a) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj)
        (ha : a ≫ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom = h),
        ((Scheme.Modules.tensorPullback a).obj D.line).IsInvertible ∧
          Epi (pulledQuotient D h a ha)) ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
        L.IsInvertible → Epi q → Classifies D h L q a → IsCanonicalMap h L q a) ∧
      (∀ (T T' : Scheme.{u}) (h : T ⟶ S) (u : T' ⟶ T) (L : T.Modules)
        (q : (Scheme.Modules.tensorPullback h).obj E ⟶ L)
        (a : T ⟶ (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj),
        L.IsInvertible → Epi q → Classifies D h L q a →
          Classifies D (u ≫ h) ((Scheme.Modules.tensorPullback u).obj L)
            ((Scheme.Modules.tensorPullbackSectionComp u h).hom.app E ≫
              (Scheme.Modules.tensorPullback u).map q) (u ≫ a)) ∧
      HasOpenCompatibility D ∧ HasFreeCompatibility D := by
  obtain ⟨D, hDopen, hDfree, _⟩ :=
    SymmetricProjTautologicalCharts.symmetric_proj_tautological_chart_gluing S E
  obtain ⟨hback, hforward⟩ := line_quotient_chart_inverse_pullback E D
  have hclassifies (T : Scheme.{u}) (h : T ⟶ S) (L : T.Modules)
      (q : (tensorPullback h).obj E ⟶ L) [L.IsInvertible] [Epi q] :
      ∃! a, Classifies D h L q a := by
    obtain ⟨ψ, hψ, _, _, F, hF, _, _, _⟩ :=
      line_quotient_homogeneous_fraction_map h E L q
    obtain ⟨hFp, θ, hθ, _, _, _⟩ := hforward T h L inferInstance q inferInstance ψ F hψ hF
    refine ⟨F, ⟨hFp, θ, hθ⟩, ?_⟩
    rintro a ⟨ha, v, hv⟩
    obtain ⟨hLa, hqa, _, hrecover⟩ := hback T h a ha
    obtain ⟨ψa, hψa, _, _, Fa, hFa, _, _, _⟩ :=
      line_quotient_homogeneous_fraction_map h E _ (pulledQuotient D h a ha)
    obtain ⟨_, _, _, _, hchange, _⟩ :=
      hforward T h _ hLa (pulledQuotient D h a ha) hqa ψa Fa hψa hFa
    exact (hrecover ψa Fa hψa hFa).1.symm.trans
      (hchange L v q hv ψ F hψ hF).1.symm
  refine ⟨D, isSeparated_projectiveBundle E, ?_, ?_, ?_, ?_, hDopen, hDfree⟩
  · intro T h L q hL hq
    exact hclassifies T h L q
  · intro T h a ha
    exact ⟨(hback T h a ha).1, (hback T h a ha).2.1⟩
  · intro T h L q a hL hq ha
    obtain ⟨ψ, hψ, _, _, F, hF, _, hcanonical, _⟩ :=
      line_quotient_homogeneous_fraction_map h E L q
    obtain ⟨hFp, θ, hθ, _⟩ := hforward T h L hL q hq ψ F hψ hF
    have haF : a = F := (hclassifies T h L q).unique ha ⟨hFp, θ, hθ⟩
    subst a
    intro V W hWV e
    obtain ⟨α, hαscalar, hαgenerator, hαhomogeneous, hα⟩ :=
      line_quotient_trivialized_coefficients h E L q ψ hψ V W hWV e
    refine ⟨α, hαscalar, hαgenerator, hα, ?_⟩
    exact hcanonical.2 W.1.toScheme W.1.ι inferInstance V
      (by simpa only [W.1.ι_preimage_self] using W.1.ι.preimage_mono hWV)
      e α hαhomogeneous hα
  · intro T T' h u L q a hL hq ha
    obtain ⟨ψ, hψ, _, _, F, hF, _, _, _⟩ :=
      line_quotient_homogeneous_fraction_map h E L q
    obtain ⟨hFp, θ, hθ, _, _, hnatural⟩ :=
      hforward T h L hL q hq ψ F hψ hF
    have haF : a = F := (hclassifies T h L q).unique ha ⟨hFp, θ, hθ⟩
    subst a
    obtain ⟨hLu, hqu, hnu⟩ := hnatural T' u
    obtain ⟨ψu, hψu, _, _, Fu, hFu, _, _, _⟩ :=
      line_quotient_homogeneous_fraction_map (u ≫ h) E _ (lineQuotientPullback h u E L q)
    obtain ⟨hFup, θu, hθu, _⟩ :=
      hforward T' (u ≫ h) _ hLu (lineQuotientPullback h u E L q) hqu ψu Fu hψu hFu
    have heq := (hnu ψu Fu hψu hFu).choose
    rw [← heq]
    exact ⟨hFup, θu, hθu⟩

end AlgebraicGeometry.ProjectiveBundleQuotientGeometry
