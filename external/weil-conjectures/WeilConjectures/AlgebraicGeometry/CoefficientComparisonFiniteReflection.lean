/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import WeilConjectures.AlgebraicGeometry.CoefficientComparisonConstantChartReflection
import WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-! # Reflection of finite local systems on the coefficient-sized models
Source: Stacks Project, Tags 099Y, 099R and 03CY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance 20000] chartModuleSheafify chartWeakModuleSheafify

private theorem comparison_coversTop_reflect (X : Scheme.{u})
    {I : Type (max v (u + 1))}
    (V : I → Scheme.smallModelComparisonEtaleSite.{u, v} X)
    (hV : (Scheme.coefficientProEtaleModelTopology.{u, v} X).CoversTop
      (fun i ↦ (Scheme.smallModelComparisonInclusion.{u, v} X).obj (V i))) :
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X).CoversTop V := by
  classical
  let D : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt := AsSmall.down
  let U : I → X.Etale := fun i ↦ AsSmall.down.obj (V i)
  let T : X.ProEt := Scheme.ProEt.mk (𝟙 X)
  have hT : Sieve.ofObjects (fun i ↦ (Scheme.toProEt X).obj (U i)) T ∈
      Scheme.ProEt.topology X T := by
    apply (Scheme.ProEt.topology X).superset_covering _
      ((CoverPreserving.of_isContinuous D _ _).cover_preserve
        (hV (AsSmall.up.obj T)))
    rintro W f ⟨Y, g, q, ⟨i, ⟨a⟩⟩, _⟩
    exact ⟨i, ⟨q ≫ D.map a⟩⟩
  have hsurj : ∀ x : X, ∃ (i : I) (y : (U i).left), (U i).hom y = x := by
    intro x
    obtain ⟨S, hS, hle⟩ := Scheme.ProEt.mem_topology_iff.mp hT
    obtain ⟨ι, Z, f, rfl⟩ := S.exists_eq_ofArrows
    have hS' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
        Scheme.proetalePrecoverage T.left := by
      simpa only [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
        Functor.comp_obj, Functor.comp_map, Scheme.ProEt.forget,
        MorphismProperty.Over.forget, MorphismProperty.Comma.forget, Over.forget,
        Comma.fst] using hS
    obtain ⟨j, y, hy⟩ :=
      ((Scheme.ofArrows_mem_precoverage_iff _).mp
        (Scheme.propQCPrecoverage_le_precoverage _ hS')).1 (show T.left from x)
    obtain ⟨i, ⟨q⟩⟩ := hle _ (f j) ⟨j⟩
    refine ⟨i, q.left y, ?_⟩
    have hw : q.left ≫ (U i).hom = (Z j).hom := MorphismProperty.Over.w q
    calc
      (U i).hom (q.left y) = (q.left ≫ (U i).hom) y := rfl
      _ = (Z j).hom y := congrArg (fun t : (Z j).left ⟶ X ↦ t y) hw
      _ = T.hom ((f j).left y) :=
        congrArg (fun t : (Z j).left ⟶ X ↦ t y) (MorphismProperty.Over.w (f j)).symm
      _ = x := by rw [hy]; rfl
  have hU : X.smallEtaleTopology.CoversTop U := by
    let T' : X.Etale := Scheme.Etale.mk (𝟙 X)
    let f : ∀ i, U i ⟶ T' := fun i ↦ MorphismProperty.Over.homMk (U i).hom (by
      change (U i).hom ≫ 𝟙 X = (U i).hom
      exact Category.comp_id _)
    apply (X.smallEtaleTopology.coversTop_iff_of_isTerminal T'
      (MorphismProperty.Over.mkIdTerminal _ X) U).mpr
    apply X.smallEtaleTopology.superset_covering (Sieve.ofArrows_le_ofObjects U f)
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff f).mpr
    exact Set.eq_univ_of_forall (fun x ↦ by
      obtain ⟨i, y, hy⟩ := hsurj x
      exact Set.mem_iUnion.mpr ⟨i, y, hy⟩)
  intro W
  let E : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale := AsSmall.down
  let : E.IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  apply (Scheme.smallModelComparisonEtaleTopology.{u, v} X).superset_covering _
    (E.cover_lift _ _ (hU (E.obj W)))
  rintro Y f ⟨i, ⟨q⟩⟩
  exact ⟨i, ⟨AsSmall.up.map q⟩⟩

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- A fixed-scalar etale module whose comparison is a finite local system is itself
a finite local system. This is the single-stratum assertion, with no stratification
or intrinsic-module inverse image in its statement.
Source: Stacks Tags 099Y and 099T
(auxiliary; not a blueprint node).

Proof: over a Noetherian ring every finite local model is finitely presented.
Apply coefficientFpLocalSystem_etaleCover to obtain etale charts whose images
cover the pro-etale site and carry specified constant finitely presented models.
Reflect this covering family: a generating pro-etale precover of the terminal
object proves joint surjectivity, which is the etale covering criterion. Transport
this calculation through the AsSmall site equivalences. On each chart apply
coefficientComparison_constant_over_reflect with the same module. For an arbitrary
object W use the covering sieve Sieve.ofObjects V W. Each member factors through
one of the etale charts; restriction preserves that chart's constant module.
Finite presentation implies finite generation, giving the required local models.
No model is resized, and the argument includes empty schemes, empty charts and
the zero module. -/
theorem coefficientComparison_finite_reflect (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (F : Sheaf (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (h : IsCoefficientModelLocallyConstantFinite
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A
      ((Functor.sheafPullbackConstruction.sheafPullback
        (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
        (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
        (Scheme.coefficientProEtaleModelTopology.{u, v} X)).obj F)) :
    IsCoefficientModelLocallyConstantFinite
      (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A F := by
  let P := Functor.sheafPullbackConstruction.sheafPullback
    (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
    (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
    (Scheme.coefficientProEtaleModelTopology.{u, v} X)
  have hfp : ∀ V : Scheme.coefficientProEtaleSiteModel.{u, v} X,
      ∃ S : Sieve V, S ∈ Scheme.coefficientProEtaleModelTopology.{u, v} X V ∧
        ∀ (U : Scheme.coefficientProEtaleSiteModel.{u, v} X) (f : U ⟶ V), S f →
          ∃ M : ModuleCat.{max v (u + 1)} A, Module.FinitePresentation A M ∧
            Nonempty ((P.obj F).over U ≅
              (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, v} X).over U)
                (ModuleCat.{max v (u + 1)} A)).obj M) := by
    intro V
    obtain ⟨S, hS, hm⟩ := h V
    refine ⟨S, hS, fun U f hf ↦ ?_⟩
    obtain ⟨M, hM, he⟩ := hm U f hf
    have := hM
    exact ⟨M, Module.finitePresentation_of_finite A M, he⟩
  obtain ⟨I, V, hV, hm⟩ := coefficientFpLocalSystem_etaleCover X A (P.obj F) hfp
  have hc := comparison_coversTop_reflect X V hV
  intro W
  refine ⟨Sieve.ofObjects V W, hc W, ?_⟩
  rintro U f ⟨i, ⟨q⟩⟩
  obtain ⟨M, hM, ⟨e⟩⟩ := hm i
  have := hM
  obtain ⟨e'⟩ := coefficientComparison_constant_over_reflect X A F (V i) M e
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let e₁ := (J.overMapPullback (ModuleCat.{max v (u + 1)} A) q).mapIso e'
  let e₂ := ((Over.map q).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{max v (u + 1)} A) (J.over U) (J.over (V i))).symm.app
      ((Functor.const (Over (V i))ᵒᵖ).obj M)
  exact ⟨M, inferInstance, ⟨(Sheaf.pushforwardOverMapIso _ q).symm ≪≫ e₁ ≪≫ e₂⟩⟩

end AlgebraicGeometry.ProEtale
