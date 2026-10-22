import Langlands.Cohomology.CyclicH2.BarComparison
import Langlands.Cohomology.CyclicH2.ExtComparison
import Langlands.Cohomology.CyclicH2.Statement

open CategoryTheory

namespace Langlands.Cohomology.CyclicH2

universe u

section ShortComplex

variable {k : Type u} [CommRing k]

lemma shortComplex_homologyMap_class
    {S T : ShortComplex (ModuleCat k)} (α : S ⟶ T)
    (z : S.cycles) (x : LinearMap.ker T.g.hom)
    (hx : α.τ₂ (S.iCycles z) = x) :
    ShortComplex.homologyMap α (S.homologyπ z) =
      T.homologyπ (T.moduleCatCyclesIso.inv x) := by
  have hz : ShortComplex.cyclesMap α z = T.moduleCatCyclesIso.inv x := by
    apply (ModuleCat.mono_iff_injective T.iCycles).1 inferInstance
    change (ShortComplex.cyclesMap α ≫ T.iCycles) z =
      (T.moduleCatCyclesIso.inv ≫ T.iCycles) x
    rw [ShortComplex.cyclesMap_i, ShortComplex.moduleCatCyclesIso_inv_iCycles]
    exact hx
  calc
    _ = T.homologyπ (ShortComplex.cyclesMap α z) :=
      congrArg (fun f => f z) (ShortComplex.homologyπ_naturality α)
    _ = _ := congrArg T.homologyπ hz

end ShortComplex

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

open Rep.FiniteCyclicGroup

noncomputable def comparisonCochainMap (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (φ : (resolution k g hg).complex ⟶ Rep.barComplex k G) :
    groupCohomology.inhomogeneousCochains A ⟶ moduleCatCochainComplex A g :=
  (groupCohomology.inhomogeneousCochainsIso A).hom ≫ precompMap A φ ≫
    (homResolutionIso A g hg).hom

set_option backward.isDefEq.respectTransparency false in
lemma comparisonCochainMap_f_two (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (φ : (resolution k g hg).complex ⟶ Rep.barComplex k G)
    (h₂ : (φ.f 2).hom (MonoidAlgebra.single 1 1) =
      ∑ i ∈ Finset.range (Fintype.card G),
        Finsupp.single ![g ^ i, g] (MonoidAlgebra.single 1 1))
    (c : groupCohomology.cocycles₂ A) :
    (comparisonCochainMap A g hg φ).f 2
      (groupCohomology.iCocycles A 2 ((groupCohomology.isoCocycles₂ A).inv c)) =
      ∑ i ∈ Finset.range (Fintype.card G), c (g ^ i, g) := by
  rw [groupCohomology.isoCocycles₂_inv_comp_iCocycles_apply]
  change (Rep.freeLift k G A ((groupCohomology.cochainsIso₂ A).inv c)).hom
    ((φ.f 2).hom (MonoidAlgebra.single 1 1)) = _
  rw [h₂, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Rep.freeLift, groupCohomology.cochainsIso₂]

noncomputable def cyclicEvenScIso (A : Rep k G) (g : G) :
    (moduleCatCochainComplex A g).sc 2 ≅ normHomCompSub A g :=
  HomologicalComplex.alternatingConstScIsoEven (ModuleCat.of k A.V)
    (by ext; simp [Rep.sub_hom]) (by ext; simp [Rep.sub_hom])
    (fun _ _ => ComplexShape.up_nat_odd_add) (by simp) (by simp) (by decide)

noncomputable def comparisonShortComplexMap (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (φ : (resolution k g hg).complex ⟶ Rep.barComplex k G) :
    (groupCohomology.inhomogeneousCochains A).sc 2 ⟶ normHomCompSub A g :=
  (HomologicalComplex.shortComplexFunctor _ _ 2).map (comparisonCochainMap A g hg φ) ≫
    (cyclicEvenScIso A g).hom

set_option backward.isDefEq.respectTransparency false in
lemma comparisonShortComplexMap_homologyMap (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (φ : (resolution k g hg).complex ⟶ Rep.barComplex k G)
    (h₀ : φ.f 0 ≫ (Rep.barResolution k G).π.f 0 = (resolution k g hg).π.f 0) :
    ShortComplex.homologyMap (comparisonShortComplexMap A g hg φ) =
      (groupCohomologyIsoEven A g hg 2 (by decide)).hom := by
  unfold groupCohomologyIsoEven
  rw [Iso.trans_hom, Iso.trans_hom, groupCohomologyIso_hom_eq A 2 _ φ h₀]
  simp only [comparisonShortComplexMap, ShortComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap (comparisonCochainMap A g hg φ) 2 ≫ _ = _
  simp only [comparisonCochainMap, HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma cocycleSumComparison_of_chainMap (A : Rep k G) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (φ : (resolution k g hg).complex ⟶ Rep.barComplex k G)
    (h₀ : φ.f 0 ≫ (Rep.barResolution k G).π.f 0 = (resolution k g hg).π.f 0)
    (h₂ : (φ.f 2).hom (MonoidAlgebra.single 1 1) =
      ∑ i ∈ Finset.range (Fintype.card G),
        Finsupp.single ![g ^ i, g] (MonoidAlgebra.single 1 1))
    (c : groupCohomology.cocycles₂ A)
    (x : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (hx : (x : A) = ∑ i ∈ Finset.range (Fintype.card G), c (g ^ i, g)) :
    groupCohomology.H2π A c = groupCohomologyπEven A g hg 2 (by decide) x := by
  have heval : (comparisonShortComplexMap A g hg φ).τ₂
      ((groupCohomology.inhomogeneousCochains A).iCycles 2
        ((groupCohomology.isoCocycles₂ A).inv c)) = x := by
    change (comparisonCochainMap A g hg φ).f 2
      (groupCohomology.iCocycles A 2 ((groupCohomology.isoCocycles₂ A).inv c)) = (x : A)
    exact (comparisonCochainMap_f_two A g hg φ h₂ c).trans hx.symm
  have h := shortComplex_homologyMap_class (comparisonShortComplexMap A g hg φ)
    ((groupCohomology.isoCocycles₂ A).inv c) x heval
  rw [comparisonShortComplexMap_homologyMap A g hg φ h₀] at h
  apply (ModuleCat.mono_iff_injective
    (groupCohomologyIsoEven A g hg 2 (by decide)).hom).1 inferInstance
  change (groupCohomologyIsoEven A g hg 2 (by decide)).hom
    (groupCohomology.H2π A c) =
      ((ShortComplex.moduleCatCyclesIso (normHomCompSub A g)).inv ≫
        (normHomCompSub A g).homologyπ ≫
        (groupCohomologyIsoEven A g hg 2 (by decide)).inv ≫
        (groupCohomologyIsoEven A g hg 2 (by decide)).hom) x
  rw [Iso.inv_hom_id, Category.comp_id]
  exact h

/-- The class of an arbitrary two-cocycle is its generator cycle sum under Mathlib's actual
finite cyclic comparison. -/
theorem cocycleSumComparison : CocycleSumComparison.{u} := by
  intro k G _ _ _ A g hg c x hx
  exact cocycleSumComparison_of_chainMap A g hg (cyclicToBar k g hg)
    (cyclicToBar_f_zero_comp_π k g hg) (cyclicToBar_f_two_single k g hg) c x hx

end Langlands.Cohomology.CyclicH2
