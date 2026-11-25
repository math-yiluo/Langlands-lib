/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedTensorComplexCohomologyVanishes
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! # A cohomology gap for tensoring with a perfect complex

Source: Stacks Project, Derived Categories of Schemes, Tag 09M4, proof,
spectral sequence following the choice of Tor amplitude for the dual perfect complex
(blueprint: lem-sc-perfect-hypercohomology-gap).
-/

@[expose] public section

universe uG wG

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_single_homology_vanishes (X : Scheme.{uG})
    [HasDerivedCategory.{wG} (SheafOfModules.{uG} (moduleRings X.toRingedSpace))]
    (P : schemeDerivedCategory X)
    (G : SheafOfModules.{uG} (moduleRings X.toRingedSpace))
    (i : ℤ) (h : schemeDerivedTensorCohomologyVanishes X P G i) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (MonoidalCategory.tensorObj P ((DerivedCategory.singleFunctor _ 0).obj G))) := by
  let := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨K, hK, ⟨eK⟩, hzero⟩ := h
  let N := (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G
  obtain ⟨comparison⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj K)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hK)
  let e := (comparison.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  let e' : MonoidalCategory.tensorObj P ((DerivedCategory.singleFunctor _ 0).obj G) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor K N
        (MonoidalCategory.curriedTensor _)) :=
    (MonoidalCategory.tensorIso eK.symm
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app G)) ≪≫ e
  exact hzero.of_iso
    ((DerivedCategory.homologyFunctor _ i).mapIso e' ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _)

set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- A perfect object of Tor amplitude `[a,b]` tensors a cohomology gap in degrees
`[j-b,j-a]` to vanishing in degree `j`.
Source: Stacks Project, Tag 09M4, spectral sequence in the proof
(blueprint: lem-sc-perfect-hypercohomology-gap).

Proof (the three steps of the node):
1. On affine opens, represent `P` by a bounded strictly perfect complex `Q`
   (lemma-coherent-base-change-invertible-sheaves--1). Its terms are flat
   (def-pc-flat-sheaf-modules), so it is K-flat (lem-pc-bounded-above-flat-kflat,
   def-pc-kflat-complex). Restriction commutes with tensor and preserves K-flatness, using exact
   extension by zero for the latter. Hence `P ⊗ᴸ L` is represented locally by the total tensor of
   `Q` with a representative of `L` (def-pc-tensor-complex-sheaves). The Tor-amplitude hypothesis
   gives `H^p(Q ⊗ H^q(L)) = 0` whenever `p` is outside `[a,b]`.
2. Filter the total tensor by `Q`-degree. The filtration is finite since `Q` is bounded.
   The filtered-complex spectral sequence (thm-sp-spectral-object-yields) has
   `E₁^{p,q} = Q^p ⊗ H^q(L)` by flatness, and its differential comes from `Q`, giving
   `E₂^{p,q} = H^p(Q ⊗ H^q(L))`. On the diagonal `p+q=j`, this is zero outside `[a,b]`
   by Tor amplitude; inside `[a,b]`, `q=j-p` lies in `[j-b,j-a]`, where `H^q(L)=0`.
   Later pages are subquotients, so all limiting terms on that diagonal vanish.
3. Convergence gives a finite filtration of the degree `j` cohomology with all graded
   pieces zero, hence the cohomology is zero locally. The affine opens cover `X`, so
   vanishing of this cohomology sheaf holds globally. -/
theorem perfect_hypercohomology_gap (X : Scheme.{uG})
    [HasDerivedCategory.{wG} (SheafOfModules.{uG} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wG} (SheafOfModules.{uG} ((moduleRings X.toRingedSpace).over U))]
    (P L : schemeDerivedCategory X) (hP : X.IsPerfect P) (a b : ℤ)
    (hTor : ∀ G : SheafOfModules.{uG} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes X P G i)
    (hL : schemeDerivedQCohProperty X L) (j : ℤ)
    (hgap : ∀ q : ℤ, j - b ≤ q → q ≤ j - a →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{uG} (moduleRings X.toRingedSpace)) q).obj L)) :
    schemeDerivedTensorComplexCohomologyVanishes X P L j := by
  classical
  -- The Tor test already supplies all bounds needed; perfection and QCoh are redundant.
  let C := SheafOfModules.{uG} (moduleRings X.toRingedSpace)
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{uG} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, uG, uG} C
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory C
  have hTor' : DerivedCategory.torAmplitudeIn C a b P := by
    intro G
    refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_, (DerivedCategory.isLE_iff _ b).2 ?_⟩
    · intro i hi
      exact tensor_single_homology_vanishes X P G i (hTor G i (Or.inl hi))
    · intro i hi
      exact tensor_single_homology_vanishes X P G i (hTor G i (Or.inr hi))
  let t := DerivedCategory.TStructure.t (C := C)
  let A := (t.truncLT (j - b)).obj L
  let B := (t.truncGE (j - b)).obj L
  have hB : B.IsGE (j - a + 1) := by
    apply (DerivedCategory.isGE_iff _ _).2
    intro q hq
    by_cases hbelow : q < j - b
    · exact DerivedCategory.isZero_of_isGE B (j - b) q hbelow
    · have hiso : IsIso ((DerivedCategory.homologyFunctor C q).map
          ((t.truncGEπ (j - b)).app L)) := by
        apply DerivedCategory.isIso_homologyMap_mor₂ _
          (t.triangleLTGE_distinguished (j - b) L) q (q + 1) (by omega)
        · exact DerivedCategory.isZero_of_isLE A (j - b - 1) q (by omega)
        · exact DerivedCategory.isZero_of_isLE A (j - b - 1) (q + 1) (by omega)
      exact (hgap q (by omega) (by omega)).of_iso
        (asIso ((DerivedCategory.homologyFunctor C q).map
          ((t.truncGEπ (j - b)).app L))).symm
  have hA : A.IsLE (j - b - 1) := inferInstance
  have hleft := DerivedCategory.isLE_tensor_of_torAmplitudeIn hTor' A (j - b - 1)
  have hright := DerivedCategory.isGE_tensor_of_torAmplitudeIn hTor' B (j - a + 1)
  have hzleft :
      IsZero ((DerivedCategory.homologyFunctor C j).obj (MonoidalCategory.tensorObj P A)) :=
    DerivedCategory.isZero_of_isLE _ (b + (j - b - 1)) j (by omega)
  have hzright :
      IsZero ((DerivedCategory.homologyFunctor C j).obj (MonoidalCategory.tensorObj P B)) :=
    DerivedCategory.isZero_of_isGE _ (a + (j - a + 1)) j (by omega)
  obtain ⟨S, hSge, hSle, hSflat, ⟨eS⟩⟩ :=
    DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hTor'
  have hSk := CochainComplex.kFlat_of_bounded_of_flat S a b hSflat
  let S' := (HomotopyCategory.quotient C (.up ℤ)).obj S
  have hS' : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat S' :=
    (HomotopyCategory.kFlat_quotient_obj_iff S).2 hSk
  let := DerivedCategory.commShiftTensorLeftQhObj S' hS'
  have := DerivedCategory.isTriangulated_tensorLeftQhObj S' hS'
  let eS' : DerivedCategory.Qh.obj S' ≅ P :=
    (DerivedCategory.quotientCompQhIso C).app S ≪≫ eS
  let eF := (MonoidalCategory.curriedTensor (schemeDerivedCategory X)).mapIso eS'
  let := Functor.CommShift.ofIso eF ℤ
  have := Functor.CommShift.ofIso_compatibility eF ℤ
  have := Functor.isTriangulated_of_iso eF
  let T :=
    (MonoidalCategory.tensorLeft P).mapTriangle.obj ((t.triangleLTGE (j - b)).obj L)
  have hT : T ∈ distTriang (schemeDerivedCategory X) :=
    Functor.map_distinguished _ _ (t.triangleLTGE_distinguished (j - b) L)
  have hz :
      IsZero ((DerivedCategory.homologyFunctor C j).obj (MonoidalCategory.tensorObj P L)) := by
    exact (DerivedCategory.HomologySequence.exact₂ T hT j).isZero_X₂
      (hzleft.eq_of_src _ _) (hzright.eq_of_tgt _ _)
  obtain ⟨K, hK, ⟨eK⟩, _⟩ := hTor
    ((DerivedCategory.homologyFunctor C 0).obj L) (a - 1) (Or.inl (by omega))
  let N := DerivedCategory.Q.objPreimage L
  let eN : DerivedCategory.Q.obj N ≅ L := DerivedCategory.Q.objObjPreimageIso L
  obtain ⟨comparison⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const (Discrete PUnit.{1})).obj K)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hK)
  let e := (comparison.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  refine ⟨K, N, hK, ⟨eK⟩, ⟨eN⟩, ?_⟩
  exact hz.of_iso
    (((DerivedCategory.homologyFunctorFactors C j).app _).symm ≪≫
      (DerivedCategory.homologyFunctor C j).mapIso (e.symm ≪≫ MonoidalCategory.tensorIso eK eN))

end AlgebraicGeometry
