/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FreeCechTupleBasis
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-! # Differential compatibility of the free Čech tuple map

Source: Stacks Project, Tags 03AT and 03F5.
(blueprint: lem-weil-pbc-free-cech-differential-compatibility)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem tupleGenerator_face (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) (n : ℕ) (φ : W ⟶ U₀)
    (x : Fin (n + 2) → freeCechLifts X ι U₀ U f W φ) (j : Fin (n + 2)) :
    (((freeCechModule X ι U₀ U f O).δ j).app (op W))
      (freeCechTupleGenerator X ι U₀ U f O W (n + 1) φ x) =
    freeCechTupleGenerator X ι U₀ U f O W n φ
      (Algebra.powerSetComplexFace _ j x) := by
  classical
  let i : Fin (n + 2) → ι := fun a ↦ (x a).1
  let F (k : ℕ) (i : Fin (k + 1) → ι) :=
    (PresheafOfModules.free O).obj
      (yoneda.obj ((∏ᶜ (fun a ↦ Over.mk (f (i a)))).left))
  let g : Over.mk φ ⟶ ∏ᶜ (fun a ↦ Over.mk (f (i a))) :=
    Pi.lift (fun a ↦ Over.homMk (x a).2.1 (x a).2.2)
  let p (i : Fin (n + 2) → ι) :
      (∏ᶜ (fun a ↦ Over.mk (f (i a)))) ⟶
        ∏ᶜ (fun a ↦ Over.mk (f (i (j.succAbove a)))) :=
    Pi.lift (fun a ↦ Pi.π (fun a ↦ Over.mk (f (i a))) (j.succAbove a))
  change ((Sigma.desc (fun i ↦
    (PresheafOfModules.free O).map (yoneda.map (p i).left) ≫
      Sigma.ι (F n) (i ∘ j.succAbove))).app (op W))
        (((Sigma.ι (F (n + 1)) i).app (op W)) (ModuleCat.freeMk g.left)) = _
  rw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app, Sigma.ι_comp_desc]
  simp only [PresheafOfModules.comp_app, ModuleCat.comp_apply,
    PresheafOfModules.free_map_app]
  dsimp only [yoneda_map_app, types_comp_apply]
  have hfree := ModuleCat.free_map_apply (R := O.obj (op W))
    (↾fun h : W ⟶ (∏ᶜ (fun a ↦ Over.mk (f (i a)))).left ↦ h ≫ (p i).left) g.left
  have hfree' := congrArg (((Sigma.ι (F n) (i ∘ j.succAbove)).app (op W))) hfree
  refine hfree'.trans ?_
  change ((Sigma.ι (F n) (i ∘ j.succAbove)).app (op W))
    (ModuleCat.freeMk (g.left ≫ (p i).left)) = _
  have hg : g ≫ p i = Pi.lift (fun a ↦
      Over.homMk (x (j.succAbove a)).2.1 (x (j.succAbove a)).2.2) := by
    apply Pi.hom_ext
    intro a
    simp [g, p]
  change ((Sigma.ι (F n) (i ∘ j.succAbove)).app (op W))
    (ModuleCat.freeMk (g ≫ p i).left) = _
  rw [hg]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The tuple map commutes with the alternating differential.
Source: Stacks Project, Tags 03AT and 03F5, the direct-sum decomposition.
Proof: Both sides are linear maps on a direct sum of free modules. Check their
values on a generator DFinsupp.single φ (Finsupp.single x r). The tuple map sends
this generator to r times the coproduct injection of the free generator associated
with the compatible tuple x. The n-th differential is the sum over j in Fin (n+2)
of (-1)^j times the j-th face. A face reindexes the indices along Fin.succAbove j
and postcomposes the product map with the corresponding product projection.
The equations Pi.lift_comp_π in Over U₀ identify that composite with the product map
for the tuple with its j-th entry omitted. Thus every summand is r times the
same generator with the same sign on both sides. The block index φ is preserved.
The integer sign action agrees with multiplication by the corresponding power
of -1 in O(W), including for noncommutative rings. Extend the equality by the
Finsupp and DFinsupp universal properties. Empty families and the zero ring
are included, since no basis element or nonzero scalar is required.
(blueprint: lem-weil-pbc-free-cech-differential-compatibility) -/
theorem freeCechDifferential_compatibility (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale)
    (U : ι → X.Etale) (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u})
    (W : X.Etale) :
    let M := freeCechModule X ι U₀ U f O
    let K := (((PresheafOfModules.evaluation O (op W)).mapHomologicalComplex _).obj
      ((AlgebraicTopology.alternatingFaceMapComplex _).obj M))
    let b := freeCechTupleMap X ι U₀ U f O W
    let D := fun n ↦ DFinsupp.mapRange.linearMap
      (fun φ ↦ Algebra.powerSetComplexDifferential (O.obj (op W))
        (freeCechLifts X ι U₀ U f W φ) n)
    ∀ n, (K.d (n + 1) n).hom.comp (b (n + 1)) = (b n).comp (D n) := by
  classical
  dsimp
  intro n
  simp only [
    AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  apply DFinsupp.lhom_ext'
  intro φ
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  change (((PresheafOfModules.evaluation O (op W)).map
    (AlgebraicTopology.AlternatingFaceMapComplex.objD
      (freeCechModule X ι U₀ U f O) n)).hom) (freeCechTupleMap X ι U₀ U f O W (n + 1)
    (DFinsupp.single φ (Finsupp.single x 1))) =
      freeCechTupleMap X ι U₀ U f O W n
        ((DFinsupp.mapRange.linearMap (fun ψ ↦
          Algebra.powerSetComplexDifferential (O.obj (op W))
            (freeCechLifts X ι U₀ U f W ψ) n))
              (DFinsupp.single φ (Finsupp.single x 1)))
  rw [freeCechTupleMap_single, one_smul]
  simp only [AlgebraicTopology.AlternatingFaceMapComplex.objD,
    Functor.map_sum, Functor.map_zsmul, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply]
  have hD : (DFinsupp.mapRange.linearMap (fun ψ ↦
      Algebra.powerSetComplexDifferential (O.obj (op W))
        (freeCechLifts X ι U₀ U f W ψ) n))
        (DFinsupp.single φ (Finsupp.single x 1)) =
      DFinsupp.single φ (∑ j : Fin (n + 2),
        ((-1 : O.obj (op W)) ^ (j : ℕ)) •
          Finsupp.single (Algebra.powerSetComplexFace _ j x) 1) := by
    change DFinsupp.mapRange _ (fun ψ ↦ LinearMap.map_zero _)
      (DFinsupp.single φ _) = _
    rw [DFinsupp.mapRange_single]
    congr 1
    simp [Algebra.powerSetComplexDifferential, Finsupp.lift_apply]
  rw [hD]
  change _ = ((freeCechTupleMap X ι U₀ U f O W n).comp (DFinsupp.lsingle φ)) _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [LinearMap.comp_apply, DFinsupp.lsingle_apply, map_smul,
    freeCechTupleMap_single, one_smul]
  change ((-1 : ℤ) ^ (j : ℕ)) •
    (((freeCechModule X ι U₀ U f O).δ j).app (op W))
      (freeCechTupleGenerator X ι U₀ U f O W (n + 1) φ x) = _
  rw [tupleGenerator_face]
  rw [← Int.cast_smul_eq_zsmul (O.obj (op W))]
  simp

end AlgebraicGeometry
