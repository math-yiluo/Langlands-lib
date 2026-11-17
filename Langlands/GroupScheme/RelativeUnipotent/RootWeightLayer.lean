import Langlands.GroupScheme.RelativeUnipotent.RootWeightFiltration

/-! # Exact-weight additive coordinates at positive cutoffs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

open LocalSplitCell Langlands.GroupTheory
open Langlands.GroupScheme.RelativeRoot.CentralExtension

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} {C : RootHeightChart U}
    (W : RootWeightData C)

/-- The exact-weight indices, including an empty layer. -/
def exactSupport (d : ℕ) : Set (Fin C.dimension) := {k | W.weight k = d + 1}

def exactEnumeration (d : ℕ) : Fin (Nat.card (W.exactSupport d)) ≃ W.exactSupport d :=
  (Finite.equivFin (W.exactSupport d)).symm

/-- The parameter homomorphism on an exact-weight factor. -/
def exactParameter (T : Over (Spec (CommRingCat.of R))) (d : ℕ)
    (k : Fin C.dimension) :
    HeightLayer.exactFactor (rootFactor C.roots ULift.up T) W.weight (d + 1) k →*
      Multiplicative Γ(T.left, ⊤) :=
  (C.rootEquiv T k).symm.toMonoidHom.comp
    (Subgroup.inclusion (HeightLayer.exactFactor_le _ _ (d + 1) k))

/-- Extract the additive parameters of the exact-weight factor product. -/
def exactParameters (T : Over (Spec (CommRingCat.of R))) (d : ℕ) :
    (∀ k, HeightLayer.exactFactor (rootFactor C.roots ULift.up T) W.weight (d + 1) k) →*
      Multiplicative (Fin (Nat.card (W.exactSupport d)) → Γ(T.left, ⊤)) where
  toFun a := Multiplicative.ofAdd fun j =>
    (W.exactParameter T d (W.exactEnumeration d j).val
      (a (W.exactEnumeration d j).val)).toAdd
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    exact congrArg Multiplicative.toAdd (map_one (W.exactParameter T d _))
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext j
    exact congrArg Multiplicative.toAdd (map_mul (W.exactParameter T d _) (a _) (b _))

/-- The exact-weight coordinate map is a homomorphism, obtained from the actual
successive group quotient and its factor-product isomorphism. -/
def layerCoordinates (T : Over (Spec (CommRingCat.of R))) (d : ℕ) :
    HeightFiltration.level (rootFactor C.roots ULift.up T) W.weight (d + 1) →*
      Multiplicative (Fin (Nat.card (W.exactSupport d)) → Γ(T.left, ⊤)) :=
  (W.exactParameters T d).comp
    (((HeightLayer.layerEquivOfPos (rootFactor C.roots ULift.up T) W.weight
      (W.commutator T) (C.ordered_factors_injective T) (d + 1) (Nat.zero_lt_succ d)).symm.toMonoidHom).comp
        (HeightLayer.projection _ _ (W.commutator T) (d + 1)))

/-- The exact-weight root factors of the coordinates of an ambient point. -/
def coordinateFactors (T : Over (Spec (CommRingCat.of R))) (d : ℕ) (x : T ⟶ U.X) :
    ∀ k, HeightLayer.exactFactor (rootFactor C.roots ULift.up T) W.weight (d + 1) k :=
  fun k => if hk : W.weight k = d + 1 then
    ⟨rootPoint (C.roots (ULift.up k)) T (C.coordinates T x k),
      (HeightLayer.exactFactor_of_eq (rootFactor C.roots ULift.up T) W.weight hk).symm ▸
        mem_rootFactor C.roots ULift.up T k _⟩ else 1

/-- A positive-weight subgroup point and its exact-weight factors have the same class
in the successive quotient. -/
theorem layerMap_coordinateFactors (T : Over (Spec (CommRingCat.of R)))
    (d : ℕ)
    (g : HeightFiltration.level (rootFactor C.roots ULift.up T) W.weight (d + 1)) :
    HeightLayer.layerMap _ _ (W.commutator T) (d + 1) (Nat.zero_lt_succ d)
      (W.coordinateFactors T d g.val) =
        HeightLayer.projection _ _ (W.commutator T) (d + 1) g := by
  let H := rootFactor C.roots ULift.up T
  let c := C.coordinates T (g : T ⟶ U.X)
  have hlow : ∀ k, W.weight k < d + 1 → c k = 0 :=
    (W.mem_subgroup_iff T d g.val).mp g.property
  have hcLevel (k : Fin C.dimension) :
      rootPoint (C.roots (ULift.up k)) T (c k) ∈ HeightFiltration.level H W.weight (d + 1) := by
    rcases lt_or_ge (W.weight k) (d + 1) with hk | hk
    · rw [hlow k hk, rootPoint_zero]
      exact one_mem _
    · exact HeightFiltration.le_level _ _ hk (mem_rootFactor C.roots ULift.up T k _)
  let b : Fin C.dimension → HeightFiltration.level H W.weight (d + 1) :=
    fun k => ⟨rootPoint (C.roots (ULift.up k)) T (c k), hcLevel k⟩
  have hprod : (List.ofFn b).prod = g := by
    apply Subtype.ext
    change (HeightFiltration.level H W.weight (d + 1)).subtype ((List.ofFn b).prod) = _
    rw [map_list_prod, List.map_ofFn]
    exact C.orderedProduct_coordinates T g.val
  have hcoord (k : Fin C.dimension) :
      HeightLayer.coordinateMap H W.weight (W.commutator T) (d + 1) k
        (W.coordinateFactors T d g.val k) =
      HeightLayer.projection H W.weight (W.commutator T) (d + 1) (b k) := by
    by_cases hk : W.weight k = d + 1
    · simp only [coordinateFactors, dite_eq_left hk]
      rfl
    · simp only [coordinateFactors, dite_eq_right hk, map_one]
      symm
      apply (HeightLayer.projection_eq_one_iff H W.weight (W.commutator T) (d + 1) _).mpr
      change rootPoint (C.roots (ULift.up k)) T (c k) ∈
        HeightFiltration.level H W.weight (d + 2)
      rcases lt_or_gt_of_ne hk with hk' | hk'
      · rw [hlow k hk', rootPoint_zero]
        exact one_mem _
      · exact HeightFiltration.le_level _ _ (by omega)
          (mem_rootFactor C.roots ULift.up T k _)
  change (List.ofFn fun k => HeightLayer.coordinateMap H W.weight (W.commutator T) (d + 1) k
    (W.coordinateFactors T d g.val k)).prod = _
  simp_rw [hcoord]
  rw [← hprod, map_list_prod, List.map_ofFn]
  rfl

/-- The quotient-defined homomorphism reads exactly the coordinates of the
specified height in the original ordered scheme chart. -/
theorem layerCoordinates_apply (T : Over (Spec (CommRingCat.of R)))
    (d : ℕ)
    (g : HeightFiltration.level (rootFactor C.roots ULift.up T) W.weight (d + 1))
    (j : Fin (Nat.card (W.exactSupport d))) :
    (W.layerCoordinates T d g).toAdd j =
      C.coordinates T g.val (W.exactEnumeration d j).val := by
  unfold layerCoordinates
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← W.layerMap_coordinateFactors T d g]
  change (W.exactParameters T d
    ((HeightLayer.layerEquivOfPos _ _ (W.commutator T)
      (C.ordered_factors_injective T) (d + 1) (Nat.zero_lt_succ d)).symm
        ((HeightLayer.layerEquivOfPos _ _ (W.commutator T)
          (C.ordered_factors_injective T) (d + 1) (Nat.zero_lt_succ d)) (W.coordinateFactors T d g.val)))).toAdd j = _
  rw [MulEquiv.symm_apply_apply]
  have hj : W.weight (W.exactEnumeration d j).val = d + 1 := (W.exactEnumeration d j).property
  change ((C.rootEquiv T (W.exactEnumeration d j).val).symm
    ⟨(W.coordinateFactors T d g.val (W.exactEnumeration d j).val : T ⟶ U.X), _⟩).toAdd = _
  simp only [coordinateFactors, dite_eq_left hj]
  change ((C.rootEquiv T _).symm
    ((C.rootEquiv T _) (Multiplicative.ofAdd (C.coordinates T g.val _)))).toAdd = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData
