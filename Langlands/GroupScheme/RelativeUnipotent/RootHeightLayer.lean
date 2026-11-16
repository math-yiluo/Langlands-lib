import Langlands.GroupScheme.RelativeUnipotent.RootHeightFiltration
import Langlands.GroupTheory.HeightLayer
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof

/-! # Exact-height additive coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj commutatorElement

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeUnipotent.RootHeightChart

open LocalSplitCell Langlands.GroupTheory
open Langlands.GroupScheme.RelativeRoot.CentralExtension

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} (C : RootHeightChart U)

@[simp]
theorem coordinates_rootPoint (T : Over (Spec (CommRingCat.of R)))
    (k : Fin C.dimension) (c : Γ(T.left, ⊤)) :
    C.coordinates T (rootPoint (C.roots (ULift.up k)) T c) = Pi.single k c := by
  rw [← LocalWeylNormalization.orderedProduct_single C.roots ULift.up T k c,
    coordinates_orderedProduct]

/-- Each root parameter is an isomorphism onto its actual point subgroup. -/
def rootEquiv (T : Over (Spec (CommRingCat.of R))) (k : Fin C.dimension) :
    Multiplicative Γ(T.left, ⊤) ≃* rootFactor C.roots ULift.up T k :=
  MulEquiv.ofBijective (rootPointHom (C.roots (ULift.up k)) T).rangeRestrict
    ⟨by
      intro x y h
      have hxy := congrArg (fun z : rootFactor C.roots ULift.up T k => C.coordinates T (z : T ⟶ U.X) k) h
      change C.coordinates T (rootPoint (C.roots (ULift.up k)) T x.toAdd) k =
        C.coordinates T (rootPoint (C.roots (ULift.up k)) T y.toAdd) k at hxy
      rw [coordinates_rootPoint, coordinates_rootPoint, Pi.single_eq_same,
        Pi.single_eq_same] at hxy
      exact Multiplicative.toAdd.injective hxy,
      MonoidHom.rangeRestrict_surjective _⟩

theorem ordered_factors_injective (T : Over (Spec (CommRingCat.of R))) :
    Function.Injective (orderedProduct
      (fun k => (rootFactor C.roots ULift.up T k).subtype)) := by
  intro a b h
  let x : Fin C.dimension → Γ(T.left, ⊤) := fun k => ((C.rootEquiv T k).symm (a k)).toAdd
  let y : Fin C.dimension → Γ(T.left, ⊤) := fun k => ((C.rootEquiv T k).symm (b k)).toAdd
  have hx (k : Fin C.dimension) :
      rootPoint (C.roots (ULift.up k)) T (x k) = (a k : T ⟶ U.X) :=
    congrArg Subtype.val ((C.rootEquiv T k).apply_symm_apply (a k))
  have hy (k : Fin C.dimension) :
      rootPoint (C.roots (ULift.up k)) T (y k) = (b k : T ⟶ U.X) :=
    congrArg Subtype.val ((C.rootEquiv T k).apply_symm_apply (b k))
  have hxy : LocalSplitCell.orderedProduct C.roots ULift.up T x =
      LocalSplitCell.orderedProduct C.roots ULift.up T y := by
    change (List.ofFn fun k => rootPoint (C.roots (ULift.up k)) T (x k)).prod =
      (List.ofFn fun k => rootPoint (C.roots (ULift.up k)) T (y k)).prod
    simp_rw [hx, hy]
    exact h
  have heq : x = y := by
    simpa only [coordinates_orderedProduct] using congrArg (C.coordinates T) hxy
  funext k
  apply (C.rootEquiv T k).symm.injective
  apply Multiplicative.toAdd.injective
  exact congrFun heq k

/-- The exact-height indices, including an empty layer. -/
def exactSupport (d : ℕ) : Set (Fin C.dimension) := {k | C.height k = d}

def exactEnumeration (d : ℕ) : Fin (Nat.card (C.exactSupport d)) ≃ C.exactSupport d :=
  (Finite.equivFin (C.exactSupport d)).symm

/-- The parameter homomorphism on an exact-height factor. -/
def exactParameter (T : Over (Spec (CommRingCat.of R))) (d : ℕ)
    (k : Fin C.dimension) :
    HeightLayer.exactFactor (rootFactor C.roots ULift.up T) C.height d k →*
      Multiplicative Γ(T.left, ⊤) :=
  (C.rootEquiv T k).symm.toMonoidHom.comp
    (Subgroup.inclusion (HeightLayer.exactFactor_le _ _ d k))

/-- Extract the additive parameters of the exact-height factor product. -/
def exactParameters (T : Over (Spec (CommRingCat.of R))) (d : ℕ) :
    (∀ k, HeightLayer.exactFactor (rootFactor C.roots ULift.up T) C.height d k) →*
      Multiplicative (Fin (Nat.card (C.exactSupport d)) → Γ(T.left, ⊤)) where
  toFun a := Multiplicative.ofAdd fun j =>
    (C.exactParameter T d (C.exactEnumeration d j).val
      (a (C.exactEnumeration d j).val)).toAdd
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext j
    exact congrArg Multiplicative.toAdd (map_one (C.exactParameter T d _))
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    funext j
    exact congrArg Multiplicative.toAdd (map_mul (C.exactParameter T d _) (a _) (b _))

/-- The exact-height coordinate map is a homomorphism, obtained from the actual
successive group quotient and its factor-product isomorphism. -/
def layerCoordinates (T : Over (Spec (CommRingCat.of R))) (d : ℕ) (hd : 0 < d) :
    HeightFiltration.level (rootFactor C.roots ULift.up T) C.height d →*
      Multiplicative (Fin (Nat.card (C.exactSupport d)) → Γ(T.left, ⊤)) :=
  (C.exactParameters T d).comp
    (((HeightLayer.layerEquiv (rootFactor C.roots ULift.up T) C.height
      (C.commutator T) C.height_pos (C.ordered_factors_injective T) d hd).symm.toMonoidHom).comp
        (HeightLayer.projection _ _ (C.commutator T) d))

/-- The exact-height root factors of the coordinates of an ambient point. -/
def coordinateFactors (T : Over (Spec (CommRingCat.of R))) (d : ℕ) (x : T ⟶ U.X) :
    ∀ k, HeightLayer.exactFactor (rootFactor C.roots ULift.up T) C.height d k :=
  fun k => if hk : C.height k = d then
    ⟨rootPoint (C.roots (ULift.up k)) T (C.coordinates T x k),
      (HeightLayer.exactFactor_of_eq (rootFactor C.roots ULift.up T) C.height hk).symm ▸
        mem_rootFactor C.roots ULift.up T k _⟩ else 1

/-- A height-subgroup point and its exact-height factors have the same class
in the successive quotient. -/
theorem layerMap_coordinateFactors (T : Over (Spec (CommRingCat.of R)))
    (d : ℕ) (hd : 0 < d)
    (g : HeightFiltration.level (rootFactor C.roots ULift.up T) C.height d) :
    HeightLayer.layerMap _ _ (C.commutator T) d hd
      (C.coordinateFactors T d g.val) =
        HeightLayer.projection _ _ (C.commutator T) d g := by
  let H := rootFactor C.roots ULift.up T
  let c := C.coordinates T (g : T ⟶ U.X)
  have hlow : ∀ k, C.height k < d → c k = 0 :=
    (C.mem_subgroup_iff T d g.val).mp g.property
  have hcLevel (k : Fin C.dimension) :
      rootPoint (C.roots (ULift.up k)) T (c k) ∈ HeightFiltration.level H C.height d := by
    rcases lt_or_ge (C.height k) d with hk | hk
    · rw [hlow k hk, rootPoint_zero]
      exact one_mem _
    · exact HeightFiltration.le_level _ _ hk (mem_rootFactor C.roots ULift.up T k _)
  let b : Fin C.dimension → HeightFiltration.level H C.height d :=
    fun k => ⟨rootPoint (C.roots (ULift.up k)) T (c k), hcLevel k⟩
  have hprod : (List.ofFn b).prod = g := by
    apply Subtype.ext
    change (HeightFiltration.level H C.height d).subtype ((List.ofFn b).prod) = _
    rw [map_list_prod, List.map_ofFn]
    exact C.orderedProduct_coordinates T g.val
  have hcoord (k : Fin C.dimension) :
      HeightLayer.coordinateMap H C.height (C.commutator T) d k
        (C.coordinateFactors T d g.val k) =
      HeightLayer.projection H C.height (C.commutator T) d (b k) := by
    by_cases hk : C.height k = d
    · simp only [coordinateFactors, dite_eq_left hk]
      rfl
    · simp only [coordinateFactors, dite_eq_right hk, map_one]
      symm
      apply (HeightLayer.projection_eq_one_iff H C.height (C.commutator T) d _).mpr
      change rootPoint (C.roots (ULift.up k)) T (c k) ∈
        HeightFiltration.level H C.height (d + 1)
      rcases lt_or_gt_of_ne hk with hk' | hk'
      · rw [hlow k hk', rootPoint_zero]
        exact one_mem _
      · exact HeightFiltration.le_level _ _ (by omega)
          (mem_rootFactor C.roots ULift.up T k _)
  change (List.ofFn fun k => HeightLayer.coordinateMap H C.height (C.commutator T) d k
    (C.coordinateFactors T d g.val k)).prod = _
  simp_rw [hcoord]
  rw [← hprod, map_list_prod, List.map_ofFn]
  rfl

/-- The quotient-defined homomorphism reads exactly the coordinates of the
specified height in the original ordered scheme chart. -/
theorem layerCoordinates_apply (T : Over (Spec (CommRingCat.of R)))
    (d : ℕ) (hd : 0 < d)
    (g : HeightFiltration.level (rootFactor C.roots ULift.up T) C.height d)
    (j : Fin (Nat.card (C.exactSupport d))) :
    (C.layerCoordinates T d hd g).toAdd j =
      C.coordinates T g.val (C.exactEnumeration d j).val := by
  unfold layerCoordinates
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply,
    ← C.layerMap_coordinateFactors T d hd g]
  change (C.exactParameters T d
    ((HeightLayer.layerEquiv _ _ (C.commutator T) C.height_pos
      (C.ordered_factors_injective T) d hd).symm
        ((HeightLayer.layerEquiv _ _ (C.commutator T) C.height_pos
          (C.ordered_factors_injective T) d hd) (C.coordinateFactors T d g.val)))).toAdd j = _
  rw [MulEquiv.symm_apply_apply]
  have hj : C.height (C.exactEnumeration d j).val = d := (C.exactEnumeration d j).property
  change ((C.rootEquiv T (C.exactEnumeration d j).val).symm
    ⟨(C.coordinateFactors T d g.val (C.exactEnumeration d j).val : T ⟶ U.X), _⟩).toAdd = _
  simp only [coordinateFactors, dite_eq_left hj]
  change ((C.rootEquiv T _).symm
    ((C.rootEquiv T _) (Multiplicative.ofAdd (C.coordinates T g.val _)))).toAdd = _
  rw [MulEquiv.symm_apply_apply]
  rfl

end Langlands.GroupScheme.RelativeUnipotent.RootHeightChart
