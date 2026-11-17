import Langlands.GroupScheme.RelativeUnipotent.RootHeightLayer
import Langlands.GroupTheory.HeightPositiveLayer

/-! # Positive filtration terms for nonnegative root weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.RelativeUnipotent

open LocalSplitCell Langlands.GroupTheory

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))}

/-- A second, possibly zero, weight family on a regular root-height chart,
together with its standard commutator sum bound. -/
structure RootWeightData (C : RootHeightChart U) where
  weight : Fin C.dimension → ℕ
  commutator : ∀ (T : Over (Spec (CommRingCat.of R))) (k l : Fin C.dimension),
    ⁅rootFactor C.roots ULift.up T k, rootFactor C.roots ULift.up T l⁆ ≤
      HeightFiltration.level (rootFactor C.roots ULift.up T) weight (weight k + weight l)

namespace RootWeightData

variable {C : RootHeightChart U} (W : RootWeightData C)

/-- Term `d` is the strictly positive cutoff `d+1`. -/
abbrev subgroup (d : ℕ) : SubgroupFunctor U :=
  heightSubgroup C.roots ULift.up W.weight (d + 1)

/-- The positive terms are exactly the supported coordinates in the original
chart, including when some of the ambient weights are zero. -/
theorem mem_subgroup_iff (T : Over (Spec (CommRingCat.of R))) (d : ℕ)
    (x : T ⟶ U.X) :
    x ∈ (W.subgroup d).carrier T ↔
      ∀ k, W.weight k < d + 1 → C.coordinates T x k = 0 := by
  constructor
  · intro hx
    obtain ⟨c, hc, hlow, hprod⟩ := HeightFiltration.exists_coords_of_pos
      (rootFactor C.roots ULift.up T) W.weight (W.commutator T) (Nat.zero_lt_succ d) hx
    choose a ha using hc
    let b : Fin C.dimension → Γ(T.left, ⊤) :=
      fun k => if W.weight k < d + 1 then 0 else (a k).toAdd
    have hb : orderedProduct C.roots ULift.up T b = x := by
      have hcoord (k : Fin C.dimension) :
          rootPoint (C.roots (ULift.up k)) T (b k) = c k := by
        dsimp only [b]
        split_ifs with hk
        · rw [rootPoint_zero, hlow k hk]
        · exact ha k
      change (List.ofFn fun k => rootPoint (C.roots (ULift.up k)) T (b k)).prod = x
      simp_rw [hcoord]
      exact hprod
    rw [← hb, C.coordinates_orderedProduct]
    exact fun k hk => ite_eq_left hk
  · intro hx
    rw [← C.orderedProduct_coordinates T x]
    apply (HeightFiltration.level (rootFactor C.roots ULift.up T) W.weight (d + 1)).list_prod_mem
    intro a ha
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp ha
    rcases lt_or_ge (W.weight k) (d + 1) with hk | hk
    · rw [hx k hk, rootPoint_zero]
      exact one_mem _
    · exact HeightFiltration.le_level _ _ hk
        (mem_rootFactor C.roots ULift.up T k _)

/-- The ambient indices retained by term `d`, at cutoff `d+1`. -/
def support (d : ℕ) : Set (Fin C.dimension) := {k | d + 1 ≤ W.weight k}

/-- This enumeration is used for affine-space coordinates, without changing
the order of the original root product. -/
def enumeration (d : ℕ) : Fin (Nat.card (W.support d)) ≃ W.support d :=
  (Finite.equivFin (W.support d)).symm

theorem mem_subgroup_iff_supported (T : Over (Spec (CommRingCat.of R)))
    (d : ℕ) (x : T ⟶ U.X) :
    x ∈ (W.subgroup d).carrier T ↔
      ∀ k, k ∉ W.support d →
        (VectorGroup.coordinates (CommRingCat.of R) C.dimension T
          (x ≫ C.chart.inv)).toAdd k = 0 := by
  rw [mem_subgroup_iff]
  simp only [support, Set.mem_ofPred_eq, not_le, RootHeightChart.coordinates]

/-- The actual positive-weight subgroup scheme on its coordinate affine space. -/
abbrev groupScheme (d : ℕ) : GroupScheme (Spec (CommRingCat.of R)) :=
  CoordinateFiltrationTerm.groupScheme C.chart (W.support d) (W.enumeration d)
    (W.subgroup d) (fun T x => W.mem_subgroup_iff_supported T d x)

/-- The closed inclusion of term `d`, which is weight cutoff `d+1`. -/
def inclusion (d : ℕ) : W.groupScheme d ⟶ U :=
  CoordinateFiltrationTerm.inclusion C.chart (W.support d) (W.enumeration d)
    (W.subgroup d) (fun T x => W.mem_subgroup_iff_supported T d x)

theorem isRepresentedBy_inclusion (d : ℕ) :
    (W.subgroup d).IsRepresentedBy (W.inclusion d) :=
  CoordinateFiltrationTerm.isRepresentedBy_inclusion _ _ _ _ _

theorem isClosedSubgroup_inclusion (d : ℕ) : IsClosedSubgroup (W.inclusion d) :=
  CoordinateFiltrationTerm.isClosedSubgroup_inclusion _ _ _ _ _

theorem smooth_groupScheme (d : ℕ) : Smooth (W.groupScheme d).X.hom :=
  CoordinateFiltrationTerm.smooth_groupScheme _ _ _ _ _

theorem isAffineHom_groupScheme (d : ℕ) : IsAffineHom (W.groupScheme d).X.hom :=
  CoordinateFiltrationTerm.isAffineHom_groupScheme _ _ _ _ _

/-- Every positive weight level is normal in the full chart group. -/
theorem isNormal_subgroup (d : ℕ) : (W.subgroup d).IsNormal := by
  intro T g x _ hx
  have hg : g ∈ ⨆ k, rootFactor C.roots ULift.up T k := by
    have hg' : g ∈ (C.subgroup 1).carrier T := by
      rw [C.subgroup_one]
      exact Subgroup.mem_top _
    simpa only [RootHeightChart.subgroup, heightSubgroup,
      HeightFiltration.level_one _ _ C.height_pos] using hg'
  have hle : (⨆ k, rootFactor C.roots ULift.up T k) ≤
      Subgroup.normalizer (HeightFiltration.level
        (rootFactor C.roots ULift.up T) W.weight (d + 1) : Set (T ⟶ U.X)) :=
    iSup_le fun k => HeightFiltration.le_normalizer_level
      (rootFactor C.roots ULift.up T) W.weight (W.commutator T) (d + 1) k
  exact (Subgroup.le_normalizer_iff.mp hle) g hg x hx

/-- Terms above every weight are trivial on every scheme test. -/
theorem subgroup_eq_bot {d : ℕ} (hd : ∀ k, W.weight k < d + 1) :
    W.subgroup d = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  exact HeightFiltration.level_eq_bot _ _ hd

end RootWeightData

end Langlands.GroupScheme.RelativeUnipotent
