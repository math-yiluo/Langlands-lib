import Langlands.GroupScheme.RelativeLevi.SplitUnipotentWeightCommutator
import Langlands.GroupScheme.RelativeLevi.SplitBorelDynamicProjection
import Langlands.GroupScheme.Reductive.LocalSplitFlatBigCell
import Langlands.LinearAlgebra.RootDatumFaceHeight

/-! # Actual split charts adapted to a supplied cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open LocalSplitCell

variable {I J : Type u} [Fintype I] [Finite J]

/-- The ordinary coordinate character/cocharacter pairing, as an integral
functional on the full character lattice. -/
def coPairingLinear (wt : I → ℤ) : Module.Dual ℤ (I → ℤ) where
  toFun x := coPairing x wt
  map_add' x y := by simp [coPairing, add_mul, Finset.sum_add_distrib]
  map_smul' a x := by simp [coPairing, mul_assoc, Finset.mul_sum]

/-- Every coordinate cocharacter admits a positive system on which all its
root pairings are nonnegative, including roots with zero pairing. -/
theorem exists_base_nonnegative_coPairing
    (P : RootDatum J (I → ℤ) (I → ℤ)) [P.IsReduced] (wt : I → ℤ) :
    ∃ b : P.Base, ∀ a, b.IsPos a → 0 ≤ coPairing (P.root a) wt := by
  classical
  let := Fintype.ofFinite J
  let q := coPairingLinear wt
  let cv := P.flip.toPerfPair.symm q
  have he (a : J) : P.root' a cv = coPairing (P.root a) wt := by
    change (P.flip.toPerfPair cv) (P.root a) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  let C := Langlands.LinearAlgebra.RootDatumCoweightFace.coweightFace P cv
  refine ⟨C.base, ?_⟩
  intro a ha
  apply ha.induction_on_add
  · intro a ha
    rw [← he a]
    exact Langlands.LinearAlgebra.RootDatumFaceHeight.face_dominant C a ha
  · intro a b c hc ha hb
    change 0 ≤ coPairingLinear wt (P.root c)
    rw [hc, map_add]
    exact add_nonneg ha (by
      change 0 ≤ coPairing (P.root b) wt
      rw [← he b]
      exact Langlands.LinearAlgebra.RootDatumFaceHeight.face_dominant C b hb)

variable {R : Type u} [CommRing R]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (P : RootDatum J (I → ℤ) (I → ℤ))
  (fam : J → (Ga R ⟶ G)) (wt : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- Actual regular-cell coordinates with independent parabolic weights and
explicit ambient root labels and composites. -/
structure SplitParabolicWeightChart where
  cocharacter : I → ℤ
  regular : ∀ a : J, coPairing (P.root a) cocharacter ≠ 0
  base : P.Base
  chart : RelativeUnipotent.RootHeightChart
    (AffineRegularBorel.contractingGroup i cocharacter)
  index : Fin chart.dimension ≃ {a // base.IsPos a}
  root_comp : ∀ k, chart.roots (ULift.up k) ≫
    Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i cocharacter) =
      fam (index k)
  weights : RelativeUnipotent.RootWeightData chart
  weight_eq : ∀ k, (weights.weight k : ℤ) = coPairing (P.root (index k)) wt

variable {i P fam wt}

set_option maxHeartbeats 800000 in
/-- Reductivity and actual root parametrizations produce a chart adapted to
every supplied coordinate cocharacter, allowing arbitrary Levi zero weights. -/
theorem nonempty_splitParabolicWeightChart
    (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus
      (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) i)
    (hP : IsFibrewiseRootDatumOf I G i P)
    (hfam : ∀ a, IsRootParametrization i (P.root a) (fam a)) :
    Nonempty (SplitParabolicWeightChart i P fam wt) := by
  classical
  let : P.IsReduced := hP.isReduced
  obtain ⟨b, hb⟩ := exists_base_nonnegative_coPairing P wt
  obtain ⟨ν, hνpos, hνneg⟩ := exists_cocharacter_of_base P b
  let neg := (Finite.equivFin {a // ¬ b.IsPos a}).symm
  let pos := (Finite.equivFin {a // b.IsPos a}).symm
  let n := Nat.card {a // b.IsPos a}
  let hTE : TorusEquivariant i (fun a => P.root a) fam :=
    fun a Z t c => (hfam a).equivariant Z t c
  let := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b fam hfam neg pos
  have hpos (k : Fin n) : 0 < coPairing (P.root (pos k)) ν :=
    hνpos _ (pos k).property
  have hneg (k : Fin (Nat.card {a // ¬ b.IsPos a})) :
      coPairing (P.root (neg k)) ν < 0 :=
    hνneg _ (neg k).property
  have hwt (k : Fin n) : 0 ≤ coPairing (P.root (pos k)) wt :=
    hb _ (pos k).property
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffineHom (AffineRegularBorel.contractingGroup i ν).X.hom :=
    AffineRegularBorel.isAffineHom_contractingGroup i ν
  let : IsAffine (AffineRegularBorel.contractingGroup i ν).X.left :=
    isAffine_of_isAffineHom (AffineRegularBorel.contractingGroup i ν).X.hom
  let j := Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter i ν)
  let hU := Dynamic.Affine.isRepresentedBy_unipotentHom
    (AffineRegularBorel.cocharacter i ν)
  refine ⟨{
    cocharacter := ν
    regular := ?_
    base := b
    chart := positiveCellRootHeightChart j hTE ν hU hpos hneg
    index := pos
    root_comp := ?_
    weights := positiveCellRootWeightData j hTE ν hU hpos hneg wt hwt
    weight_eq := ?_
  }⟩
  · intro a
    by_cases ha : b.IsPos a
    · exact ne_of_gt (hνpos a ha)
    · exact ne_of_lt (hνneg a ha)
  · intro k
    exact rootToUnipotent_comp j hTE ν hU (pos k) (hpos k)
  · intro k
    exact Int.toNat_of_nonneg (hwt k)

end Langlands.GroupScheme
