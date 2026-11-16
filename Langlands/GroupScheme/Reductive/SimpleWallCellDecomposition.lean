import Langlands.GroupScheme.Reductive.SimpleWallCellFactors
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.IntegralModel.OrderedCellLemmas

/-! # Extracting the centralizer factor of a big-cell relation -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Dynamic

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- Equality of opposite-unipotent, centralizer and unipotent products
determines the centralizer factor on every test scheme. -/
theorem centralizer_factor_eq_of_triple_eq
    {Z : Over (Spec R)} {m m' z z' v v' : Z ⟶ G.X}
    (hm : m ∈ (unipotent (oppositeCocharacter χ)).carrier Z)
    (hm' : m' ∈ (unipotent (oppositeCocharacter χ)).carrier Z)
    (hz : z ∈ (centralizer χ).carrier Z) (hz' : z' ∈ (centralizer χ).carrier Z)
    (hv : v ∈ (unipotent χ).carrier Z) (hv' : v' ∈ (unipotent χ).carrier Z)
    (heq : m * (z * v) = m' * (z' * v')) : z = z' := by
  have hr : m'⁻¹ * m = (z' * v') * (z * v)⁻¹ := by
    calc
      m'⁻¹ * m = m'⁻¹ * (m * (z * v)) * (z * v)⁻¹ := by
        group
      _ = m'⁻¹ * (m' * (z' * v')) * (z * v)⁻¹ := by rw [heq]
      _ = (z' * v') * (z * v)⁻¹ := by rw [inv_mul_cancel_left]
  have hrU : m'⁻¹ * m ∈ (unipotent (oppositeCocharacter χ)).carrier Z :=
    mul_mem (inv_mem hm') hm
  have hrP : m'⁻¹ * m ∈ (parabolic χ).carrier Z := by
    rw [hr]
    exact mul_mem
      (mul_mem (centralizer_le_parabolic χ Z hz') (unipotent_le_parabolic χ Z hv'))
      (inv_mem (mul_mem (centralizer_le_parabolic χ Z hz) (unipotent_le_parabolic χ Z hv)))
  have hone := eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ hrU hrP
  have hmm : m = m' := (inv_mul_eq_one.mp hone).symm
  have hp : z * v = z' * v' := by
    rw [hmm] at heq
    exact mul_left_cancel heq
  have hlim := hasLimit_centralizer_mul_unipotent χ hz hv
  have hlim' := hasLimit_centralizer_mul_unipotent χ hz' hv'
  rw [← hp] at hlim'
  exact hlim.unique χ hlim'

/-- Right multiplication by a centralizer point multiplies only the
centralizer factor of a triple decomposition. -/
theorem centralizer_factor_mul_of_triple_relation
    {Z : Over (Spec R)} {m m' z z' v v' r : Z ⟶ G.X}
    (hm : m ∈ (unipotent (oppositeCocharacter χ)).carrier Z)
    (hm' : m' ∈ (unipotent (oppositeCocharacter χ)).carrier Z)
    (hz : z ∈ (centralizer χ).carrier Z) (hz' : z' ∈ (centralizer χ).carrier Z)
    (hv : v ∈ (unipotent χ).carrier Z) (hv' : v' ∈ (unipotent χ).carrier Z)
    (hr : r ∈ (centralizer χ).carrier Z)
    (heq : (m * (z * v)) * r = m' * (z' * v')) : z * r = z' := by
  have hconj : r⁻¹ * v * r ∈ (unipotent χ).carrier Z := by
    simpa only [inv_inv] using
      conj_mem_unipotent χ (centralizer_le_parabolic χ Z (inv_mem hr)) hv
  apply centralizer_factor_eq_of_triple_eq χ hm hm' (mul_mem hz hr) hz'
    hconj hv'
  calc
    m * ((z * r) * (r⁻¹ * v * r)) = (m * (z * v)) * r := by
      simp only [mul_assoc, mul_inv_cancel_left]
    _ = _ := heq

end Langlands.GroupScheme.Dynamic

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}

/-- Negating a coordinate direction inverts the cocharacter parameter. -/
theorem coordinateDirection_neg (ν : I → ℤ) :
    CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (-ν)) ≫ i =
      Dynamic.oppositeCocharacter (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i) := by
  have h : splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I (-ν) =
      -splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν := by
    simp only [splitTorus.exponentCocharacter, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
  rw [h, groupHom_neg_comp_eq_oppositeCocharacter_overBase]

/-- The zero-weight root part is unchanged by negating the direction. -/
theorem rootProductZeroPart_neg (ν : I → ℤ) {r : ℕ} (e : Fin r → J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    rootProductZeroPart (ch := ch) (u := u) (-ν) e Z c =
      rootProductZeroPart (ch := ch) (u := u) ν e Z c := by
  have h (k : Fin r) : coPairing (ch (e k)) (-ν) = -coPairing (ch (e k)) ν := by
    simp only [coPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  simp only [rootProductZeroPart, h, neg_eq_zero]

/-- The centralizer part of a cell point, obtained by keeping its
zero-weight roots on either side of the original torus coordinate. -/
def cellLeviPart (ν : I → ℤ) {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) : Z ⟶ G.X :=
  rootProductZeroPart (ch := ch) (u := u) ν neg Z (negCoord x) *
    (torusCoord x ≫ i.hom.hom) *
    rootProductZeroPart (ch := ch) (u := u) ν pos Z (posCoord x)

/-- The opposite contracted factor of the same cell point. -/
def cellWallNegativePart (ν : I → ℤ) {m n : ℕ} (neg : Fin m → J)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) : Z ⟶ G.X :=
  orderedProduct u neg Z (negCoord x) *
    (rootProductZeroPart (ch := ch) (u := u) ν neg Z (negCoord x))⁻¹

/-- The contracted factor of the same cell point. -/
def cellWallPositivePart (ν : I → ℤ) {m n : ℕ} (pos : Fin n → J)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) : Z ⟶ G.X :=
  (rootProductZeroPart (ch := ch) (u := u) ν pos Z (posCoord x))⁻¹ *
    orderedProduct u pos Z (posCoord x)

/-- These three factors recover the original cell point exactly. -/
theorem cellMap_eq_wallParts (ν : I → ℤ) {m n : ℕ}
    (neg : Fin m → J) (pos : Fin n → J)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    x ≫ cellMap i u neg pos =
      cellWallNegativePart (ch := ch) (u := u) ν neg x *
        (cellLeviPart (i := i) (ch := ch) (u := u) ν neg pos x *
          cellWallPositivePart (ch := ch) (u := u) ν pos x) := by
  rw [comp_cellMap]
  simp only [cellPoint, cellWallNegativePart, cellLeviPart, cellWallPositivePart,
    mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]

/-- The middle part centralizes the chosen coordinate direction. -/
theorem cellLeviPart_mem_centralizer
    (hu : ∀ α, IsRootParametrization i (ch α) (u α)) (ν : I → ℤ)
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    cellLeviPart (i := i) (ch := ch) (u := u) ν neg pos x ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier Z := by
  apply mul_mem
  · apply mul_mem
    · exact rootProductZeroPart_mem_centralizer hu ν neg Z (negCoord x)
    · apply range_le_centralizer_groupHom_comp i
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) Z
      exact SubgroupFunctor.mem_range.mpr ⟨torusCoord x, rfl⟩
  · exact rootProductZeroPart_mem_centralizer hu ν pos Z (posCoord x)

/-- Nonpositive weights put the first factor in the opposite contracted subgroup. -/
theorem cellWallNegativePart_mem_unipotent
    (hu : ∀ α, IsRootParametrization i (ch α) (u α)) (ν : I → ℤ)
    {m n : ℕ} (neg : Fin m → J) (hneg : ∀ k, coPairing (ch (neg k)) ν ≤ 0)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    cellWallNegativePart (ch := ch) (u := u) ν neg x ∈
      (Dynamic.unipotent (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i))).carrier Z := by
  have hnonneg : ∀ k, 0 ≤ coPairing (ch (neg k)) (-ν) := by
    intro k
    simp only [coPairing, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    exact neg_nonneg.mpr (hneg k)
  have h := orderedProduct_mul_zeroPart_inv_mem_unipotent hu (-ν) neg hnonneg Z (negCoord x)
  rw [rootProductZeroPart_neg, coordinateDirection_neg] at h
  exact h

/-- Nonnegative weights put the last factor in the contracted subgroup. -/
theorem cellWallPositivePart_mem_unipotent
    (hu : ∀ α, IsRootParametrization i (ch α) (u α)) (ν : I → ℤ)
    {m n : ℕ} (pos : Fin n → J) (hpos : ∀ k, 0 ≤ coPairing (ch (pos k)) ν)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    cellWallPositivePart (ch := ch) (u := u) ν pos x ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier Z :=
  zeroPart_inv_mul_orderedProduct_mem_unipotent hu ν pos hpos Z (posCoord x)

/-- A cell relation under right translation by a centralizer point induces
the exact relation between its zero-weight middle factors, on every test. -/
theorem cellLeviPart_mul_of_cell_relation [IsAffine G.X.left]
    (hu : ∀ α, IsRootParametrization i (ch α) (u α)) (ν : I → ℤ)
    {m n : ℕ} (neg : Fin m → J) (pos : Fin n → J)
    (hneg : ∀ k, coPairing (ch (neg k)) ν ≤ 0)
    (hpos : ∀ k, 0 ≤ coPairing (ch (pos k)) ν)
    {Z : Over (Spec (CommRingCat.of R))} (x y : Z ⟶ cellObj R I m n)
    (r : Z ⟶ G.X)
    (hr : r ∈ (Dynamic.centralizer (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier Z)
    (hxy : (x ≫ cellMap i u neg pos) * r = y ≫ cellMap i u neg pos) :
    cellLeviPart (i := i) (ch := ch) (u := u) ν neg pos x * r =
      cellLeviPart (i := i) (ch := ch) (u := u) ν neg pos y := by
  apply Dynamic.centralizer_factor_mul_of_triple_relation _
    (cellWallNegativePart_mem_unipotent hu ν neg hneg x)
    (cellWallNegativePart_mem_unipotent hu ν neg hneg y)
    (cellLeviPart_mem_centralizer hu ν neg pos x)
    (cellLeviPart_mem_centralizer hu ν neg pos y)
    (cellWallPositivePart_mem_unipotent hu ν pos hpos x)
    (cellWallPositivePart_mem_unipotent hu ν pos hpos y) hr
  rw [← cellMap_eq_wallParts ν neg pos x, ← cellMap_eq_wallParts ν neg pos y]
  exact hxy

end Langlands.GroupScheme.LocalSplitCell
