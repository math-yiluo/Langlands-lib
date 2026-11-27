import Langlands.AlgebraicGeometry.Deformation.TransitionObstruction
import Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeqCup

/-! # The obstruction of lifted transitions as an ordered Čech cocycle -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Deformation.TransitionObstruction

open SquareZeroAffinePairs ElementaryIdealCoefficients ElementaryMorphismLifts ElementaryLiftCech
open AffineOpenQuotientSections Langlands.Cohomology
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom] [Smooth Y.hom]
  {Z : Target R} {I : Ideal R} [Fact (maximalIdeal R * I = ⊥)] (b : Z.Coordinates I)
  (F : Reduction Y (maximalIdeal R))

local notation "Index" => Fin b.cotangentRank × Fin b.idealRank

omit [IsLocalRing R] in
theorem alternating_four {G : Type*} [AddCommGroup G] {a b c d : G} (h : d + b = a + c) :
    a + -b + c + -d = 0 := by
  rw [← sub_eq_zero] at h
  rw [← neg_eq_zero, ← h]
  abel

omit [IsLocalRing R] in
theorem map_eq_res {X : Scheme.{u}} {V W : X.Opens} (h : V ≤ W) (x : Γ(X, W)) :
    (X.presheaf.map (homOfLE h).op).hom x = Cech.res (P := Cech.ab X.presheaf) h x := rfl

namespace Family

variable (D : Family Y) (hD : D.Agrees I) (π : Y ⟶ Z.X)

/-- The indexed preimages of the opens of the family in the actual residue fibre. -/
abbrev cover : D.L → F.obj.left.Opens := fun l ↦ F.toOriginal ⁻¹ᵁ D.V l

omit [IsSeparated Y.hom] [Smooth Y.hom] in
theorem inter_le_three (σ : Fin 3 → D.L) :
    Cech.inter (D.cover F) σ ≤ F.toOriginal ⁻¹ᵁ (D.V (σ 0) ⊓ D.V (σ 1) ⊓ D.V (σ 2)) :=
  fun _ hx ↦ ⟨⟨Cech.inter_le_apply (U := D.cover F) σ 0 hx, Cech.inter_le_apply (U := D.cover F) σ 1 hx⟩,
    Cech.inter_le_apply (U := D.cover F) σ 2 hx⟩

omit [IsSeparated Y.hom] [Smooth Y.hom] in
theorem inter_le_four (τ : Fin 4 → D.L) :
    Cech.inter (D.cover F) τ ≤
      F.toOriginal ⁻¹ᵁ (D.V (τ 0) ⊓ D.V (τ 1) ⊓ D.V (τ 2) ⊓ D.V (τ 3)) :=
  fun _ hx ↦ ⟨⟨⟨Cech.inter_le_apply (U := D.cover F) τ 0 hx, Cech.inter_le_apply (U := D.cover F) τ 1 hx⟩,
    Cech.inter_le_apply (U := D.cover F) τ 2 hx⟩, Cech.inter_le_apply (U := D.cover F) τ 3 hx⟩

/-- The obstruction as an ordered Čech `2`-cochain of the structure sheaf of the residue fibre,
one for each difference coordinate. -/
def cech (j : Index) : Cech.C (Cech.ab F.obj.left.presheaf) (D.cover F) 2 := fun σ ↦
  Cech.res (P := Cech.ab F.obj.left.presheaf) (D.inter_le_three F σ)
    (D.obstruction b F hD π (σ 0) (σ 1) (σ 2) j)

theorem res_cech {j : Index} (σ : Fin 3 → D.L) {W : F.obj.left.Opens}
    (h : W ≤ Cech.inter (D.cover F) σ) :
    Cech.res (P := Cech.ab F.obj.left.presheaf) h (D.cech b F hD π j σ) =
      Cech.res (P := Cech.ab F.obj.left.presheaf) (h.trans (D.inter_le_three F σ))
        (D.obstruction b F hD π (σ 0) (σ 1) (σ 2) j) := by
  rw [cech, Cech.res_res]

theorem cech_d (j : Index) :
    Cech.d (Cech.ab F.obj.left.presheaf) (D.cover F) 2 (D.cech b F hD π j) = 0 := by
  funext τ
  have key := congrArg (Cech.res (P := Cech.ab F.obj.left.presheaf) (D.inter_le_four F τ))
    (D.obstruction_four b F hD π (τ 0) (τ 1) (τ 2) (τ 3) j)
  simp only [map_eq_res] at key
  simp only [map_add, Cech.res_res] at key
  rw [Cech.d_apply, Fin.sum_univ_four]
  rw [res_cech, res_cech, res_cech, res_cech]
  change (1 : ℤ) • _ + (-1 : ℤ) • _ + (1 : ℤ) • _ + (-1 : ℤ) • _ = 0
  rw [one_zsmul, one_zsmul, neg_one_zsmul, neg_one_zsmul]
  exact alternating_four key

/-- The obstruction as an ordered Čech `2`-cocycle of the structure sheaf of the residue fibre. -/
def cocycle (j : Index) :
    LinearMap.ker (dCochain F.obj.hom (D.cover F) (unitModule F.obj.left) 2) :=
  ⟨(show cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 2 from D.cech b F hD π j), by
    rw [LinearMap.mem_ker]
    have h := dCochain_unit F.obj.hom (D.cover F) 2
      (show cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 2 from D.cech b F hD π j)
    rw [D.cech_d] at h
    exact h⟩

theorem cocycle_apply (j : Index) (σ : Fin 3 → D.L) :
    ((D.cocycle b F hD π j : cochain F.obj.hom (D.cover F) (unitModule F.obj.left) 2) σ :
      Γ(F.obj.left, Cech.inter (D.cover F) σ)) =
      (F.obj.left.presheaf.map (homOfLE (D.inter_le_three F σ)).op).hom
        (D.obstruction b F hD π (σ 0) (σ 1) (σ 2) j) := rfl

end Family

end Langlands.AlgebraicGeometry.Deformation.TransitionObstruction
