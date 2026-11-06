import Langlands.AbelianScheme.Tate.FullEvaluationKernel
import Langlands.AbelianScheme.Tate.RationalMonodromy

/-! # The finite torsion subgroup determined by a commensurable lattice -/

noncomputable section

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- A subgroup containing n times the full Tate group is saturated for evaluation at n. -/
theorem full_evaluation_mem_map_iff
    (n : Index (fun _ => True)) (M : AddSubgroup (Full G T))
    (hM : ∀ x : Full G T, n.val • x ∈ M) (x : Full G T) :
    evaluation G T (fun _ => True) n x ∈ M.map (evaluation G T (fun _ => True) n) ↔
      x ∈ M := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hz : evaluation G T (fun _ => True) n (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := full_exists_nsmul_of_evaluation_eq_zero G T n (x - y) hz
    rw [(sub_eq_iff_eq_add).mp hz.symm]
    exact M.add_mem (hM z) hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The full integral preimage of n times an additive subgroup of the rational module. -/
def normalizedIntegralSubgroup (n : ℕ) (L : AddSubgroup (RationalFull G T)) :
    AddSubgroup (Full G T) where
  carrier := {x | ∃ w ∈ L, toRational G T (fun _ => True) x = n • w}
  zero_mem' := ⟨0, L.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨w, hw, hx⟩ ⟨z, hz, hy⟩
    exact ⟨w + z, L.add_mem hw hz, by rw [map_add, hx, hy, smul_add]⟩
  neg_mem' := by
    rintro x ⟨w, hw, hx⟩
    exact ⟨-w, L.neg_mem hw, by rw [map_neg, hx, smul_neg]⟩

@[simp]
theorem mem_normalizedIntegralSubgroup
    (n : ℕ) (L : AddSubgroup (RationalFull G T)) (x : Full G T) :
    x ∈ normalizedIntegralSubgroup G T n L ↔
      ∃ w ∈ L, toRational G T (fun _ => True) x = n • w := Iff.rfl

/-- The square of a positive full index, with its positivity retained. -/
def fullSquareIndex (n : Index (fun _ => True)) : Index (fun _ => True) :=
  ⟨n.val * n.val, Nat.mul_pos n.property.1 n.property.1, trivial⟩

/-- The torsion-level image of the normalized integral subgroup at level n². -/
def normalizedLevelSubgroup (n : Index (fun _ => True))
    (L : AddSubgroup (RationalFull G T)) :
    AddSubgroup (Level G T (n.val * n.val)) :=
  (normalizedIntegralSubgroup G T n.val L).map
    (evaluation G T (fun _ => True) (fullSquareIndex n))

theorem square_nsmul_mem_normalizedIntegralSubgroup
    (n : ℕ) (L : AddSubgroup (RationalFull G T))
    (hlower : ∀ x : Full G T, n • toRational G T (fun _ => True) x ∈ L)
    (x : Full G T) :
    (n * n) • x ∈ normalizedIntegralSubgroup G T n L := by
  refine ⟨n • toRational G T (fun _ => True) x, hlower x, ?_⟩
  rw [map_nsmul, smul_smul]

/-- The finite-level subgroup has exactly the prescribed full integral preimage. -/
theorem evaluation_mem_normalizedLevelSubgroup_iff
    (n : Index (fun _ => True)) (L : AddSubgroup (RationalFull G T))
    (hlower : ∀ x : Full G T, n.val • toRational G T (fun _ => True) x ∈ L)
    (x : Full G T) :
    evaluation G T (fun _ => True) (fullSquareIndex n) x ∈
        normalizedLevelSubgroup G T n L ↔
      x ∈ normalizedIntegralSubgroup G T n.val L :=
  full_evaluation_mem_map_iff G T (fullSquareIndex n) _
    (square_nsmul_mem_normalizedIntegralSubgroup G T n.val L hlower) x

/-- The upper commensurability bound makes every normalized rational element integral. -/
theorem exists_normalizedIntegralSubgroup_of_upper_bound
    (n : ℕ) (L : AddSubgroup (RationalFull G T))
    (hupper : ∀ w ∈ L, ∃ x : Full G T, toRational G T (fun _ => True) x = n • w)
    (w : RationalFull G T) (hw : w ∈ L) :
    ∃ x ∈ normalizedIntegralSubgroup G T n L,
      toRational G T (fun _ => True) x = n • w := by
  obtain ⟨x, hx⟩ := hupper w hw
  exact ⟨x, ⟨w, hw, hx⟩, hx⟩

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

open Langlands.AlgebraicGeometry.FiniteEtale
open GroupScheme.Tate

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ S) (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{u}) (A : AbelianScheme S)
  (hu : ∀ n : Index (fun _ => True), IsUnit (n.val : Γ(S, ⊤)))

/-- Rational monodromy invariance passes to the normalized full integral subgroup. -/
theorem normalizedIntegralSubgroup_monodromy
    (n : ℕ) (L : AddSubgroup (RationalFull A (Over.mk s)))
    (hL : ∀ (g : FundamentalGroup s hs) (w : RationalFull A (Over.mk s)),
      rationalMonodromy s hs htor A (fun _ => True) hu g w ∈ L ↔ w ∈ L)
    (g : FundamentalGroup s hs) (x : Full A (Over.mk s)) :
    integralMonodromy s hs htor A (fun _ => True) hu g x ∈
        normalizedIntegralSubgroup A.toGrp (Over.mk s) n L ↔
      x ∈ normalizedIntegralSubgroup A.toGrp (Over.mk s) n L := by
  have hf (g : FundamentalGroup s hs) (x : Full A (Over.mk s))
      (hx : x ∈ normalizedIntegralSubgroup A.toGrp (Over.mk s) n L) :
      integralMonodromy s hs htor A (fun _ => True) hu g x ∈
        normalizedIntegralSubgroup A.toGrp (Over.mk s) n L := by
    obtain ⟨w, hw, hx⟩ := hx
    refine ⟨rationalMonodromy s hs htor A (fun _ => True) hu g w,
      (hL g w).mpr hw, ?_⟩
    rw [toRational_monodromy, hx, map_nsmul]
  constructor
  · intro hx
    have hx' := hf g⁻¹ _ hx
    change (integralMonodromy s hs htor A (fun _ => True) hu g).symm
      (integralMonodromy s hs htor A (fun _ => True) hu g x) ∈ _ at hx'
    simpa only [AddEquiv.symm_apply_apply] using hx'
  · exact hf g x

/-- Its finite torsion-level image is invariant under the actual level monodromy. -/
theorem normalizedLevelSubgroup_monodromy
    (n : Index (fun _ => True)) (L : AddSubgroup (RationalFull A (Over.mk s)))
    (hL : ∀ (g : FundamentalGroup s hs) (w : RationalFull A (Over.mk s)),
      rationalMonodromy s hs htor A (fun _ => True) hu g w ∈ L ↔ w ∈ L)
    (g : FundamentalGroup s hs) (y : Level A (Over.mk s) (n.val * n.val)) :
    levelMonodromy s hs htor A (n.val * n.val)
        (Nat.mul_pos n.property.1 n.property.1) (hu (fullSquareIndex n)) g y ∈
        normalizedLevelSubgroup A.toGrp (Over.mk s) n L ↔
      y ∈ normalizedLevelSubgroup A.toGrp (Over.mk s) n L := by
  have hf (g : FundamentalGroup s hs) (y : Level A (Over.mk s) (n.val * n.val))
      (hy : y ∈ normalizedLevelSubgroup A.toGrp (Over.mk s) n L) :
      levelMonodromy s hs htor A (n.val * n.val)
          (Nat.mul_pos n.property.1 n.property.1) (hu (fullSquareIndex n)) g y ∈
        normalizedLevelSubgroup A.toGrp (Over.mk s) n L := by
    obtain ⟨x, hx, rfl⟩ := hy
    refine ⟨integralMonodromy s hs htor A (fun _ => True) hu g x,
      (normalizedIntegralSubgroup_monodromy s hs htor A hu n.val L hL g x).mpr hx, ?_⟩
    exact evaluation_integralMonodromyHom s hs htor A (fun _ => True) hu g
      (fullSquareIndex n) x
  constructor
  · intro hy
    have hy' := hf g⁻¹ _ hy
    change (levelMonodromy s hs htor A (n.val * n.val)
      (Nat.mul_pos n.property.1 n.property.1) (hu (fullSquareIndex n)) g).symm
      (levelMonodromy s hs htor A (n.val * n.val)
        (Nat.mul_pos n.property.1 n.property.1) (hu (fullSquareIndex n)) g y) ∈ _ at hy'
    simpa only [AddEquiv.symm_apply_apply] using hy'
  · exact hf g y

end Langlands.AbelianScheme.Tate
