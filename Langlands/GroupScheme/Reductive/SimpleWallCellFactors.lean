import Langlands.GroupScheme.Reductive.CorootSimpleWall
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationProof
import Langlands.GroupScheme.Dynamic.ParabolicProduct

/-! # Dynamic limits of ordered root products on a simple wall -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}

/-- The part of an ordered root product whose exponents have zero weight
along the supplied cocharacter. -/
def rootProductZeroPart (ν : I → ℤ) {r : ℕ} (e : Fin r → J)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    Z ⟶ G.X :=
  (List.ofFn fun k => if coPairing (ch (e k)) ν = 0 then rootPoint (u (e k)) Z (c k)
    else 1).prod

/-- A zero-weight root point centralizes the actual coordinate cocharacter. -/
theorem IsRootParametrization.rootPoint_mem_dynamicCentralizer
    {m : I → ℤ} {v : Ga R ⟶ G} (hv : IsRootParametrization i m v)
    (ν : I → ℤ) (hν : coPairing m ν = 0)
    (Z : Over (Spec (CommRingCat.of R))) (c : Γ(Z.left, ⊤)) :
    rootPoint v Z c ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier Z := by
  apply LocalRootGroup.subgroup_le_centralizer i ν m hν
  rw [← hv.represents.2]
  exact SubgroupFunctor.mem_range.mpr
    ⟨VectorGroup.scalarPoint (CommRingCat.of R) Z c, rfl⟩

/-- The zero-weight part centralizes the cocharacter on every test scheme. -/
theorem rootProductZeroPart_mem_centralizer
    (hu : ∀ α, IsRootParametrization i (ch α) (u α)) (ν : I → ℤ)
    {r : ℕ} (e : Fin r → J) (Z : Over (Spec (CommRingCat.of R)))
    (c : Fin r → Γ(Z.left, ⊤)) :
    rootProductZeroPart (ch := ch) (u := u) ν e Z c ∈
      (Dynamic.centralizer (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier Z := by
  unfold rootProductZeroPart
  induction r with
  | zero =>
    rw [List.ofFn_zero, List.prod_nil]
    exact one_mem _
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons]
    apply mul_mem
    · split_ifs with h
      · exact (hu (e 0)).rootPoint_mem_dynamicCentralizer ν h Z (c 0)
      · exact one_mem _
    · exact ih (fun k => e k.succ) (fun k => c k.succ)

/-- If all factors have nonnegative weights, the dynamic limit of their
ordered product is its zero-weight part. -/
theorem orderedProduct_hasLimit_zeroPart
    (hu : ∀ α, IsRootParametrization i (ch α) (u α)) (ν : I → ℤ)
    {r : ℕ} (e : Fin r → J) (hnonneg : ∀ k, 0 ≤ coPairing (ch (e k)) ν)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    Dynamic.HasLimit (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)
      (orderedProduct u e Z c) (rootProductZeroPart (ch := ch) (u := u) ν e Z c) := by
  unfold orderedProduct rootProductZeroPart
  induction r with
  | zero =>
    rw [List.ofFn_zero, List.prod_nil, List.ofFn_zero, List.prod_nil]
    exact Dynamic.hasLimit_of_mem_centralizer _ (one_mem _)
  | succ r ih =>
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    apply Dynamic.HasLimit.mul
    · split_ifs with h
      · exact Dynamic.hasLimit_of_mem_centralizer _
          ((hu (e 0)).rootPoint_mem_dynamicCentralizer ν h Z (c 0))
      · exact (hu (e 0)).rootPoint_mem_dynamicUnipotent ν
          (lt_of_le_of_ne (hnonneg 0) (Ne.symm h)) Z (c 0)
    · exact ih (fun k => e k.succ) (fun k => hnonneg k.succ) (fun k => c k.succ)

/-- Removing the zero-weight limit on the left leaves an actual contracted
point. No uniqueness of limits or reducedness assumption is required. -/
theorem zeroPart_inv_mul_orderedProduct_mem_unipotent
    (hu : ∀ α, IsRootParametrization i (ch α) (u α)) (ν : I → ℤ)
    {r : ℕ} (e : Fin r → J) (hnonneg : ∀ k, 0 ≤ coPairing (ch (e k)) ν)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    (rootProductZeroPart (ch := ch) (u := u) ν e Z c)⁻¹ * orderedProduct u e Z c ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier Z := by
  rw [Dynamic.mem_unipotent]
  have hzero := Dynamic.hasLimit_of_mem_centralizer _
    (rootProductZeroPart_mem_centralizer hu ν e Z c)
  have hprod := orderedProduct_hasLimit_zeroPart hu ν e hnonneg Z c
  exact (by simpa only [inv_mul_cancel] using hzero.inv.mul _ hprod)

/-- Removing the zero-weight limit on the right also leaves a contracted point. -/
theorem orderedProduct_mul_zeroPart_inv_mem_unipotent
    (hu : ∀ α, IsRootParametrization i (ch α) (u α)) (ν : I → ℤ)
    {r : ℕ} (e : Fin r → J) (hnonneg : ∀ k, 0 ≤ coPairing (ch (e k)) ν)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    orderedProduct u e Z c * (rootProductZeroPart (ch := ch) (u := u) ν e Z c)⁻¹ ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter (Spec (CommRingCat.of R)) I ν) ≫ i)).carrier Z := by
  rw [Dynamic.mem_unipotent]
  have hzero := Dynamic.hasLimit_of_mem_centralizer _
    (rootProductZeroPart_mem_centralizer hu ν e Z c)
  have hprod := orderedProduct_hasLimit_zeroPart hu ν e hnonneg Z c
  exact (by simpa only [mul_inv_cancel] using hprod.mul _ hzero.inv)

/-- With exactly one zero-weight factor, the limit is that root point. -/
theorem rootProductZeroPart_eq_single (ν : I → ℤ) {r : ℕ}
    (e : Fin r → J) (k₀ : Fin r)
    (hzero : coPairing (ch (e k₀)) ν = 0)
    (hne : ∀ k, k ≠ k₀ → coPairing (ch (e k)) ν ≠ 0)
    (Z : Over (Spec (CommRingCat.of R))) (c : Fin r → Γ(Z.left, ⊤)) :
    rootProductZeroPart (ch := ch) (u := u) ν e Z c =
      rootPoint (u (e k₀)) Z (c k₀) := by
  rw [rootProductZeroPart, LocalWeylNormalization.list_prod_ofFn_eq _ k₀
    (fun k hk => ite_eq_right (hne k hk)), ite_eq_left hzero]

end Langlands.GroupScheme.LocalSplitCell
