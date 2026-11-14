import Langlands.Geometry.Building.GenericPointSharpExchange
import Langlands.Geometry.Building.ChamberPositiveCollection
import Langlands.Geometry.Building.ChamberOrderedInjective

/-! # Ordered positive root factors of apartment-point stabilizers, without apartment axioms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}

/-- Without apartment axioms, every positive actual root is an indivisible positive
root or its double. The bound on the multiple comes from the ray property given by
coroots of opposite factor pairs. -/
theorem exists_indivisiblePositiveRoot_eq_or_double_of_factorization [Smooth G.X.hom]
    (hS : IsSplitTorus S.toGrp) (hrank : RelativeRoot.HasRankOneFactorization i)
    (ν : cocharacterLattice S) {b : characterLattice S}
    (hb : b ∈ positiveRelativeRoots i ν) :
    ∃ a ∈ RelativeRoot.indivisiblePositiveRoots i ν, b = a ∨ b = 2 • a := by
  obtain ⟨a, ha, m, _, hm, hma⟩ :=
    RelativeRoot.exists_indivisiblePositiveRoot_ray i ν hb.1 hb.2
  have hev : ∀ (m : ℕ) (v : V S), eval S (m • a) v = (m : ℝ) * eval S a v := by
    intro m v
    induction m with
    | zero => simp only [zero_nsmul, eval_zero_char, Nat.cast_zero, zero_mul]
    | succ m ih =>
      rw [succ_nsmul, eval_add_char, ih]
      push_cast
      ring
  have heval : eval S b = (m : ℝ) • eval S a := by
    apply LinearMap.ext
    intro v
    rw [← hma, hev, LinearMap.smul_apply, smul_eq_mul]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rcases hasRayProperty_of_rankOne hS hrank ha.1.1 hb.1 hmR heval with h | h | h
  · exact ⟨a, ha, Or.inl h⟩
  · exact ⟨a, ha, Or.inr h⟩
  · exfalso
    have hp := congrArg (fun χ => latticePairing S χ ν) h
    have hq := congrArg (fun χ => latticePairing S χ ν) hma
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hp hq
    have hpos := ha.2
    push_cast at hp hq
    nlinarith

variable (D : KPApartmentData i ω)

/-- Collection for an injective enumeration of the indivisible positive roots, at
either zero depth, using only the rank-one factorization in place of AS 2. -/
theorem range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup_of_factorization
    [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp)
    (hrank : RelativeRoot.HasRankOneFactorization i)
    (x : D.Apartment) (strict : Bool) (ν : cocharacterLattice S)
    {n : ℕ} (a : Fin n → characterLattice S)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν) :
    Set.range (RelativeRoot.CentralExtension.orderedProduct
      (fun j => (D.chamberRootGroup x strict (a j)).subtype)) =
      ((⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x strict b :
        Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
  classical
  let c : Fin (n * 2) → characterLattice S := fun l =>
    if (finProdFinEquiv.symm l).2 = 0 then a (finProdFinEquiv.symm l).1
      else 2 • a (finProdFinEquiv.symm l).1
  let H : Fin (n * 2) → Subgroup (rationalPoints G) := fun l =>
    if c l ∈ relativeRoots i then D.chamberRootGroup x strict (c l) else ⊥
  have ha (j : Fin n) : a j ∈ RelativeRoot.indivisiblePositiveRoots i ν :=
    hrange ▸ Set.mem_range_self j
  have hc0 (j : Fin n) : c (finProdFinEquiv (j, 0)) = a j := by
    simp only [c, Equiv.symm_apply_apply, ↓reduceIte]
  have hc1 (j : Fin n) : c (finProdFinEquiv (j, 1)) = 2 • a j := by
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [c, Equiv.symm_apply_apply, ite_eq_right h10]
  have hpos (l : Fin (n * 2)) (hl : c l ∈ relativeRoots i) :
      c l ∈ positiveRelativeRoots i ν := by
    refine ⟨hl, ?_⟩
    dsimp only [c]
    split_ifs
    · exact (ha _).2
    · have hp := (ha (finProdFinEquiv.symm l).1).2
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      omega
  have hcover (b : positiveRelativeRoots i ν) : ∃ l, c l = b := by
    obtain ⟨d, hd, hb⟩ := exists_indivisiblePositiveRoot_eq_or_double_of_factorization hS hrank ν b.2
    obtain ⟨j, hj⟩ := (show d ∈ Set.range a by rw [hrange]; exact hd)
    rcases hb with hb | hb
    · exact ⟨finProdFinEquiv (j, 0), (hc0 j).trans (hj.trans hb.symm)⟩
    · exact ⟨finProdFinEquiv (j, 1),
        (hc1 j).trans ((congrArg (2 • ·) hj).trans hb.symm)⟩
  have hcollect :
      Set.range (RelativeRoot.CentralExtension.orderedProduct (fun l => (H l).subtype)) =
        ((⨆ l, H l : Subgroup (rationalPoints G)) : Set (rationalPoints G)) := by
    apply Langlands.GroupTheory.HeightCollection.range_orderedProduct_eq_iSup
      (w := fun l => (latticePairing S (c l) ν).toNat)
    intro j k
    by_cases hj : c j ∈ relativeRoots i
    · by_cases hk : c k ∈ relativeRoots i
      · have hjH : H j = D.chamberRootGroup x strict (c j) := ite_eq_left hj
        have hkH : H k = D.chamberRootGroup x strict (c k) := ite_eq_left hk
        rw [hjH, hkH]
        refine (D.chamberRootGroup_commutator_height x strict ν (hpos j hj)
          (hpos k hk)).trans ?_
        refine iSup_le fun b => iSup_le fun hb => ?_
        obtain ⟨l, hl⟩ := hcover b
        have hroot : c l ∈ relativeRoots i := hl.symm ▸ b.2.1
        exact le_iSup_of_le l (le_iSup_of_le (hl.symm ▸ hb)
          (by dsimp only [H]; rw [ite_eq_left hroot, hl]))
      · simp only [H, ite_eq_right hk, Subgroup.commutator_bot_right, bot_le]
    · simp only [H, ite_eq_right hj, Subgroup.commutator_bot_left, bot_le]
  have h0 (j : Fin n) :
      H (finProdFinEquiv (j, 0)) = D.chamberRootGroup x strict (a j) := by
    simp only [H, hc0, ite_eq_left (ha j).1.1]
  have h1 (j : Fin n) :
      H (finProdFinEquiv (j, 1)) ≤ D.chamberRootGroup x strict (a j) := by
    simp only [H, hc1]
    split_ifs with h2a
    · cases strict with
      | false => exact D.filtration_double_le x (ha j).1.1 h2a
      | true => exact D.filtrationPlus_double_le x (ha j).1.1 h2a
    · exact bot_le
  rw [← range_orderedProduct_pairs H _ h0 h1, hcollect]
  apply congrArg (fun K : Subgroup (rationalPoints G) => (K : Set (rationalPoints G)))
  apply le_antisymm
  · refine iSup_le fun l => ?_
    dsimp only [H]
    split_ifs with hl
    · exact le_iSup (fun b : positiveRelativeRoots i ν =>
        D.chamberRootGroup x strict b) ⟨c l, hpos l hl⟩
    · exact bot_le
  · refine iSup_le fun b => ?_
    obtain ⟨l, hl⟩ := hcover b
    have hroot : c l ∈ relativeRoots i := hl.symm ▸ b.2.1
    exact le_iSup_of_le l (by dsimp only [H]; rw [ite_eq_left hroot, hl])

/-- **Ordered positive factors of a point stabilizer.** Let `ν` be generic and let
`a` enumerate the indivisible positive roots injectively. If the ordered product of
actual root points `u j ∈ U_{a j}(k)` fixes the image of `x` in the reduced building,
then every factor lies in the depth-zero filtration at `x`. No apartment axiom is
assumed. -/
theorem mem_filtration_of_orderedProduct_smul_apartmentMap_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (x : D.Apartment) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {n : ℕ} (a : Fin n → characterLattice S) (ha : Function.Injective a)
    (hrange : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν)
    (u : Fin n → rationalPoints G) (hu : ∀ j, u j ∈ rootGroupPoints i (a j))
    (hfix : (List.ofFn u).prod • D.apartmentMap x = D.apartmentMap x) (j : Fin n) :
    u j ∈ D.filtration x (a j) 0 := by
  have : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hrank := rootRankOneFactorization k G hG S i hi
  have hapos (r : Fin n) : 0 < latticePairing S (a r) ν :=
    (show a r ∈ RelativeRoot.indivisiblePositiveRoots i ν from
      hrange ▸ Set.mem_range_self r).2
  have hgU : (List.ofFn u).prod ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
    exact RelativeRoot.subgroup_le_dynamicUnipotent i ν (hapos r) _ (hu r)
  have hmem := D.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq
    hG hi x ν hν hgU hfix
  rw [← SetLike.mem_coe, ← D.range_orderedIndivisiblePositiveRootGroupProduct_eq_iSup_of_factorization
    hS hrank x false ν a hrange] at hmem
  obtain ⟨v, hv⟩ := hmem
  have hinj := RelativeRoot.orderedRootSubgroupPoints_injective_of_statement
    RelativeRoot.dynamicRootOrderedProduct hG hi ν a ha hrange (Over.mk (𝟙 _))
  let u' : ∀ r, (RelativeRoot.subgroup i (a r)).carrier (Over.mk (𝟙 _)) :=
    fun r => ⟨u r, hu r⟩
  let v' : ∀ r, (RelativeRoot.subgroup i (a r)).carrier (Over.mk (𝟙 _)) :=
    fun r => ⟨v r, D.filtration_le_rootGroupPoints x (a r) 0 (v r).2⟩
  have heq : u' = v' := by
    apply hinj
    change (List.ofFn u).prod = (List.ofFn fun r => (v r : rationalPoints G)).prod
    rw [← hv]
    rfl
  have hj := congrArg (fun w => (w j : rationalPoints G)) heq
  change u j = (v j : rationalPoints G) at hj
  rw [hj]
  exact (v j).2

end KPApartmentData

end Langlands.Geometry.Building
