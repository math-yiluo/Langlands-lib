import Langlands.GroupScheme.Reductive.LocalSplitHeightCommutator
import Langlands.GroupTheory.HeightFiltration

/-! # Root-height subgroups on every scheme test -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.LocalSplitCell

open Langlands.GroupTheory

variable {R : Type u} [CommRing R]
    {G : GroupScheme (Spec (CommRingCat.of R))}

/-- A root map evaluated on global functions, as a group homomorphism. -/
def rootPointHom (a : Ga R ⟶ G) (Z : Over (Spec (CommRingCat.of R))) :
    Multiplicative Γ(Z.left, ⊤) →* (Z ⟶ G.X) where
  toFun c := rootPoint a Z c.toAdd
  map_one' := rootPoint_zero a Z
  map_mul' c c' := rootPoint_add a Z c.toAdd c'.toAdd

variable {J : Type u} (u : J → (Ga R ⟶ G)) {n : ℕ} (pos : Fin n → J)

/-- The actual point subgroup of one parametrized root. -/
def rootFactor (Z : Over (Spec (CommRingCat.of R))) (k : Fin n) :
    Subgroup (Z ⟶ G.X) :=
  (rootPointHom (u (pos k)) Z).range

theorem mem_rootFactor (Z : Over (Spec (CommRingCat.of R))) (k : Fin n)
    (c : Γ(Z.left, ⊤)) : rootPoint (u (pos k)) Z c ∈ rootFactor u pos Z k :=
  ⟨Multiplicative.ofAdd c, rfl⟩

theorem comp_mem_rootFactor {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z)
    {k : Fin n} {x : Z ⟶ G.X} (hx : x ∈ rootFactor u pos Z k) :
    f ≫ x ∈ rootFactor u pos W k := by
  obtain ⟨c, rfl⟩ := hx
  exact ⟨Multiplicative.ofAdd (f.left.appTop c.toAdd), comp_rootPoint _ f _ |>.symm⟩

variable (w : Fin n → ℕ)

/-- The generated root-height subgroup functor on all scheme tests. -/
def heightSubgroup (d : ℕ) : SubgroupFunctor G where
  carrier Z := HeightFiltration.level (rootFactor u pos Z) w d
  comp_mem {T T'} f x hx := by
    refine Subgroup.iSup_induction
      (HeightFiltration.factor (rootFactor u pos T) w d)
      (C := fun x => f ≫ x ∈ HeightFiltration.level (rootFactor u pos T') w d) hx
      (fun k x hx => ?_) ?_ (fun a b ha hb => ?_)
    · rcases lt_or_ge (w k) d with hk | hk
      · rw [HeightFiltration.factor_of_lt _ _ hk] at hx
        rw [Subgroup.mem_bot.mp hx, MonObj.comp_one]
        exact one_mem _
      · rw [HeightFiltration.factor_of_le _ _ hk] at hx
        exact HeightFiltration.le_level _ _ hk (comp_mem_rootFactor u pos f hx)
    · rw [MonObj.comp_one]
      exact one_mem _
    · rw [MonObj.comp_mul]
      exact mul_mem ha hb

theorem antitone_heightSubgroup : Antitone (heightSubgroup u pos w) := by
  intro d e hde Z
  exact HeightFiltration.antitone_level _ _ hde

section Bound

variable {I : Type u} [Fintype I]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {ch : J → I → ℤ} {m : ℕ} {neg : Fin m → J}
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ p, coPairing (ch (neg p)) ν < 0)
    (hpos : ∀ p, 0 < coPairing (ch (pos p)) ν)
    (hw : ∀ p, coPairing (ch (pos p)) ν = (w p : ℤ))

include hu hneg hpos hw

/-- The standard group commutator, with the convention
`a * b * a⁻¹ * b⁻¹`, satisfies the root-height sum bound. -/
theorem commutator_rootFactor_le
    (Z : Over (Spec (CommRingCat.of R))) (k l : Fin n) :
    ⁅rootFactor u pos Z k, rootFactor u pos Z l⁆ ≤
      HeightFiltration.level (rootFactor u pos Z) w (w k + w l) := by
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨c, hc, hlow⟩ := exists_posComm_eq_weight_ge
    (neg := neg) hu ν hneg hpos l k Z (-y.toAdd) (-x.toAdd)
  have hstandard :
      ⁅rootPoint (u (pos k)) Z x.toAdd, rootPoint (u (pos l)) Z y.toAdd⁆ =
        orderedProduct u pos Z c := by
    rw [← hc, posComm, rootPoint_neg, rootPoint_neg, commutatorElement_def]
    group
  change ⁅rootPoint (u (pos k)) Z x.toAdd, rootPoint (u (pos l)) Z y.toAdd⁆ ∈ _
  rw [hstandard]
  apply (HeightFiltration.level (rootFactor u pos Z) w (w k + w l)).list_prod_mem
  intro a ha
  obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ha
  by_cases hp : w k + w l ≤ w p
  · exact HeightFiltration.le_level _ _ hp (mem_rootFactor u pos Z p (c p))
  · have hc0 : c p = 0 := hlow p (by rw [hw p, hw l, hw k]; omega)
    rw [hc0, rootPoint_zero]
    exact one_mem _

/-- Every generated height point has ordered root coordinates supported at
that height and above. -/
theorem mem_heightSubgroup_iff
    (Z : Over (Spec (CommRingCat.of R))) (d : ℕ) (g : Z ⟶ G.X) :
    g ∈ (heightSubgroup u pos w d).carrier Z ↔
      ∃ c : Fin n → Γ(Z.left, ⊤),
        (∀ p, w p < d → c p = 0) ∧ orderedProduct u pos Z c = g := by
  classical
  have hwpos (p : Fin n) : 0 < w p := by
    have := hpos p
    rw [hw p] at this
    omega
  constructor
  · intro hg
    obtain ⟨c, hc, hlow, hprod⟩ := HeightFiltration.exists_coords
      (rootFactor u pos Z) w hwpos
      (commutator_rootFactor_le u pos w hu ν hneg hpos hw Z) d hg
    choose x hx using hc
    refine ⟨fun p => if w p < d then 0 else (x p).toAdd,
      fun p hp => ite_eq_left hp, ?_⟩
    have hcoord (p : Fin n) :
        rootPoint (u (pos p)) Z (if w p < d then 0 else (x p).toAdd) = c p := by
      split_ifs with hp
      · rw [rootPoint_zero, hlow p hp]
      · exact hx p
    change (List.ofFn fun p =>
      rootPoint (u (pos p)) Z (if w p < d then 0 else (x p).toAdd)).prod = g
    simp_rw [hcoord]
    exact hprod
  · rintro ⟨c, hlow, rfl⟩
    apply (HeightFiltration.level (rootFactor u pos Z) w d).list_prod_mem
    intro a ha
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp ha
    rcases lt_or_ge (w p) d with hp | hp
    · rw [hlow p hp, rootPoint_zero]
      exact one_mem _
    · exact HeightFiltration.le_level _ _ hp (mem_rootFactor u pos Z p (c p))

/-- Supported ordered root coordinates are unique. -/
theorem existsUnique_coords_of_mem_heightSubgroup
    (Z : Over (Spec (CommRingCat.of R))) (d : ℕ) (g : Z ⟶ G.X)
    (hg : g ∈ (heightSubgroup u pos w d).carrier Z) :
    ∃! c : Fin n → Γ(Z.left, ⊤),
      (∀ p, w p < d → c p = 0) ∧ orderedProduct u pos Z c = g := by
  obtain ⟨c, hlow, hprod⟩ :=
    (mem_heightSubgroup_iff u pos w hu ν hneg hpos hw Z d g).mp hg
  exact ⟨c, ⟨hlow, hprod⟩, fun c' hc' =>
    orderedProduct_pos_injective (i := i) (neg := neg) Z (hc'.2.trans hprod.symm)⟩

/-- Each next root-height subgroup is normal in the current one. -/
theorem normal_next_heightSubgroup
    (Z : Over (Spec (CommRingCat.of R))) (d : ℕ) :
    (((heightSubgroup u pos w (d + 1)).carrier Z).subgroupOf
      ((heightSubgroup u pos w d).carrier Z)).Normal :=
  HeightFiltration.normal_next (rootFactor u pos Z) w
    (commutator_rootFactor_le u pos w hu ν hneg hpos hw Z) d

/-- Each root-height subgroup is normal in the group generated by all positive factors. -/
theorem normal_heightSubgroup
    (Z : Over (Spec (CommRingCat.of R))) (d : ℕ) :
    (((heightSubgroup u pos w d).carrier Z).subgroupOf
      (⨆ p, rootFactor u pos Z p)).Normal :=
  HeightFiltration.normal_level_subgroupOf (rootFactor u pos Z) w
    (commutator_rootFactor_le u pos w hu ν hneg hpos hw Z) d

end Bound

end Langlands.GroupScheme.LocalSplitCell
