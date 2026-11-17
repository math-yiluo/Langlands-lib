import Langlands.GroupScheme.Reductive.LocalSplitHeightSubgroup
import Langlands.GroupTheory.HeightPositiveLayer

/-! # Nonnegative weights independent of the regular cell cocharacter -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj commutatorElement

namespace Langlands.GroupScheme.LocalSplitCell

open Langlands.GroupTheory

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
    {G : GroupScheme (Spec (CommRingCat.of R))}
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
    {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}
    [IsOpenImmersion (cellMap i u neg pos).left]

/-- Construct universal commutators using a regular cocharacter, then bound
their coordinates with an independent cocharacter. -/
theorem exists_posComm_eq_weight_ge_of_regular
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ p, coPairing (ch (neg p)) ν < 0)
    (hpos : ∀ p, 0 < coPairing (ch (pos p)) ν)
    (wt : I → ℤ) (k l : Fin n)
    (hk : 0 ≤ coPairing (ch (pos k)) wt)
    (hl : 0 ≤ coPairing (ch (pos l)) wt)
    (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)) :
    ∃ z : Fin n → Γ(Z.left, ⊤),
      posComm u pos Z k l x y = orderedProduct u pos Z z ∧
        ∀ p, coPairing (ch (pos p)) wt <
          coPairing (ch (pos k)) wt + coPairing (ch (pos l)) wt → z p = 0 := by
  obtain ⟨E, hE⟩ := exists_isUnivComm (i := i) (neg := neg) hu ν hneg hpos k l
  refine ⟨fun p => lineEvalSections Z x y (E p), hE.posComm_eq_sections Z x y, ?_⟩
  intro p hp
  change lineEvalSections Z x y (E p) = 0
  rw [hE.eq_zero_of_coPairing_lt_add (neg := neg) hu wt hk hl p hp, map_zero]

variable (u pos) (w : Fin n → ℕ)
    (hu : TorusEquivariant i ch u) (ν : I → ℤ)
    (hneg : ∀ p, coPairing (ch (neg p)) ν < 0)
    (hpos : ∀ p, 0 < coPairing (ch (pos p)) ν)
    (wt : I → ℤ) (hw : ∀ p, coPairing (ch (pos p)) wt = (w p : ℤ))

include hu hneg hpos hw

/-- The standard commutator satisfies the sum bound for nonnegative weights
measured by a cocharacter independent of the regular one. -/
theorem commutator_rootFactor_le_of_regular
    (Z : Over (Spec (CommRingCat.of R))) (k l : Fin n) :
    ⁅rootFactor u pos Z k, rootFactor u pos Z l⁆ ≤
      HeightFiltration.level (rootFactor u pos Z) w (w k + w l) := by
  apply Subgroup.commutator_le.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨c, hc, hlow⟩ := exists_posComm_eq_weight_ge_of_regular
    (neg := neg) hu ν hneg hpos wt l k
      (by rw [hw l]; exact_mod_cast Nat.zero_le (w l))
      (by rw [hw k]; exact_mod_cast Nat.zero_le (w k)) Z (-y.toAdd) (-x.toAdd)
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

/-- Positive weight subgroups are exactly the ordered products supported above
the cutoff, with zero-weight factors retained in the ambient chart. -/
theorem mem_heightSubgroup_iff_of_regular
    (Z : Over (Spec (CommRingCat.of R))) (d : ℕ) (hd : 0 < d) (g : Z ⟶ G.X) :
    g ∈ (heightSubgroup u pos w d).carrier Z ↔
      ∃ c : Fin n → Γ(Z.left, ⊤),
        (∀ p, w p < d → c p = 0) ∧ orderedProduct u pos Z c = g := by
  classical
  constructor
  · intro hg
    obtain ⟨c, hc, hlow, hprod⟩ := HeightFiltration.exists_coords_of_pos
      (rootFactor u pos Z) w
      (commutator_rootFactor_le_of_regular u pos w hu ν hneg hpos wt hw Z) hd hg
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

/-- The supported section vectors parametrize the actual positive-height
point subgroup bijectively. This is an equivalence of types, not a claim that
the full ordered chart respects the group law. -/
def positiveHeightCoordinatesEquiv
    (Z : Over (Spec (CommRingCat.of R))) (d : ℕ) (hd : 0 < d) :
    {c : Fin n → Γ(Z.left, ⊤) // ∀ p, w p < d → c p = 0} ≃
      ↥((heightSubgroup u pos w d).carrier Z) :=
  Equiv.ofBijective
    (fun c => ⟨orderedProduct u pos Z c.val,
      (mem_heightSubgroup_iff_of_regular u pos w hu ν hneg hpos wt hw Z d hd _).2
        ⟨c.val, c.property, rfl⟩⟩)
    ⟨by
      intro a b h
      apply Subtype.ext
      exact orderedProduct_pos_injective (i := i) (neg := neg) Z
        (congrArg Subtype.val h),
      by
      intro g
      obtain ⟨c, hlow, hprod⟩ :=
        (mem_heightSubgroup_iff_of_regular u pos w hu ν hneg hpos wt hw Z d hd g.val).1
          g.property
      exact ⟨⟨c, hlow⟩, Subtype.ext hprod⟩⟩

end Langlands.GroupScheme.LocalSplitCell
