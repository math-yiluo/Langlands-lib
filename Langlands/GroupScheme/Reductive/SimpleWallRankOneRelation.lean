import Langlands.GroupScheme.Reductive.SimpleWallCellDecomposition

/-! # The actual rank-one relation extracted from a negative-simple translation -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I]
  {J : Type u} [Finite J] {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)} [P.IsReduced]
  {u : J → (Ga R ⟶ G)} {m n : ℕ}

/-- The two selected opposite root coordinates and original torus coordinate
of a full cell point, as an actual point of the ambient group. -/
def cellRankOnePart (a : J) (kneg : Fin m) (kpos : Fin n)
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) : Z ⟶ G.X :=
  rootPoint (u (P.reflectionPerm a a)) Z (negCoord x kneg) *
    (torusCoord x ≫ i.hom.hom) * rootPoint (u a) Z (posCoord x kpos)

variable (b : P.Base)
  (hpair : ∀ x y : I → ℤ, P.toLinearMap x y = coPairing x y)
  {a : J} (ha : a ∈ b.support)
  (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
  (kneg : Fin m) (kpos : Fin n)
  (hkneg : (neg kneg : J) = P.reflectionPerm a a) (hkpos : (pos kpos : J) = a)

include hkpos in
omit [Fintype I] [Finite J] [P.IsReduced] in
private theorem wall_pos_ne (k : Fin n) (hk : k ≠ kpos) : (pos k : J) ≠ a := by
  intro he
  apply hk
  apply pos.injective
  exact Subtype.ext (he.trans hkpos.symm)

include hkneg in
omit [Fintype I] [Finite J] [P.IsReduced] in
private theorem wall_neg_ne (k : Fin m) (hk : k ≠ kneg) :
    (neg k : J) ≠ P.reflectionPerm a a := by
  intro he
  apply hk
  apply neg.injective
  exact Subtype.ext (he.trans hkneg.symm)

include hkneg hkpos in
/-- On the simple wall, the zero-weight middle factor is exactly the
selected opposite-root, torus, root product. -/
theorem cellLeviPart_simpleWall_eq
    {Z : Over (Spec (CommRingCat.of R))} (x : Z ⟶ cellObj R I m n) :
    cellLeviPart (i := i) (ch := fun β => P.root β) (u := u)
        (simpleWallCocharacter P b hpair ha)
        (fun k => (neg k : J)) (fun k => (pos k : J)) x =
      cellRankOnePart (i := i) (P := P) (u := u) a kneg kpos x := by
  have hzeroN : coPairing (P.root (neg kneg : J))
      (simpleWallCocharacter P b hpair ha) = 0 :=
    (simpleWallCocharacter_zero_iff P b hpair ha _).mpr (Or.inr hkneg)
  have hzeroP : coPairing (P.root (pos kpos : J))
      (simpleWallCocharacter P b hpair ha) = 0 :=
    (simpleWallCocharacter_zero_iff P b hpair ha _).mpr (Or.inl hkpos)
  have hneN : ∀ k, k ≠ kneg → coPairing (P.root (neg k : J))
      (simpleWallCocharacter P b hpair ha) ≠ 0 := by
    intro k hk
    exact ne_of_lt (simpleWallCocharacter_neg P b hpair ha (neg k).2
      (wall_neg_ne b neg kneg hkneg k hk))
  have hneP : ∀ k, k ≠ kpos → coPairing (P.root (pos k : J))
      (simpleWallCocharacter P b hpair ha) ≠ 0 := by
    intro k hk
    exact ne_of_gt (simpleWallCocharacter_pos P b hpair ha (pos k).2
      (wall_pos_ne b pos kpos hkpos k hk))
  unfold cellLeviPart cellRankOnePart
  rw [rootProductZeroPart_eq_single _ _ kneg hzeroN hneN,
    rootProductZeroPart_eq_single _ _ kpos hzeroP hneP, hkneg, hkpos]

include hpair ha hkneg hkpos in
/-- A negative-simple translation relation between full cell points implies
the corresponding actual rank-one relation, with the same torus coordinates. -/
theorem cellRankOnePart_mul_negativeSimple_of_cell_relation [IsAffine G.X.left]
    (hu : ∀ β, IsRootParametrization i (P.root β) (u β))
    {Z : Over (Spec (CommRingCat.of R))} (x y : Z ⟶ cellObj R I m n)
    (c : Γ(Z.left, ⊤))
    (hxy : (x ≫ cellMap i u (fun k => (neg k : J)) (fun k => (pos k : J))) *
      rootPoint (u (P.reflectionPerm a a)) Z c =
        y ≫ cellMap i u (fun k => (neg k : J)) (fun k => (pos k : J))) :
    cellRankOnePart (i := i) (P := P) (u := u) a kneg kpos x *
        rootPoint (u (P.reflectionPerm a a)) Z c =
      cellRankOnePart (i := i) (P := P) (u := u) a kneg kpos y := by
  let ν := simpleWallCocharacter P b hpair ha
  have hzeroN : coPairing (P.root (P.reflectionPerm a a)) ν = 0 :=
    (simpleWallCocharacter_zero_iff P b hpair ha _).mpr (Or.inr rfl)
  have hneg : ∀ k, coPairing (P.root (neg k : J)) ν ≤ 0 := by
    intro k
    by_cases he : (neg k : J) = P.reflectionPerm a a
    · rw [he, hzeroN]
    · exact (simpleWallCocharacter_neg P b hpair ha (neg k).2 he).le
  have hpos : ∀ k, 0 ≤ coPairing (P.root (pos k : J)) ν := by
    intro k
    by_cases he : (pos k : J) = a
    · rw [(simpleWallCocharacter_zero_iff P b hpair ha _).mpr (Or.inl he)]
    · exact (simpleWallCocharacter_pos P b hpair ha (pos k).2 he).le
  have hr := (hu (P.reflectionPerm a a)).rootPoint_mem_dynamicCentralizer ν hzeroN Z c
  have h := cellLeviPart_mul_of_cell_relation hu ν
    (fun k => (neg k : J)) (fun k => (pos k : J)) hneg hpos x y
    (rootPoint (u (P.reflectionPerm a a)) Z c) hr hxy
  rw [cellLeviPart_simpleWall_eq b hpair ha neg pos kneg kpos hkneg hkpos x,
    cellLeviPart_simpleWall_eq b hpair ha neg pos kneg kpos hkneg hkpos y] at h
  exact h

end Langlands.GroupScheme.LocalSplitCell
